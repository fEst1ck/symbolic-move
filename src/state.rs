//! # Evaluation State
use crate::value::{
  ConstrainedValue, Constraint, PrimitiveValue, Value, Type,
  struct_type_to_datatype_sort, sat, BranchCondition,
};
use itertools::Itertools;
use move_stackless_bytecode::{
  stackless_bytecode::{Bytecode, Label},
  function_target::{FunctionTarget, FunctionData},
};
use std::fmt;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::ops::{BitAnd, BitOr};
use symbolic_evaluation::traits::{State, StateSet, Transition};
use z3::{
  ast::{Ast, Bool, Array, BV},
  Context, SatResult, Solver,
  Sort, Symbol, FuncDecl,
};
use move_model::{
  model::{
    GlobalEnv, ModuleEnv, FunctionEnv, StructEnv, FieldEnv,
    ModuleId, StructId, QualifiedId, QualifiedInstId,
  }
};

pub type CodeOffset = u16;
pub type TempIndex = usize;
pub type BlockId = CodeOffset;

pub type Union<'ctx> = Vec<ConstrainedValue<'ctx>>;

#[derive(Clone, Debug)]
pub enum TerminationStatus<'ctx> {
  None,
  Return(Vec<Union<'ctx>>),
  Abort(Union<'ctx>),
  Unsat,
}

impl<'ctx> fmt::Display for TerminationStatus<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      TerminationStatus::None => write!(f, "Still running"),
      TerminationStatus::Return(return_vals) => {
        writeln!(f, "Returns with values:")?;
        for (i, val) in return_vals.iter().enumerate() {
          write!(f, "#{}: ", i)?;
          writeln!(f, "{}", val.iter().format(", "))?;
        }
        Ok(())
      }
      TerminationStatus::Abort(val) => writeln!(f, "Aborts with error code {}.", val.iter().format(", ")),
      TerminationStatus::Unsat => writeln!(f, "Unsatisfied"),
    }
  }
}

impl<'ctx> TerminationStatus<'ctx> {
  fn is_final(&self) -> bool {
    match self {
      TerminationStatus::None => false,
      _ => true,
    }
  }
}

#[derive(Clone, Debug)]
pub struct Local<'ctx> {
  content: Vec<ConstrainedValue<'ctx>>,
}

impl<'ctx, 'env> fmt::Display for Local<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.content.iter().format(", "))?;
    Ok(())
  }
}

impl<'ctx> BitAnd<Bool<'ctx>> for Local<'ctx> {
  type Output = Self;

  fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
    Local {
      content: self
        .content
        .into_iter()
        .map(|x| ((x & rhs.clone()).simplify()))
        .collect(),
    }
  }
}

impl<'ctx> BitOr<Local<'ctx>> for Local<'ctx> {
  type Output = Self;

  fn bitor(self, rhs: Local<'ctx>) -> Self {
    self.merge(rhs)
  }
}

impl<'ctx> Local<'ctx> {
  pub fn new() -> Self {
    Self {
      content: Vec::new(),
    }
  }

  pub fn from_type<S: Into<Symbol>>(x: S, t: &Type, ctx: &'ctx Context) -> Self {
    Self {
      content: vec![ConstrainedValue::new_const(x, t, ctx)],
    }
  }

  /// Turn a local of boolean sort into a constraint.
  pub fn to_branch_condition(&self, ctx: &'ctx Context) -> BranchCondition<'ctx> {
    self
      .content
      .clone()
      .into_iter()
      .map(|x| x.to_branch_condition())
      .fold(BranchCondition::or_id(ctx), |acc, x| (acc | x).simplify())
  }

  /// Set the content to empty, and return the original value.
  pub fn del(&mut self) -> Vec<ConstrainedValue<'ctx>> {
    let res = self.content.clone();
    self.content = Vec::new();
    res
  }

  /// Return the number of possible values of the local.
  pub fn len(&self) -> usize {
    self.content.len()
  }

  /// Return the merge of the locals.
  pub fn merge(mut self, mut other: Self) -> Self {
    fn merge_content<'ctx>(
      xs: Vec<ConstrainedValue<'ctx>>,
      ys: Vec<ConstrainedValue<'ctx>>,
    ) -> Vec<ConstrainedValue<'ctx>> {
      let mut res = Vec::with_capacity(xs.len());
      for (x, y) in xs.into_iter().zip(ys.into_iter()) {
        res.append(&mut x.merge(y));
      }
      res
    }
    if self.len() == other.len() {
      Self {
        content: merge_content(self.content, other.content),
      }
    } else {
      self.content.append(&mut other.content);
      self
    }
  }
}

#[derive(Clone, Debug)]
pub struct LocalState<'ctx> {
  context: &'ctx Context,
  // Instruction Counter
  ic: CodeOffset,
  pc: Constraint<'ctx>,
  ts: TerminationStatus<'ctx>,
  locals: Vec<Local<'ctx>>,
}

use std::ops::{Index, IndexMut};
impl<'ctx> Index<TempIndex> for LocalState<'ctx> {
  type Output = Local<'ctx>;

  fn index(&self, index: TempIndex) -> &Self::Output {
    self.locals.index(index)
  }
}

impl<'ctx> IndexMut<TempIndex> for LocalState<'ctx> {
  fn index_mut(&mut self, index: TempIndex) -> &mut Self::Output {
    self.locals.index_mut(index)
  }
}

impl<'ctx> BitAnd<Constraint<'ctx>> for LocalState<'ctx> {
  type Output = Self;

  fn bitand(self, rhs: Constraint<'ctx>) -> Self::Output {
    let new_pc: Constraint<'ctx> = (&self.pc & &rhs).simplify();
    if sat(&new_pc, new_pc.get_ctx()) {
      LocalState {
        pc: new_pc,
        locals: self.locals.into_iter().map(|x| x & rhs.clone()).collect(),
        ..self
      }
    } else {
      LocalState {
        pc: new_pc,
        locals: self.locals.into_iter().map(|x| x & rhs.clone()).collect(),
        ts: TerminationStatus::Unsat,
        ..self
      }
    }
  }
}

impl<'ctx, 'env> fmt::Display for LocalState<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    writeln!(f, "LocalState")?;
    writeln!(f, "Instruction Counter: {} | Path Constraint: {}", self.ic, self.pc)?;
    writeln!(f, "{}", self.ts)?;
    writeln!(f, "Locals:")?;
    for (i, local) in self.locals.iter().enumerate() {
      writeln!(f, "$t{} = {}", i, local)?;
    }
    Ok(())
  }
}

impl<'ctx> LocalState<'ctx> {
  pub fn new(
    context: &'ctx Context,
    ic: CodeOffset,
    pc: Constraint<'ctx>,
    ts: TerminationStatus<'ctx>,
    locals: Vec<Local<'ctx>>,
  ) -> Self {
    Self {
      context,
      ic,
      pc,
      ts,
      locals,
    }
  }

  pub fn new_default(
    context: &'ctx Context,
    locals: Vec<Local<'ctx>>,
  ) -> Self {
    Self {
      context,
      ic: 0,
      pc: Bool::from_bool(context, true),
      ts: TerminationStatus::None,
      locals,
    }
  }

  /// Return constrained tuples of operation arguments.
  pub fn args(&self, srcs: &[TempIndex]) -> Vec<(Vec<Value<'ctx>>, Constraint<'ctx>)> {
    // v = (x, p) vs = ((y ...), q)
    // return ((y ... x), q & p)
    fn add_operand<'ctx>(
      ctx: &'ctx Context,
      v: (Value<'ctx>, Constraint<'ctx>),
      vs: (Vec<Value<'ctx>>, Constraint<'ctx>),
    ) -> Option<(Vec<Value<'ctx>>, Constraint<'ctx>)> {
      let (x, p) = v;
      let (mut xs, q) = vs;
      let constraint = (q & p).simplify();
      if sat(&constraint, ctx) {
        xs.push(x);
        Some((xs, constraint))
      } else {
        None
      }
    }
    // v = (x, p) vs = (((y ...), q) ...)
    // return (((y ... x), q & p) ...) where q & p not unsat
    fn add_operand1<'ctx>(
      ctx: &'ctx Context,
      v: ConstrainedValue<'ctx>,
      args: Vec<(Vec<Value<'ctx>>, Constraint<'ctx>)>,
    ) -> Vec<(Vec<Value<'ctx>>, Constraint<'ctx>)> {
      args.into_iter().filter_map(|x| add_operand(ctx, v.clone().decompose(), x)).collect()
    }

    fn add_operand2<'ctx>(
      ctx: &'ctx Context,
      v: Vec<ConstrainedValue<'ctx>>,
      args: Vec<(Vec<Value<'ctx>>, Constraint<'ctx>)>,
    ) -> Vec<(Vec<Value<'ctx>>, Constraint<'ctx>)> {
      v.into_iter()
        .map(|x| add_operand1(ctx, x, args.clone()))
        .flatten()
        .collect()
    }
    srcs.iter().fold(vec![(Vec::new(), Bool::from_bool(self.get_ctx(), true))], |acc, &x| {
      add_operand2(self.get_ctx(), self.index(x).content.clone(), acc)
    })
  }

  pub fn get_ctx(&self) -> &'ctx Context {
    &self.context
  }

  /// Return the program counter.
  pub fn ic(&self) -> CodeOffset {
    self.ic
  }

  /// Two `LocalState`s are similar iff they have the same ic.
  pub fn similar(&self, other: &Self) -> bool {
    self.ic() == other.ic()
  }

  /// Return the termination status.
  pub fn termination_status(&self) -> &TerminationStatus {
    &self.ts
  }

  /// Set `var` to empty and return the original values of `var`.
  pub fn del(&mut self, var: TempIndex) -> Vec<ConstrainedValue<'ctx>> {
    self.index_mut(var).del()
  }
}

pub struct Constrained<'ctx, T> {
  pub content: T,
  pub constraint: Constraint<'ctx>,
}

impl<'ctx, T: Clone> Clone for Constrained<'ctx, T> {
  fn clone(&self) -> Self {
    Self {
      content: self.content.clone(),
      constraint: self.constraint.clone(),
    }
  }
}

/// Impose another constraint.
impl<'ctx, T> BitAnd<Bool<'ctx>> for Constrained<'ctx, T> {
  type Output = Self;

  fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
    Constrained {
      constraint: self.constraint & rhs,
      ..self
    }
  }
}

impl<'ctx, T: Clone> BitAnd<Bool<'ctx>> for &Constrained<'ctx, T> {
  type Output = Constrained<'ctx, T>;

  fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
    Constrained {
      constraint: &self.constraint & rhs,
      content: self.content.clone(),
    }
  }
}

impl<'ctx, T> Constrained<'ctx, T> {
  pub fn unconstrained(x: T, ctx: &'ctx Context) -> Self {
    Self {
      content: x,
      constraint: Bool::from_bool(ctx, true),
    }
  }

  pub fn simplify(self) -> Self {
    Self {
      constraint: self.constraint.simplify(),
      ..self
    }
  }
}

pub type ConstrainedArray<'ctx> = Constrained<'ctx, Array<'ctx>>;

pub type ConstrainedBool<'ctx> = Constrained<'ctx, Bool<'ctx>>;

impl<'ctx> ConstrainedBool<'ctx> {
  pub fn default(ctx: &'ctx Context) -> Self {
    Constrained::unconstrained(Bool::fresh_const(ctx, ""), ctx)
  }
}

pub struct GlobalState<'ctx> {
  ctx: &'ctx Context,
  pub global_state: BTreeMap<QualifiedInstId<StructId>, Vec<ConstrainedArray<'ctx>>>,
  pub resource_exists: BTreeMap<QualifiedInstId<StructId>, Vec<ConstrainedBool<'ctx>>>,
}

impl<'ctx> GlobalState<'ctx> {
  pub fn new_empty(ctx: &'ctx Context) -> Self {
    Self {
      ctx,
      global_state: BTreeMap::new(),
      resource_exists: BTreeMap::new(),
    }
  }

  pub fn get_ctx(&self) -> &'ctx Context {
    self.ctx
  }

  /// Initialize resource and return the initial value.
  pub fn init_global_state(&mut self, resource: &QualifiedInstId<StructId>) -> ConstrainedArray<'ctx> {
    let init_val: ConstrainedArray<'ctx> = Constrained {
      content: Array::fresh_const(self.get_ctx(), "", &Sort::bitvector(self.get_ctx(), PrimitiveValue::LENGTH), todo!()),
      constraint: Bool::from_bool(self.get_ctx(), true)
    };
    self.global_state.insert(
      resource.clone(),
      vec![init_val.clone()],
    );
    init_val
  }

  /// Initialize resource and return the initial value.
  pub fn init_resource_map(&mut self, resource: &QualifiedInstId<StructId>) -> ConstrainedBool<'ctx> {
    let init_val: ConstrainedBool<'ctx> = Constrained {
      content: Bool::fresh_const(self.get_ctx(), ""),
      constraint: Bool::from_bool(self.get_ctx(), true)
    };
    self.resource_exists.insert(
      resource.clone(),
      vec![init_val.clone()],
    );
    init_val
  }

  /// Return the condition that resource_type exists.
  /// `self.resource_exists` is updated if `resource_type` is not contained.
  pub fn exists(&mut self, resource_type: &QualifiedInstId<StructId>) -> Constraint<'ctx> {
    match self.resource_exists.get(resource_type) {
      Some(constrained_bools) => {
        constrained_bools.iter().fold(
          Bool::from_bool(self.get_ctx(), false),
          |acc, x| {
            acc | (&x.content & &x.constraint).simplify()
          }
        )
      }
      None => {
        let fresh_bool: Bool = Bool::fresh_const(self.get_ctx(), "");
        self.resource_exists.insert(
          resource_type.clone(),
          vec![
            Constrained { content: fresh_bool.clone(), constraint: Bool::from_bool(self.get_ctx(), true) }
            ],
        );
        fresh_bool
      }
    }
  }
}

#[derive(Clone)]
pub struct MoveState<'ctx, 'env> {
  function_target: FunctionTarget<'env>,
  label_to_offset: BTreeMap<Label, CodeOffset>,
  pub offset_to_block_id: BTreeMap<CodeOffset, BlockId>,
  pub bytecodes: &'env [Bytecode],
  local_state: LocalState<'ctx>,
}

impl<'ctx, 'env> fmt::Display for MoveState<'ctx, 'env> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      // Customize so only `x` and `y` are denoted.
      write!(f, "{}", self.local_state)
  }
}

impl<'ctx, 'env> PartialEq for MoveState<'ctx, 'env> {
  fn eq(&self, other: &Self) -> bool {
    !self.is_final() && !other.is_final() && self.local_state.similar(&other.local_state)
  }
}

impl<'ctx, 'env> Eq for MoveState<'ctx, 'env> {}

use std::cmp::Ordering;
/// `MoveState` is ordered by block id.
impl<'ctx, 'env> PartialOrd for MoveState<'ctx, 'env> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    self.cur_block_id().partial_cmp(&other.cur_block_id())
  }
}

impl<'ctx, 'env> Ord for MoveState<'ctx, 'env> {
  fn cmp(&self, other: &Self) -> Ordering {
    self
      .cur_block_id()
      .partial_cmp(&other.cur_block_id())
      .unwrap()
  }
}

impl<'ctx, 'env> Hash for MoveState<'ctx, 'env> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.local_state.ic.hash(state);
  }
}

impl<'ctx, 'env> State for MoveState<'ctx, 'env> {
  fn merge(self, other: Self) -> Option<Self> {
    if self == other {
      Some(MoveState {
        local_state: LocalState {
          pc: (&self.local_state().pc | &other.local_state().pc).simplify(),
          locals: {
            self
              .local_state
              .locals
              .into_iter()
              .zip(other.local_state.locals.into_iter())
              .map(|(x, y)| x | y)
              .collect()
          },
          ..self.local_state
        },
        ..self
      })
    } else {
      None
    }
  }
}

/// Get the uninitiated struct type.
fn get_struct_type(global_env: &GlobalEnv, mod_id: ModuleId, struct_id: StructId) -> Type {
  let struct_env = global_env.get_struct(mod_id.qualified(struct_id));
  let field_types: Vec<Type> = struct_env
    .get_fields()
    .map(|field_env| {
      field_env.get_type()
    })
    .collect();
  Type::Struct(mod_id, struct_id, field_types)
}

mod eval {
  use super::*;
  use move_stackless_bytecode::stackless_bytecode::{AbortAction, AssignKind, Constant, Operation};

  // Evaluate an `Assign`.
  fn assign<'ctx>(
    dst: TempIndex,
    src: TempIndex,
    kind: &AssignKind,
    mut s: LocalState<'ctx>,
  ) -> LocalState<'ctx> {
    let src_val = match kind {
      AssignKind::Move => s.del(src),
      AssignKind::Copy | AssignKind::Store => s.index(src).content.clone(),
    };
    s.index_mut(dst).content = src_val;
    s.ic += 1;
    s
  }

  // Evaluate a `Load`.
  fn load<'ctx>(dst: TempIndex, c: &Constant, mut s: LocalState<'ctx>) -> LocalState<'ctx> {
    s[dst].content = vec![ConstrainedValue::new(
      Value::from_constant(c, s.get_ctx()),
      s.pc.clone(),
    )];
    s.ic += 1;
    s
  }

  // Evaluate a `Jump`.
  fn jump<'ctx>(
    label: &Label,
    label_to_offset: &BTreeMap<Label, CodeOffset>,
    s: LocalState<'ctx>,
  ) -> LocalState<'ctx> {
    LocalState {
      ic: *label_to_offset.get(label).unwrap(),
      ..s
    }
  }

  // Evaluate a `Branch`.
  fn branch<'ctx>(
    ctx: &'ctx Context,
    label_to_offset: &BTreeMap<Label, CodeOffset>,
    cond: TempIndex,
    then_label: &Label,
    else_label: &Label,
    s: LocalState<'ctx>,
  ) -> Vec<LocalState<'ctx>> {
    let BranchCondition { true_branch, false_branch } = s.index(cond).to_branch_condition(ctx);
    vec![
      jump(then_label, label_to_offset, s.clone() & true_branch),
      jump(else_label, label_to_offset, s & false_branch),
    ]
  }

  // Handle pure operations.
  fn pure_operation<'ctx, F>(
    dsts: &[TempIndex],
    op: F,
    srcs: &[TempIndex],
    mut s: LocalState<'ctx>,
  ) -> LocalState<'ctx>
  where
    F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>>,
  {
    let constrined_args = s.args(srcs);
    for &x in dsts {
      s.index_mut(x).del();
    }
    for (args, constraint) in constrined_args {
      let res = op(args);
      debug_assert!(res.len() == dsts.len());
      for (&x, val) in dsts.iter().zip(res.into_iter()) {
        s.index_mut(x)
          .content
          .push(ConstrainedValue::new(val, constraint.clone()))
      }
    }
    s
  }

  fn operation<'ctx>(
    dsts: &[TempIndex],
    op: &Operation,
    srcs: &[TempIndex],
    _on_abort: Option<&AbortAction>,
    mut s: LocalState<'ctx>,
    global_env: &GlobalEnv,
  ) -> LocalState<'ctx> {
    use Operation::*;
    s.ic += 1;
    match op {
      // Pack(ModuleId, StructId, Vec<Type>),
      Pack(mod_id, struct_id, type_params) => {
        let ctx = s.get_ctx();
        pure_operation(
        dsts,
        |x: Vec<Value>| {
          let struct_type = get_struct_type(global_env, *mod_id, *struct_id);
          let instantiated_struct_type = struct_type.instantiate(type_params);
          if let Type::Struct(_, _, types) = instantiated_struct_type {
            vec![
              Value::Struct({
                let data_type = struct_type_to_datatype_sort(*mod_id, *struct_id, &types, ctx);
                data_type.variants[0].constructor.apply(
                  x.iter().map(|x| x.to_ast()).collect::<Vec<&dyn Ast>>().as_slice()
                ).as_datatype().unwrap()
              })
            ]
          } else {
            panic!()
          }
        },
        srcs,
        s
      )}
      // Unpack(ModuleId, StructId, Vec<Type>),

      // Unary
      // CastU8 => todo!
      // CastU64 => todo!
      // CastU128 => todo!
      Not => pure_operation(
        dsts,
        |x: Vec<Value>| {
          assert_eq!(x.len(), 1);
          vec![!x.index(0)]
        },
        srcs,
        s
      ),
      // Binary
      Add => pure_operation(
        dsts,
        |x: Vec<Value>| {
          assert_eq!(x.len(), 2);
          vec![x.index(0) + x.index(1)]
        },
        srcs,
        s
      ),
      Mul => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x.index(0) * x.index(1)]
        },
        srcs,
        s,
      ),
      Div => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x.index(0) / x.index(1)]
        },
        srcs,
        s,
      ),
      Mod => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x.index(0) % x.index(1)]
        },
        srcs,
        s,
      ),
      BitOr => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x.index(0) | x.index(1)]
        },
        srcs,
        s,
      ),
      BitAnd => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x.index(0) & x.index(1)]
        },
        srcs,
        s,
      ),
      Xor => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x.index(0) ^ x.index(1)]
        },
        srcs,
        s,
      ),
      // Shl,
      // Shr,
      Lt => pure_operation(
        dsts,
        |x| {
          println!("fjdkf");
          assert_eq!(x.len(), 2);
          vec![x[0].lt(&x[1])]
        },
        srcs,
        s,
      ),
      Gt => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].gt(&x[1])]
        },
        srcs,
        s,
      ),
      Le => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].le(&x[1])]
        },
        srcs,
        s,
      ),
      Ge => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].ge(&x[1])]
        },
        srcs,
        s,
      ),
      Or => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].or(&x[1])]
        },
        srcs,
        s,
      ),
      And => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].and(&x[1])]
        },
        srcs,
        s,
      ),
      Eq => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].eq(&x[1])]
        },
        srcs,
        s,
      ),
      Neq => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].neq(&x[1])]
        },
        srcs,
        s,
      ),
      // CastU256,
      _ => s,
      _ => todo!(),
    }
  }

  pub fn step<'ctx, 'env>(
    mut s: MoveState<'ctx, 'env>,
    instr: &Bytecode,
  ) -> Vec<MoveState<'ctx, 'env>> {
    match instr {
      Bytecode::Assign(_, dst, src, kind) => vec![MoveState {
        local_state: assign(*dst, *src, kind, s.local_state),
        ..s
      }],
      Bytecode::Call(_, dsts, op, srcs, on_abort) => {
        let global_env = s.get_global_env();
        s.local_state = operation(dsts, op, srcs, on_abort.as_ref(), s.local_state, global_env);
        vec![s]
      }
      Bytecode::Ret(_, srcs) => 
        vec![{
          s.local_state.ts = TerminationStatus::Return(
            srcs
              .iter()
              .map(|&x| s.local_state[x].content.clone())
              .collect()
          );
          s
        }],
      Bytecode::Load(_, dst, c) => vec![MoveState {
        local_state: load(*dst, c, s.local_state),
        ..s
      }],
      Bytecode::Label(_, _) => {
        s.local_state.ic += 1;
        vec![s]
      }
      Bytecode::Jump(_, label) => vec![MoveState {
        local_state: jump(label, &s.label_to_offset, s.local_state),
        ..s
      }],
      Bytecode::Branch(_, then_label, else_label, cond) => {
        let label_to_offset = &s.label_to_offset;
        branch(
          s.local_state.get_ctx(),
          label_to_offset,
          *cond,
          then_label,
          else_label,
          s.local_state.clone(),
        )
        .into_iter()
        .map(|local_state| MoveState {
          local_state,
          ..s.clone()
        })
        .collect()
      }
      Bytecode::Abort(_, index) => {
        s.local_state.ts = TerminationStatus::Abort(s.local_state[*index].content.clone());
        vec![s]
      },
      _ => {
        s.local_state.ic += 1;
        vec![s]
      }
    }
  }
}

impl<'ctx, 'env> Transition for MoveState<'ctx, 'env> {
  type IntoIter = Vec<MoveState<'ctx, 'env>>;

  fn suc(self) -> Vec<MoveState<'ctx, 'env>> {
    assert!(!self.is_final());
    let instr = self.cur_instr().clone();
    eval::step(self, &instr)
  }

  fn is_final(&self) -> bool {
    self.local_state().ic() >= self.bytecodes.len() as u16
      || self.local_state().termination_status().is_final()
  }
}

use move_stackless_bytecode::{stackless_control_flow_graph::{StacklessControlFlowGraph, BlockContent}};
pub fn topo_sort(cfg: &StacklessControlFlowGraph) -> Vec<BlockId> {
  fn visit(s: BlockId, visited: &mut Vec<bool>, res: &mut Vec<BlockId>, cfg: &StacklessControlFlowGraph) {
    if !visited[s as usize] {
      visited[s as usize] = true;
      for &t in cfg.successors(s) {
        visit(t, visited, res, cfg);
      }
      res.push(s);
    }
  }
  let mut res = Vec::with_capacity(cfg.num_blocks() as usize);
  let mut visited = Vec::with_capacity(cfg.num_blocks() as usize);
  for _ in 0..cfg.num_blocks() {
    visited.push(false);
  }
  visit(cfg.entry_block(), &mut visited, &mut res, cfg);
  res.reverse();
  res
}

impl<'ctx, 'env> MoveState<'ctx, 'env> {
  fn generate_offset_to_block_id(bytecodes: &[Bytecode]) -> BTreeMap<CodeOffset, BlockId> {
    let mut offset_to_block_id = BTreeMap::new();
    let cfg = StacklessControlFlowGraph::new_forward(bytecodes);
    let sorted_block_id = topo_sort(&cfg);
    for i in 0..cfg.num_blocks() {
      match cfg.content(sorted_block_id[i as usize]) {
        BlockContent::Basic{ lower, upper } => {
          for code_offset in *lower..*upper+1 {
            offset_to_block_id.insert(code_offset, i);
          }
        },
        BlockContent::Dummy => (),
      }
    }
    offset_to_block_id
  }
}

impl<'ctx, 'env> MoveState<'ctx, 'env> {
  pub fn new_default(
    ctx: &'ctx Context,
    function_target: FunctionTarget<'env>,
  ) -> Self {
    Self {
      label_to_offset: Bytecode::label_offsets(function_target.data.code.as_slice()),
      offset_to_block_id: Self::generate_offset_to_block_id(function_target.data.code.as_slice()),
      bytecodes: function_target.data.code.as_slice(),
      local_state: LocalState::new_default(ctx, {
        let mut locals: Vec<Local<'ctx>> = Vec::new();
        let symbol_pool = function_target.symbol_pool();
        for local_index in 0..function_target.get_local_count() {
          let local_symbol = function_target.get_local_name(local_index);
          let local_name: String = symbol_pool.string(local_symbol).to_string();
          let local_type = function_target.get_local_type(local_index);
          locals.push(
            if local_index < function_target.get_parameter_count() {
              Local::from_type(local_name, &local_type, ctx)
            } else {
              Local::new()
            }
          );
        }
        locals
      }),
      function_target
    }
  }

  // Getters

  pub fn get_function_env(&self) -> &FunctionEnv<'env> {
    self.function_target.func_env
  }

  pub fn get_function_data(&self) -> &FunctionData {
    self.function_target.data
  }

  pub fn get_global_env(&self) -> &'env GlobalEnv {
    self.get_function_env().module_env.env
  }

  /// Return the local state.
  pub fn local_state(&self) -> &LocalState<'ctx> {
    &self.local_state
  }

  // return the instruction to be executed
  // panics if the ic is invalid
  fn cur_instr(&self) -> &Bytecode {
    self
      .bytecodes
      .get(self.local_state().ic() as usize)
      .unwrap()
  }

  fn cur_block_id(&self) -> BlockId {
    *self.offset_to_block_id.get(&self.local_state.ic).unwrap()
  }
}

pub struct MoveStateSet<'ctx, 'env>(BTreeSet<MoveState<'ctx, 'env>>);

impl<'ctx, 'env> MoveStateSet<'ctx, 'env> {
  pub fn first(&self) -> Option<MoveState<'ctx, 'env>> {
    match self.0.iter().next() {
      Some(s) => Some(s.clone()),
      None => None,
    }
  }
}

impl<'ctx, 'env> StateSet<MoveState<'ctx, 'env>> for MoveStateSet<'ctx, 'env> {
  fn new() -> Self {
    Self(BTreeSet::new())
  }

  fn insert(&mut self, s: MoveState<'ctx, 'env>) {
    match self.0.take(&s) {
      Some(t) => self.0.insert(t.merge(s).unwrap()),
      None => self.0.insert(s),
    };
  }

  fn remove(&mut self, s: &MoveState<'ctx, 'env>) -> Option<MoveState<'ctx, 'env>> {
    self.0.take(s)
  }

  fn is_empty(&self) -> bool {
    self.0.is_empty()
  }
}
