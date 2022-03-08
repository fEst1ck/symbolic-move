//! # Evaluation State
use crate::value::{ConstrainedValue, Constraint, Type, Value};
use move_stackless_bytecode::{
  stackless_bytecode::{Bytecode, Label},
};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::ops::{BitAnd, BitOr};
use symbolic_evaluation::traits::{State, StateSet, Transition};
use z3::{
  ast::{Ast, Bool},
  Context, SatResult, Solver,
};

pub type CodeOffset = u16;
pub type TempIndex = usize;
pub type BlockId = CodeOffset;

pub type Union<'ctx> = Vec<ConstrainedValue<'ctx>>;

#[derive(Clone, Debug)]
pub enum TerminationStatus<'ctx> {
  None,
  Return(Vec<Union<'ctx>>),
  Abort,
  Unsat,
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

  pub fn from_type(t: &Type, ctx: &'ctx Context) -> Self {
    Self {
      content: vec![ConstrainedValue::from_type(t, ctx)],
    }
  }

  /// Turn a local of boolean sort into a constraint.
  pub fn to_constraint(&self, ctx: &'ctx Context) -> Constraint<'ctx> {
    self
      .content
      .clone()
      .into_iter()
      .map(|x| x.to_constraint())
      .fold(Bool::from_bool(ctx, true), |acc, x| (acc | x).simplify())
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
    LocalState {
      pc: (&self.pc & &rhs).simplify(),
      locals: self.locals.into_iter().map(|x| x & rhs.clone()).collect(),
      ..self
    }
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
      let solver = Solver::new(ctx);
      solver.assert(&constraint);
      match solver.check() {
        SatResult::Unsat => None,
        _ => {
          xs.push(x);
          Some((xs, constraint))
        }
      }
    }
    // v = (x, p) vs = (((y ...), q) ...)
    // return (((y ... x), q & p) ...) where q & p not unsat
    fn add_operand1<'ctx>(
      ctx: &'ctx Context,
      v: ConstrainedValue<'ctx>,
      args: Vec<(Vec<Value<'ctx>>, Constraint<'ctx>)>,
    ) -> Vec<(Vec<Value<'ctx>>, Constraint<'ctx>)> {
      let mut res = Vec::new();
      for arg in args {
        if let Some(arg) = add_operand(ctx, v.clone().decompose(), arg) {
          res.push(arg)
        }
      }
      res
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
    srcs.iter().fold(Vec::new(), |acc, &x| {
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

#[derive(Clone, Debug)]
pub struct MoveState<'bytecodes, 'ctx> {
  label_to_offset: BTreeMap<Label, CodeOffset>,
  offset_to_block_id: BTreeMap<CodeOffset, CodeOffset>,
  bytecodes: &'bytecodes [Bytecode],
  local_state: LocalState<'ctx>,
}

impl<'bytecodes, 'ctx> PartialEq for MoveState<'bytecodes, 'ctx> {
  fn eq(&self, other: &Self) -> bool {
    !self.is_final() && !other.is_final() && self.local_state.similar(&other.local_state)
  }
}

impl<'bytecodes, 'ctx> Eq for MoveState<'bytecodes, 'ctx> {}

use std::cmp::Ordering;
/// `MoveState` is ordered by block id.
impl<'bytecodes, 'ctx> PartialOrd for MoveState<'bytecodes, 'ctx> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    self.cur_block_id().partial_cmp(&other.cur_block_id())
  }
}

impl<'bytecodes, 'ctx> Ord for MoveState<'bytecodes, 'ctx> {
  fn cmp(&self, other: &Self) -> Ordering {
    self
      .cur_block_id()
      .partial_cmp(&other.cur_block_id())
      .unwrap()
  }
}

impl<'bytecodes, 'ctx> Hash for MoveState<'bytecodes, 'ctx> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.local_state.ic.hash(state);
  }
}

impl<'bytecodes, 'ctx> State for MoveState<'bytecodes, 'ctx> {
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
    let constraint = s.index(cond).to_constraint(ctx);
    vec![
      jump(then_label, label_to_offset, s.clone() & constraint.clone()),
      jump(else_label, label_to_offset, s & !constraint),
    ]
  }

  // Handle pure operations.
  fn pure_operation<'ctx, F>(
    dsts: &[TempIndex],
    op: F,
    srcs: &[TempIndex],
    s: &mut LocalState<'ctx>,
  ) where
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
  }

  fn operation<'ctx>(
    dsts: &[TempIndex],
    op: &Operation,
    srcs: &[TempIndex],
    _on_abort: Option<&AbortAction>,
    s: &mut LocalState,
  ) {
    use Operation::*;
    match op {
      // Unary
      // CastU8 => todo!
      // CastU64 => todo!
      // CastU128 => todo!
      // Not => todo!
      // Binary
      Add => pure_operation(
        dsts,
        |x: Vec<Value>| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone() + x[1].clone()]
        },
        srcs,
        s,
      ),
      Mul => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone() * x[1].clone()]
        },
        srcs,
        s,
      ),
      Div => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone() / x[1].clone()]
        },
        srcs,
        s,
      ),
      Mod => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone() % x[1].clone()]
        },
        srcs,
        s,
      ),
      BitOr => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone() | x[1].clone()]
        },
        srcs,
        s,
      ),
      BitAnd => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone() & x[1].clone()]
        },
        srcs,
        s,
      ),
      Xor => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone() ^ x[1].clone()]
        },
        srcs,
        s,
      ),
      // Shl,
      // Shr,
      Lt => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().lt(x[1].clone())]
        },
        srcs,
        s,
      ),
      Gt => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().gt(x[1].clone())]
        },
        srcs,
        s,
      ),
      Le => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().le(x[1].clone())]
        },
        srcs,
        s,
      ),
      Ge => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().ge(x[1].clone())]
        },
        srcs,
        s,
      ),
      Or => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().or(x[1].clone())]
        },
        srcs,
        s,
      ),
      And => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().and(x[1].clone())]
        },
        srcs,
        s,
      ),
      Eq => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().eq(x[1].clone())]
        },
        srcs,
        s,
      ),
      Neq => pure_operation(
        dsts,
        |x| {
          assert_eq!(x.len(), 2);
          vec![x[0].clone().neq(x[1].clone())]
        },
        srcs,
        s,
      ),
      // CastU256,
      _ => todo!(),
    }
    s.ic += 1;
  }

  pub fn step<'bytecodes, 'ctx>(
    mut s: MoveState<'bytecodes, 'ctx>,
    instr: &Bytecode,
  ) -> Vec<MoveState<'bytecodes, 'ctx>> {
    match instr {
      Bytecode::Assign(_, dst, src, kind) => vec![MoveState {
        local_state: assign(*dst, *src, kind, s.local_state),
        ..s
      }],
      Bytecode::Call(_, dsts, op, srcs, on_abort) => {
        operation(dsts, op, srcs, on_abort.as_ref(), &mut s.local_state);
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
      _ => todo!(),
    }
  }
}

impl<'bytecodes, 'ctx> Transition for MoveState<'bytecodes, 'ctx> {
  type IntoIter = Vec<MoveState<'bytecodes, 'ctx>>;

  fn suc(self) -> Vec<MoveState<'bytecodes, 'ctx>> {
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

impl<'bytecodes, 'ctx> MoveState<'bytecodes, 'ctx> {
  pub fn new(
    bytecodes: &'bytecodes [Bytecode],
    local_state: LocalState<'ctx>,
  ) -> Self {
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
    Self {
      label_to_offset: Bytecode::label_offsets(bytecodes),
      offset_to_block_id,
      bytecodes,
      local_state,
    }
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

pub struct MoveStateSet<'bytecode, 'ctx>(BTreeSet<MoveState<'bytecode, 'ctx>>);

impl<'bytecode, 'ctx> MoveStateSet<'bytecode, 'ctx> {
  pub fn first(&self) -> Option<MoveState<'bytecode, 'ctx>> {
    match self.0.iter().next() {
      Some(s) => Some(s.clone()),
      None => None,
    }
  }
}

impl<'bytecode, 'ctx> StateSet<MoveState<'bytecode, 'ctx>> for MoveStateSet<'bytecode, 'ctx> {
  fn new() -> Self {
    Self(BTreeSet::new())
  }

  fn insert(&mut self, s: MoveState<'bytecode, 'ctx>) {
    match self.0.take(&s) {
      Some(t) => self.0.insert(t.merge(s).unwrap()),
      None => self.0.insert(s),
    };
  }

  fn remove(&mut self, s: &MoveState<'bytecode, 'ctx>) -> Option<MoveState<'bytecode, 'ctx>> {
    self.0.take(s)
  }

  fn is_empty(&self) -> bool {
    self.0.is_empty()
  }
}
