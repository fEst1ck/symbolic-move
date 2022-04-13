//! # Evaluation State
use crate::{value::{
    ConstrainedValue,
    PrimitiveValue, Value,
}, constraint::{Constrained, Constraint, sat, Disjoints},
    ty::{Type, Datatypes, ResourceId},
};
use itertools::Itertools;
use move_model::model::{
    FunctionEnv, GlobalEnv, QualifiedInstId,
};
use move_stackless_bytecode::{
    function_target::{FunctionData, FunctionTarget},
    stackless_bytecode::{Bytecode, Label},
};
use std::{fmt, cell::{RefCell}};
use std::hash::{Hash, Hasher};
use std::ops::{BitAnd, BitOr};
use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};
use symbolic_evaluation::traits::{State, StateSet, Transition};
use z3::{
    ast::{Array, Ast, Bool, Datatype, BV, Dynamic},
    Context, Sort, Symbol,
};

pub type CodeOffset = u16;
pub type TempIndex = usize;
pub type BlockId = CodeOffset;

#[derive(Clone)]
pub enum TerminationStatus<'ctx> {
    None,
    Return(Vec<Disjoints<'ctx, Value<'ctx>>>),
    Abort(Disjoints<'ctx, Value<'ctx>>),
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
            TerminationStatus::Abort(val) => {
                writeln!(f, "Aborts with error code {}.", val.iter().format(", "))
            }
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

/// Local variable
#[derive(Clone)]
pub struct Local<'ctx> {
    content: Disjoints<'ctx, Value<'ctx>>,
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
        Local { content: self.content & rhs }
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
            content: Disjoints(Vec::new()),
        }
    }

    pub fn simplify(self) -> Self {
        Self {
            content: self.content.into_iter().map(|x| x.simplify()).collect()
        }
    }

    pub fn from_type<'env, S: Into<Symbol>>(x: S, t: &Type, ctx: &'ctx Context, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>) -> Self {
        Self {
            content: Disjoints(vec![ConstrainedValue::new_const(x, t, ctx, datatypes)]),
        }
    }

    pub fn to_branch_condition(&self, ctx: &'ctx Context) -> Option<BranchCondition<'ctx>> {
        let mut acc = BranchCondition::or_id(ctx);
        for cv in self.content.clone() {
            match cv.to_branch_condition() {
                Some(bc) => acc = (acc | bc).simplify(),
                None => return None
            }
        }
        Some(acc)
    }

    /// Set the content to empty, and return the original value.
    pub fn del(&mut self) -> Disjoints<'ctx, Value<'ctx>> {
        let res = self.content.clone();
        self.content = Disjoints(Vec::new());
        res
    }

    /// Return the number of possible values of the local.
    pub fn len(&self) -> usize {
        self.content.0.len()
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
                content: Disjoints(merge_content(self.content.0, other.content.0)),
            }
        } else {
            self.content.0.append(&mut other.content.0);
            self
        }
    }
}

/// Local evaluation state
#[derive(Clone)]
pub struct LocalState<'ctx> {
    pub(crate) context: &'ctx Context,
    /// Instruction Counter
    pub(crate) ic: CodeOffset,
    /// Path constraint
    pub(crate) pc: Constraint<'ctx>,
    pub(crate) ts: TerminationStatus<'ctx>,
    pub(crate) locals: Vec<Local<'ctx>>,
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
        if sat(&new_pc) {
            LocalState {
                pc: new_pc,
                locals: self.locals.into_iter().map(|x| (x & rhs.clone()).simplify()).collect(),
                ..self
            }
        } else {
            LocalState {
                pc: new_pc,
                locals: self.locals.into_iter().map(|x| (x & rhs.clone()).simplify()).collect(),
                ts: TerminationStatus::Unsat,
                ..self
            }
        }
    }
}

impl<'ctx, 'env> fmt::Display for LocalState<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "LocalState")?;
        writeln!(
            f,
            "Instruction Counter: {} | Path Constraint: {}",
            self.ic, self.pc
        )?;
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

    pub fn new_default(context: &'ctx Context, locals: Vec<Local<'ctx>>) -> Self {
        Self {
            context,
            ic: 0,
            pc: Bool::from_bool(context, true),
            ts: TerminationStatus::None,
            locals,
        }
    }

    /// Return constrained tuples of operation arguments.
    pub fn args(&self, srcs: &[TempIndex]) -> Disjoints<'ctx, Vec<Value<'ctx>>> {
        srcs
            .iter()
            .map(|idx| self.index(*idx).content.clone().map(|x| vec![x]))
            .fold(
                Disjoints::unit(self.get_ctx()),
                |acc, x| acc.mappend(x)
            )
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
    pub fn del(&mut self, var: TempIndex) -> Disjoints<'ctx, Value<'ctx>> {
        self.index_mut(var).del()
    }
}

pub type ConstrainedArray<'ctx> = Constrained<'ctx, Array<'ctx>>;

pub type ConstrainedBool<'ctx> = Constrained<'ctx, Bool<'ctx>>;

impl<'ctx> ConstrainedBool<'ctx> {
    pub fn default(ctx: &'ctx Context) -> Self {
        Constrained::pure(Bool::fresh_const(ctx, ""), ctx)
    }
}

/// Global evaluation state
#[derive(Clone)]
pub struct GlobalState<'ctx> {
    ctx: &'ctx Context,
    pub resource_value: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>,
    pub resource_existence: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>,
}

impl<'ctx> GlobalState<'ctx> {
    pub fn new_empty(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            resource_value: BTreeMap::new(),
            resource_existence: BTreeMap::new(),
        }
    }

    pub fn get_ctx(&self) -> &'ctx Context {
        self.ctx
    }

    // Initialize resource value.
    // acquire: called only when `resource` is not in `resource_value`.
    fn init_resource_value<'env>(&mut self, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>, resource: &ResourceId) {
        let init_val: ConstrainedArray<'ctx> = Constrained {
            content: Array::fresh_const(
                self.get_ctx(),
                "global memory",
                &Sort::bitvector(self.get_ctx(), PrimitiveValue::ADDR_LENGTH),
                &datatypes.borrow_mut().from_struct(&resource).sort,
            ),
            constraint: Bool::from_bool(self.get_ctx(), true),
        };
        self.resource_value
            .insert(resource.clone(), Disjoints(vec![init_val]));
    }

    // Similar to `init_resource_value`.
    fn init_resource_existence(&mut self, resource: &ResourceId) {
        let init_val: ConstrainedArray<'ctx> = Constrained {
            content: Array::fresh_const(
                self.get_ctx(),
                "global memory domain",
                &Sort::bitvector(self.get_ctx(), PrimitiveValue::ADDR_LENGTH),
                &Sort::bool(self.get_ctx()),
            ),
            constraint: Bool::from_bool(self.get_ctx(), true),
        };
        self.resource_existence
            .insert(resource.clone(), Disjoints(vec![init_val]));
    }

    pub fn get_resource_existence(
        &mut self,
        resource: &ResourceId,
    ) -> Disjoints<'ctx, Array<'ctx>> {
        match self.resource_existence.get(resource) {
            Some(arrays) => arrays.clone(),
            None => {
                self.init_resource_existence(resource);
                self.get_resource_existence(resource).clone()
            }
        }
    }

    /// Return the condition that resource_type exists.
    /// `self.resource_existence` is updated if `resource_type` is not contained.
    pub fn exists(
        &mut self,
        resource_type: &ResourceId,
        addr: &Disjoints<'ctx, Value<'ctx>>,
    ) -> Disjoints<'ctx, Constraint<'ctx>> {
        let resource_existence = self.get_resource_existence(resource_type);
        resource_existence
            .prod(addr)
            .map(|(array, value)| {
                array
                    .select(value.as_addr().unwrap())
                    .as_bool()
                    .expect("resource_existence contains non-boolean")
        })
    }

    pub fn real_move_to<'env>(
        &mut self,
        resource_type: &ResourceId,
        addrs: &Disjoints<'ctx, BV<'ctx>>,
        resource: Disjoints<'ctx, Datatype<'ctx>>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) {
        // update resource value map so that addr contains value
        // update resource existence map so that addr contains true
        match self.resource_value.get(resource_type) {
            Some(resource_value_maps) => {
                let resource_vals: Disjoints<'ctx, Datatype<'ctx>> = resource;
                let new_resource_value_map = resource_value_maps
                    .prod(addrs)
                    .prod(&resource_vals)
                    .map(|((array, addr), resource_val)| array.store(&addr, &resource_val));
                let resource_existence_map: &Disjoints<Array> =
                    self.resource_existence.get(resource_type).unwrap(); // already inited when checking for existence
                let new_resource_existence_map =
                    resource_existence_map
                        .prod(addrs)
                        .map(|(array, addr)| {
                            array.store(&addr, &Bool::from_bool(self.get_ctx(), true))
                        });
                self.resource_value
                    .insert(resource_type.clone(), new_resource_value_map);
                self.resource_existence
                    .insert(resource_type.clone(), new_resource_existence_map);
            }
            None => {
                self.init_resource_value(datatypes.clone(), resource_type);
                self.real_move_to(resource_type, addrs, resource, datatypes);
            }
        }
    }

    pub fn real_move_from<'env>(
        &mut self,
        resource_type: &ResourceId,
        addrs: &Disjoints<'ctx, BV<'ctx>>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) -> Disjoints<'ctx, Dynamic<'ctx>> {
        // update resource value map so that addr contains value
        // update resource existence map so that addr contains true
        match self.resource_value.get(resource_type) {
            Some(resource_value_maps) => {
                let ret_vals = resource_value_maps.prod(addrs).map(
                    |(global_mem, addr)| global_mem.select(&addr)
                );
                let resource_existence_map: &Disjoints<Array> =
                    self.resource_existence.get(resource_type).unwrap(); // already inited when checking for existence
                let new_resource_existence_map = resource_existence_map
                    .prod(addrs)
                    .map(|(array, addr)| array.store(&addr, &Bool::from_bool(self.get_ctx(), false)));
                self.resource_existence
                    .insert(resource_type.clone(), new_resource_existence_map);
                ret_vals
            }
            None => {
                self.init_resource_value(datatypes.clone(), resource_type);
                self.real_move_from(resource_type, addrs, datatypes)
            }
        }
    }
}

impl<'ctx> BitAnd<Bool<'ctx>> for GlobalState<'ctx> {
    type Output = Self;

    fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
        match self {
            GlobalState { ctx, resource_value, resource_existence } => {
                GlobalState {
                    ctx,
                    resource_value: resource_value.into_iter().map(|(k, v)| (k, v & &rhs)).collect(),
                    resource_existence: resource_existence.into_iter().map(|(k, v)| (k, v & &rhs)).collect(),
                }
            }
        }
    }
}

/// Move evaluation state
#[derive(Clone)]
pub struct MoveState<'ctx, 'env> {
    function_target: FunctionTarget<'env>,
    label_to_offset: BTreeMap<Label, CodeOffset>,
    pub(crate) offset_to_block_id: BTreeMap<CodeOffset, BlockId>,
    pub(crate) bytecodes: &'env [Bytecode],
    pub(crate) local_state: LocalState<'ctx>,
    global_state: GlobalState<'ctx>,
    datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
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
        self.cur_block_id()
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
                    pc: (&self.get_local_state().pc | &other.get_local_state().pc).simplify(),
                    locals: {
                        self.local_state
                            .locals
                            .into_iter()
                            .zip(other.local_state.locals.into_iter())
                            .map(|(x, y)| (x | y).simplify())
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

/// A pair of disjoint constraints. So true_branch & false_branch is never satisfiable.
pub struct BranchCondition<'ctx> {
    pub true_branch: Constraint<'ctx>,
    pub false_branch: Constraint<'ctx>,
}
  
impl<'ctx> BitOr for BranchCondition<'ctx> {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
        (
            BranchCondition { true_branch: t1, false_branch: f1 },
            BranchCondition { true_branch: t2, false_branch: f2 },
        ) => BranchCondition { true_branch: t1 | t2, false_branch: f1 | f2 },
        }
    }
}

impl<'ctx> BranchCondition<'ctx> {
    /// The identity element of the | operation.
    pub fn or_id(ctx: &'ctx Context) -> Self {
        BranchCondition { true_branch: Bool::from_bool(ctx, false), false_branch: Bool::from_bool(ctx, false) }
    }

    /// Simplify fields.
    pub fn simplify(self) -> Self {
        match self {
        BranchCondition { true_branch, false_branch } => BranchCondition { true_branch: true_branch.simplify(), false_branch: false_branch.simplify() }
        }
    }
}

mod eval {
    use crate::ty::new_resource_id;

    use super::*;
    use move_stackless_bytecode::stackless_bytecode::{
        AbortAction, AssignKind, Constant, Operation,
    };

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
        s[dst].content = Disjoints(
            vec![ConstrainedValue::new(
                Value::from_constant(c, s.get_ctx()),
                s.pc.clone(),
            )]
        );
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
        let BranchCondition {
            true_branch,
            false_branch,
        } = s.index(cond).to_branch_condition(ctx).expect(&format!("${}, used as a branch condition, is not of boolean type.", cond));
        vec![
            jump(then_label, label_to_offset, s.clone() & true_branch),
            jump(else_label, label_to_offset, s & false_branch),
        ]
    }

    // Handle pure operations.
    // the arity of inputs is checked in `op
    fn pure_local_operation<'ctx, F>(
        dsts: &[TempIndex],
        op: F,
        srcs: &[TempIndex],
        mut s: LocalState<'ctx>,
    ) -> LocalState<'ctx>
    where
        F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
    {
        let constrained_args = s.args(srcs);
        let res = constrained_args.map(op);
        for &x in dsts {
            s.index_mut(x).del();
        }
        for Constrained { content: vals, constraint} in res {
            debug_assert!(vals.len() == dsts.len());
            for (&x, val) in dsts.iter().zip(vals.into_iter()) {
                s.index_mut(x)
                    .content.0
                    .push(ConstrainedValue::new(val.simplify(), constraint.clone()))
            }
        }
        s
    }

    fn pure_local_operation_<'ctx, F>(
        dsts: &[TempIndex],
        op: F,
        srcs: &[TempIndex],
        s: LocalState<'ctx>,
        t: GlobalState<'ctx>
    ) -> Vec<(LocalState<'ctx>, GlobalState<'ctx>)>
    where
        F: Fn(Vec<Value<'ctx>>) -> Vec<Value<'ctx>> + Clone,
    {
        vec![(pure_local_operation(dsts, op, srcs, s), t)]
    }

    fn operation<'ctx, 'env>(
        dsts: &[TempIndex],
        op: &Operation,
        srcs: &[TempIndex],
        _on_abort: Option<&AbortAction>,
        mut s: LocalState<'ctx>,
        mut t: GlobalState<'ctx>,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) -> Vec<(LocalState<'ctx>, GlobalState<'ctx>)> {
        use Operation::*;
        s.ic += 1;
        match op {
            // Pack(ModuleId, StructId, Vec<Type>),
            Pack(module_id, struct_id, type_params) => {
                pure_local_operation_(
                    dsts,
                    |x: Vec<Value>| {
                        let resource_type = QualifiedInstId {
                            module_id: *module_id,
                            inst: type_params.clone(),
                            id: *struct_id,
                        };
                        let mut dt = datatypes.borrow_mut();
                        let struct_type = dt.from_struct(&resource_type);
                        vec![
                            Value::Struct(struct_type.variants[0]
                                .constructor
                                .apply(
                                    x.iter()
                                        .map(|x| x.unwrap())
                                        .collect::<Vec<&dyn Ast>>()
                                        .as_slice(),
                                )
                                .as_datatype()
                                .unwrap()
                                .simplify())
                        ]
                    },
                    srcs,
                    s,
                    t,
                )
            }
            // Unpack(ModuleId, StructId, Vec<Type>),
            Unpack(module_id, struct_id, type_params) => {
                pure_local_operation_(
                    dsts,
                    |x: Vec<Value>| {
                        let resource_type = QualifiedInstId {
                            module_id: *module_id,
                            inst: type_params.clone(),
                            id: *struct_id,
                        };
                        let field_types = datatypes.borrow().get_field_types(*module_id, *struct_id);
                        let mut dt = datatypes.borrow_mut();
                        let struct_sort = dt.from_struct(&resource_type);
                        struct_sort
                            .variants[0]
                            .accessors
                            .iter()
                            .zip(field_types.iter())
                            .map(|(f, t)| Value::wrap(&f.apply(&[x[0].unwrap()]).simplify(), &t))
                            .collect()
                    },
                    srcs,
                    s,
                    t,
                )
            }

            // Resources
            MoveTo(module_id, struct_id, type_params) => {
                let addr_val = s[srcs[0]].content.clone();
                let resource_type = QualifiedInstId { module_id: *module_id, inst: type_params.clone(), id: *struct_id };
                let branch_condition = t.exists(&resource_type, &addr_val).to_branch_condition(s.get_ctx());
                let mut true_branch_local_state = s.clone() & branch_condition.true_branch.clone();
                true_branch_local_state.ts = TerminationStatus::Abort(Disjoints(vec![]));
                let true_branch_global_state = t.clone() & branch_condition.true_branch;
                let false_branch_local_state = s & branch_condition.false_branch.clone();
                let mut false_branch_global_state = t.clone() & branch_condition.false_branch;
                false_branch_global_state.real_move_to(&resource_type,
                    &false_branch_local_state[srcs[0]].content.clone().map(|x| x.as_addr().unwrap().clone()),
                    false_branch_local_state[srcs[1]].content.clone().map(|x| x.as_datatype().unwrap().clone()),
                    datatypes
                );
                vec![(true_branch_local_state, true_branch_global_state), (false_branch_local_state, false_branch_global_state)]
            }
            MoveFrom(module_id, struct_id, type_params) => {
                let addr_val = s[srcs[0]].content.clone();
                let resource_id = new_resource_id(*module_id, *struct_id, type_params.clone());
                let branch_condition = t.exists(&resource_id, &addr_val).to_branch_condition(s.get_ctx());
                let mut true_branch_local_state = s.clone() & branch_condition.true_branch.clone();
                let mut true_branch_global_state = t.clone() & branch_condition.true_branch;
                let resource_moved_out = true_branch_global_state.real_move_from(&resource_id,
                    &true_branch_local_state[srcs[0]].content.clone().map(|x| x.as_addr().unwrap().clone()),
                    datatypes
                );
                true_branch_local_state[dsts[0]].content = resource_moved_out.map(
                    |x| Value::Struct(x.as_datatype().unwrap())
                );
                let mut false_branch_local_state = s & branch_condition.false_branch.clone();
                false_branch_local_state.ts = TerminationStatus::Abort(Disjoints(vec![]));
                let false_branch_global_state = t.clone() & branch_condition.false_branch;
                vec![(true_branch_local_state, true_branch_global_state), (false_branch_local_state, false_branch_global_state)]
            }
            Exists(module_id, struct_id, type_params) => {
                let dst = dsts[0];
                let src = srcs[0];
                let src_val = s[src]
                    .content
                    .clone();
                let resource_type = QualifiedInstId {
                    module_id: *module_id,
                    inst: type_params.clone(),
                    id: *struct_id,
                };
                s[dst].content = t
                    .exists(&resource_type, &src_val)
                    .map(|x| Value::Primitive(PrimitiveValue::Bool(x)));
                vec![(s, t)]
            }

            // Unary
            // CastU8 => todo!
            // CastU64 => todo!
            // CastU128 => todo!
            Not => pure_local_operation_(
                dsts,
                |x: Vec<Value>| {
                    assert_eq!(x.len(), 1);
                    vec![!x.index(0)]
                },
                srcs,
                s,
                t,
            ),
            // Binary
            Add => pure_local_operation_(
                dsts,
                |x: Vec<Value>| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) + x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            Sub => pure_local_operation_(
                dsts,
                |x: Vec<Value>| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) - x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            Mul => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) * x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            Div => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) / x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            Mod => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) % x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            BitOr => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) | x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            BitAnd => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) & x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            Xor => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x.index(0) ^ x.index(1)]
                },
                srcs,
                s,
                t,
            ),
            // Shl,
            // Shr,
            Lt => pure_local_operation_(
                dsts,
                |x| {
                    println!("fjdkf");
                    assert_eq!(x.len(), 2);
                    vec![x[0].lt(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            Gt => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].gt(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            Le => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].le(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            Ge => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].ge(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            Or => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].or(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            And => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].and(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            Eq => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].eq(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            Neq => pure_local_operation_(
                dsts,
                |x| {
                    assert_eq!(x.len(), 2);
                    vec![x[0].neq(&x[1])]
                },
                srcs,
                s,
                t,
            ),
            // CastU256,
            _ => vec![(s, t)],
        }
    }

    pub fn step<'ctx, 'env>(
        mut s: MoveState<'ctx, 'env>,
        instr: &Bytecode,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) -> Vec<MoveState<'ctx, 'env>> {
        match instr {
            Bytecode::Assign(_, dst, src, kind) => vec![MoveState {
                local_state: assign(*dst, *src, kind, s.local_state),
                ..s
            }],
            Bytecode::Call(_, dsts, op, srcs, on_abort) => {
                let res = operation(
                    dsts,
                    op,
                    srcs,
                    on_abort.as_ref(),
                    s.local_state.clone(),
                    s.global_state.clone(),
                    datatypes
                );
                res.into_iter().map(
                    |(local_state, global_state)|
                        MoveState {
                            local_state,
                            global_state,
                            ..s.clone()
                        }
                ).collect()
            }
            Bytecode::Ret(_, srcs) => vec![{
                s.local_state.ts = TerminationStatus::Return(
                    srcs.iter()
                        .map(|&x| s.local_state[x].content.clone())
                        .collect(),
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
            }
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
        let datatypes = self.datatypes.clone();
        eval::step(self, &instr, datatypes)
    }

    fn is_final(&self) -> bool {
        self.get_local_state().ic() >= self.bytecodes.len() as u16
            || self.get_local_state().termination_status().is_final()
    }
}

impl<'ctx, 'env> MoveState<'ctx, 'env> {
    fn generate_offset_to_block_id(bytecodes: &[Bytecode]) -> BTreeMap<CodeOffset, BlockId> {
        let mut offset_to_block_id = BTreeMap::new();
        let cfg = StacklessControlFlowGraph::new_forward(bytecodes);
        let sorted_block_id = topo_sort(&cfg);
        for i in 0..cfg.num_blocks() {
            match cfg.content(sorted_block_id[i as usize]) {
                BlockContent::Basic { lower, upper } => {
                    for code_offset in *lower..*upper + 1 {
                        offset_to_block_id.insert(code_offset, i);
                    }
                }
                BlockContent::Dummy => (),
            }
        }
        offset_to_block_id
    }
}

impl<'ctx, 'env> MoveState<'ctx, 'env> {
    pub fn new_default(ctx: &'ctx Context, function_target: FunctionTarget<'env>) -> Self {
        let global_env = function_target.func_env.module_env.env;
        let datatypes = Rc::new(RefCell::new(Datatypes::new(ctx, global_env)));
        Self {
            label_to_offset: Bytecode::label_offsets(function_target.data.code.as_slice()),
            offset_to_block_id: Self::generate_offset_to_block_id(
                function_target.data.code.as_slice(),
            ),
            bytecodes: function_target.data.code.as_slice(),
            local_state: LocalState::new_default(ctx, {
                let mut locals: Vec<Local<'ctx>> = Vec::new();
                let symbol_pool = function_target.symbol_pool();
                for local_index in 0..function_target.get_local_count() {
                    let local_symbol = function_target.get_local_name(local_index);
                    let local_name: String = symbol_pool.string(local_symbol).to_string();
                    let local_type = function_target.get_local_type(local_index);
                    locals.push(if local_index < function_target.get_parameter_count() {
                        Local::from_type(local_name, &local_type, ctx, datatypes.clone())
                    } else {
                        Local::new()
                    });
                }
                locals
            }),
            global_state: GlobalState::new_empty(ctx),
            function_target,
            // datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
            datatypes: datatypes
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

    pub fn get_local_state(&self) -> &LocalState<'ctx> {
        &self.local_state
    }

    // return the instruction to be executed
    // panics if the ic is invalid
    fn cur_instr(&self) -> &Bytecode {
        self.bytecodes
            .get(self.get_local_state().ic() as usize)
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

// Utilities
use move_stackless_bytecode::stackless_control_flow_graph::{
    BlockContent, StacklessControlFlowGraph,
};
fn topo_sort(cfg: &StacklessControlFlowGraph) -> Vec<BlockId> {
    fn visit(
        s: BlockId,
        visited: &mut Vec<bool>,
        res: &mut Vec<BlockId>,
        cfg: &StacklessControlFlowGraph,
    ) {
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