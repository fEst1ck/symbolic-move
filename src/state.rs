//! # Evaluation State
use crate::{value::{
    ConstrainedValue,
    PrimitiveValue, Value,
}, constraint::{Constrained, Constraint, sat, Disjoints},
    ty::{Type, Datatypes, ResourceId},
};
use itertools::Itertools;
use move_model::model::{
    FunctionEnv, GlobalEnv,
};
use move_stackless_bytecode::{
    function_target::{FunctionData, FunctionTarget},
    stackless_bytecode::{Bytecode, Label},
};
use std::{fmt, cell::{RefCell}, ops::BitAndAssign};
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
    pub fn is_final(&self) -> bool {
        match self {
            TerminationStatus::None => false,
            _ => true,
        }
    }
}

/// Local variable
#[derive(Clone)]
pub struct Local<'ctx> {
    pub ty: Type,
    pub(crate) content: Disjoints<'ctx, Value<'ctx>>,
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
        Local { content: self.content & rhs, ..self }
    }
}

impl<'ctx> BitAndAssign<Bool<'ctx>> for Local<'ctx> {
    fn bitand_assign(&mut self, rhs: Bool<'ctx>) {
        self.content &= rhs;
    }
}

impl<'ctx> BitAndAssign<&Bool<'ctx>> for Local<'ctx> {
    fn bitand_assign(&mut self, rhs: &Bool<'ctx>) {
        self.content &= rhs;
    }
}

impl<'ctx> BitOr<Local<'ctx>> for Local<'ctx> {
    type Output = Self;

    fn bitor(self, rhs: Local<'ctx>) -> Self {
        self.merge(rhs)
    }
}

impl<'ctx> Local<'ctx> {
    pub fn new(ty: Type) -> Self {
        Self {
            ty,
            content: Disjoints(Vec::new()),
        }
    }

    pub fn simplify(self) -> Self {
        Self {
            content: self.content.into_iter().map(|x| x.simplify()).collect(),
            ..self
        }
    }

    pub fn from_type<'env, S: Into<Symbol>>(x: S, t: &Type, ctx: &'ctx Context, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>) -> Self {
        Self {
            ty: t.clone(),
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
        std::mem::replace(&mut self.content, Disjoints(Vec::new()))
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
                ty: {
                    assert!(self.ty == other.ty);
                    self.ty
                },
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

impl<'ctx> BitAndAssign<Constraint<'ctx>> for LocalState<'ctx> {
    fn bitand_assign(&mut self, rhs: Constraint<'ctx>) {
        let new_pc: Constraint<'ctx> = (&self.pc & &rhs).simplify();
        if !sat(&new_pc) {
            self.ts = TerminationStatus::Unsat;
        }
        self.pc = new_pc;
        for local in &mut self.locals {
            *local &= &rhs;
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

    pub fn merge(self, other: Self) -> Self {
        LocalState {
            pc: (&self.pc | &other.pc).simplify(),
            locals: {
                self
                    .locals
                    .into_iter()
                    .zip(other.locals.into_iter())
                    .map(|(x, y)| (x | y).simplify())
                    .collect()
            },
            ..self
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
    pub ctx: &'ctx Context,
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

    pub fn merge(self, other: Self) -> Self {
        fn merge<'ctx>(x: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>, y: BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>>) -> BTreeMap<ResourceId, Disjoints<'ctx, Array<'ctx>>> {
            let mut res = x;
            for (resource_id, mut disjoints) in y {
                res.entry(resource_id)
                    .and_modify(|x| x.0.append(&mut disjoints.0))
                    .or_insert(disjoints);
            }
            res
        }
        assert!(self.ctx == other.ctx);
        GlobalState { 
            ctx: self.ctx,
            resource_value: merge(self.resource_value, other.resource_value),
            resource_existence: merge(self.resource_existence, other.resource_existence)
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

    pub fn get_resource_value<'env>(
        &mut self,
        resource: &ResourceId,
        datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
    ) -> Disjoints<'ctx, Array<'ctx>> {
        match self.resource_value.get(resource) {
            Some(arrays) => arrays.clone(),
            None => {
                self.init_resource_value(datatypes.clone(), resource);
                self.get_resource_value(resource, datatypes)
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

    pub fn real_move_from_<'env>(
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

impl<'ctx> BitAndAssign<Constraint<'ctx>> for GlobalState<'ctx> {
    fn bitand_assign(&mut self, rhs: Constraint<'ctx>) {
        for (_, v) in self.resource_value.iter_mut() {
            *v &= &rhs;
        }
        for (_, v) in self.resource_existence.iter_mut() {
            *v &= &rhs;
        }
    }
}

/// Move evaluation state
#[derive(Clone)]
pub struct MoveState<'ctx, 'env> {
    pub(crate) function_target: FunctionTarget<'env>,
    pub(crate) label_to_offset: BTreeMap<Label, CodeOffset>,
    pub(crate) offset_to_block_id: BTreeMap<CodeOffset, BlockId>,
    pub(crate) bytecodes: &'env [Bytecode],
    pub(crate) local_state: LocalState<'ctx>,
    pub(crate) global_state: GlobalState<'ctx>,
    pub(crate) datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>
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
                global_state: self.global_state.merge(other.global_state),
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
                        Local::new(local_type.clone())
                    });
                }
                locals
            }),
            global_state: GlobalState::new_empty(ctx),
            function_target,
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
    pub(crate) fn cur_instr(&self) -> &Bytecode {
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