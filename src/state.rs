//! # Evaluation State
use crate::{value::{
    ConstrainedValue,
    PrimitiveValue, Value,
}, constraint::{Constrained, Constraint, OrderedConstraint},
    ty::{Type, Datatypes, ResourceId, type_of_constant}, symbolic_tree::SymbolicTree, };
use move_stackless_bytecode::{
    stackless_bytecode::{Constant},
};
use std::{fmt, cell::{RefCell}, ops::BitAndAssign};
use std::ops::{BitAnd, BitOr};
use std::{
    collections::{BTreeMap},
    rc::Rc,
};
use z3::{
    ast::{Array, Bool, Datatype, BV, Dynamic},
    Context, Sort, Symbol,
};

pub type CodeOffset = u16;
pub type TempIndex = usize;
pub type BlockId = CodeOffset;
pub type Values<'ctx> = SymbolicTree<OrderedConstraint<'ctx>, Value<'ctx>>;

pub mod termination;
pub mod local;
pub mod global;

pub use termination::{
    TerminationStatus
};
pub use local::{
    Local,
    LocalMemory
};
pub use global::{
    GlobalMemory
};

#[derive(Clone)]
pub struct EvalState<'ctx> {
    pub(crate) context: &'ctx Context,
    pub path_constraint: Bool<'ctx>,
    pub termination_status: TerminationStatus<'ctx>,
    pub local_memory: LocalMemory<'ctx>,
    pub global_memory: GlobalMemory<'ctx>
}