use move_stackless_bytecode::stackless_bytecode::{Bytecode as stackless_bytecode, Operation, Constant, AssignKind,};

use crate::state::TempIndex;

/// The structured stackless bytecode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bytecode {
    Load(TempIndex, Constant),
    Assign(TempIndex, TempIndex, AssignKind),
    Call(
        Vec<TempIndex>,
        Operation,
        Vec<TempIndex>,
    ),
    Ret(Vec<TempIndex>),
    If(TempIndex, Vec<Bytecode>, Vec<Bytecode>),
    While(TempIndex, Vec<Bytecode>, Vec<Bytecode>),
    Abort(TempIndex),
    Nop(),
}

impl Bytecode {
    /// Converting from stackless bytecode.
    /// Return `None` for non-compatible bytecodes.
    pub fn from_stackless_bytecode(bytecode: stackless_bytecode) -> Option<Self> {
        use stackless_bytecode::*;
        match bytecode {
            Load(_, dst, c) => Some(Self::Load(dst, c)),
            Assign(_, dst, src, kind) => Some(Self::Assign(src, dst, kind)),
            Call(_, dsts, op, srcs, _) => Some(Self::Call(dsts, op, srcs)),
            Ret(_, temp_index) => Some(Self::Ret(temp_index)),
            Abort(_, temp_index) => Some(Self::Abort(temp_index)),
            Nop(_) => Some(Self::Nop()),
            Branch(_, _, _, _) => None,
            Jump(_, _) => None,
            Label(_, _) => None,
            SaveMem(_, _, _) => None,
            SaveSpecVar(_, _, _) => None,
            Prop(_, _, _) => None,
        }
    }
}