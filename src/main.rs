use symbolic_move::state::{MoveState, Local, LocalState, TerminationStatus};
use symbolic_move::value::{Type};
use symbolic_move::evaluation::eval;
use z3::{Solver, SatResult, Context, Config, ast::{Bool, Ast}};
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation, Constant, Label, AssignKind, AttrId};
use std::collections::{BTreeMap, BTreeSet};

fn main() {
  let dummy = AttrId::new(0);
  let codes = vec![
    Bytecode::Load(dummy, 2, Constant::U64(0)),
    Bytecode::Assign(dummy, 3, 0, AssignKind::Copy),
    Bytecode::Call(dummy, vec![4], Operation::Lt, vec![2, 3], None),
    Bytecode::Branch(dummy, Label::new(0), Label::new(1), 4),
    Bytecode::Label(dummy, Label::new(1)), // 4
    Bytecode::Jump(dummy, Label::new(2)),
    Bytecode::Label(dummy, Label::new(0)), // 6
    Bytecode:: Assign(dummy, 5, 0, AssignKind::Copy),
    Bytecode::Assign(dummy, 1, 5, AssignKind::Store),
    Bytecode::Jump(dummy, Label::new(3)),
    Bytecode::Label(dummy, Label::new(2)), // 10
    Bytecode::Load(dummy, 6, Constant::U64(0)),
    Bytecode::Assign(dummy, 1, 6, AssignKind::Copy),
    Bytecode::Jump(dummy, Label::new(3)),
    Bytecode::Label(dummy, Label::new(3)), // 14
    Bytecode::Assign(dummy, 7, 1, AssignKind::Move),
  ];

  let label_to_offset_ = [(Label::new(0), 6), (Label::new(1), 4), (Label::new(2), 10), (Label::new(3), 14)];
  let mut label_to_offset = BTreeMap::new();
  for (label, offset) in label_to_offset_ {
    label_to_offset.insert(label, offset);
  }
  let offset_to_block_id_ = 
  [
    (0, 0), (1, 0), (2, 0), (3, 0),
    (4, 1), (5, 1),
    (10, 2), (11, 2), (12, 2), (13, 2),
    (6, 3), (7, 3), (8, 3), (9, 3),
    (14, 4), (15, 4)
  ];
  let mut offset_to_block_id = BTreeMap::new();
  for (offset, block) in offset_to_block_id_ {
    offset_to_block_id.insert(offset, block);
  }
  let config = Config::new();
  let ctx = Context::new(&config);
  let s = MoveState::new(label_to_offset, offset_to_block_id, codes.as_slice(), LocalState::new(&ctx, 0, Bool::from_bool(&ctx, true), TerminationStatus::None, 
  vec![Local::from_type(&Type::U64, &ctx), Local::new(), Local::new(), Local::new(), Local::new(), Local::new(), Local::new(), Local::new()]));
  eval(s);
}
