use crate::state::{MoveState, MoveStateSet};
use symbolic_evaluation::evaluation::{eval as sym_eval};

/// Evaluate a move program.
pub fn eval(init_state: MoveState) {
  sym_eval(init_state, |x: &MoveStateSet| x.first(), |x| {
    println!("{:?}", x);
  });
}