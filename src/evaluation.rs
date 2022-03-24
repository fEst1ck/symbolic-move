use crate::state::{MoveState, MoveStateSet};
use symbolic_evaluation::evaluation::{eval as sym_eval};

/// Evaluate a move program.
pub fn eval<'ctx, 'env>(init_state: MoveState<'ctx, 'env>) -> Vec<MoveState<'ctx, 'env>> {
  let mut res: Vec<MoveState<'ctx, 'env>> = Vec::new();
  sym_eval(init_state, |x: &MoveStateSet| x.first(), |x| {
    res.push(x);
  });
  res
}