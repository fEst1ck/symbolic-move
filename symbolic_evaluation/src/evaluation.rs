//! A generic symbolic execution algorithm.

use crate::traits::{State, Transition, StateSet};

/// Evaluate from initial state `init_state` using the
/// `pickNext` as the search strategy, report all
/// successing final states.
pub fn eval<T, S, F, G>(init_state: T, pick_next: F, mut report: G)
  where 
    T: State + Transition,
    S: StateSet<T>,
    F: Fn(&S) -> Option<T>,
    G: FnMut(T) -> (),
{
  let mut frontier = S::new();
  frontier.insert(init_state);
  while !frontier.is_empty() {
    let state = frontier.remove(&pick_next(&frontier).unwrap()).unwrap();
    for s in state.suc() {
      if s.is_final() {
        report(s);
      } else {
        frontier.insert(s);
      }
    }
  }
}