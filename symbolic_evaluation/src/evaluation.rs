//! A generic symbolic execution algorithm.

use crate::traits::{State, Transition, StateSet};

pub fn eval<T, S, F, G>(init_state: T, pick_next: F, report: G)
  where 
    T: State + Transition + std::fmt::Debug,
    S: StateSet<T>,
    F: Fn(&S) -> Option<T>,
    G: Fn(T) -> (),
{
  let mut frontier = S::new();
  frontier.insert(init_state);
  while !frontier.is_empty() {
    let state = frontier.remove(&pick_next(&frontier).unwrap()).unwrap();
    for s in state.suc() {
      if s.is_final() {
        report(s);
      } else {
        println!("{:?}", &s);
        frontier.insert(s);
      }
    }
  }
}