//! # Symbolic Evaluation
//! 
//! The crate defines a generic symbolic execution algorithm parametrized by
//! 
//! - a transition system, which defines the dynamic of the language;
//! 
//! - a similar relation defined on the states of the transitoin system, and
//! a merge operator defined on similar states, which together defines the
//! merge strategy;
//! 
//! - a `pick_next` method, which defines the search strategy.

pub mod traits;
pub mod evaluation;