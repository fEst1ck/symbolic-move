//! Traits for the generic symbolic execution algorithm.

/// State transition systems.
pub trait Transition {
  type IntoIter: IntoIterator<Item=Self>;
  fn suc(self) -> Self::IntoIter;
  fn is_final(&self) -> bool;
}

/// Evaluation states equipped with a *similar* relation,
/// and a merge operation.
pub trait State: Eq + Sized {
  /// Merge two similar evaluation states.
  fn merge(self, other: Self) -> Option<Self>;
}

/// Sets of equivalence classes of evaluation states.
pub trait StateSet<T: State> {
  /// Create a empty set.
  fn new() -> Self;
  /// If a state `t` similar to `s` is already in `self`,
  /// then `t` is replaced with the merge of `s` and `t`.
  fn insert(&mut self, s: T);
  fn remove(&mut self, s: &T) -> Option<T>;
  fn is_empty(&self) -> bool;
}