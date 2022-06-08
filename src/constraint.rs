use std::{ops::{BitAnd, BitAndAssign}, fmt::{Display, self}, iter::FromIterator};

use itertools::iproduct;
use z3::{ast::{Bool, Ast}, Solver, SatResult, Context};

use crate::{value::Value, state::BranchCondition};

/// Boolean sort
pub type Constraint<'ctx> = Bool<'ctx>;

/// Return false if the constraint is unsatisfiable.
pub fn sat<'ctx>(constraint: &Constraint<'ctx>) -> bool {
  let solver = Solver::new(constraint.get_ctx());
  solver.assert(constraint);
  match solver.check() {
    SatResult::Unsat => false,
    _ => true,
  }
}

/// Return `None` if the constraint is unsatisfiable, else the wrapped value.
pub fn constraint_filter<'ctx>(constraint: Constraint<'ctx>) -> Option<Constraint<'ctx>> {
  if sat(&constraint) {
    Some(constraint)
  } else {
    None
  }
}

// The (_, Constrained) functor
pub struct Constrained<'ctx, T> {
  pub content: T,
  pub constraint: Constraint<'ctx>,
}

impl<'ctx> Constrained<'ctx, ()> {
  pub fn unit(ctx: &'ctx Context) -> Self {
    Self {
      content: (),
      constraint: Bool::from_bool(ctx, true),
    }
  }
}

impl<'ctx, T> Constrained<'ctx, T> {
  pub fn new(content: T, constraint: Constraint<'ctx>) -> Self {
    Self { content, constraint }
  }

  /// Apply f lifted.
  pub fn map<U, F>(self, f: F) -> Constrained<'ctx, U>
  where F: Fn(T) -> U
  {
    Constrained { content: f(self.content), constraint: self.constraint }
  }

  /// (x, p) * (y, q) => ((x, y), p & q)
  pub fn prod<U>(self, other: Constrained<'ctx, U>) -> Constrained<'ctx, (T, U)> {
    Constrained { content: (self.content, other.content), constraint: self.constraint & other.constraint }
  }

  /// Return the value constrained by true.
  pub fn pure(x: T, ctx: &'ctx Context) -> Self {
    // Constrained::unit(ctx).map(|_| x)
    Self {
      content: x,
      constraint: Bool::from_bool(ctx, true),
    }
  }

  /// Simplify the constraint.
  pub fn simplify(self) -> Self {
    Self {
      constraint: self.constraint.simplify(),
      ..self
    }
  }

  /// Return none if the constraint is unsatisfiable.
  pub fn filter(self) -> Option<Self> {
    if sat(&self.constraint) {
      Some(self)
    } else {
      None
    }
  }

  /// (x, p) => pred(x) & p
  pub fn pred<F>(self, pred: F) -> Constraint<'ctx>
  where F: Fn(T) -> Constraint<'ctx>
  {
    self.map(pred).to_constraint()
  }
}

pub fn map2_constrained<'ctx, A, B, T, F>(f: F, arg: (Constrained<'ctx, A>, Constrained<'ctx, B>)) -> Constrained<'ctx, T>
  where F: Fn((A, B)) -> T 
{
  let arg = arg.0.prod(arg.1);
  arg.map(f)
}

impl<'ctx, T> Constrained<'ctx, Vec<T>> {
  pub fn mappend(mut self, mut other: Self) -> Self {
    self.content.append(&mut other.content);
    self.constraint = self.constraint & other.constraint;
    self
  }
}

impl<'ctx, T: Clone> Clone for Constrained<'ctx, T> {
  fn clone(&self) -> Self {
    Self {
      content: self.content.clone(),
      constraint: self.constraint.clone(),
    }
  }
}

impl<'ctx, T: Eq> Constrained<'ctx, T> {
  /// Return a single merged value if `self` and `other` have identical values,
  /// otherwise a `Vec` of `self` and `other`.
  pub fn merge(self, other: Self) -> Vec<Self> {
    if self.content == other.content {
      vec![
        Self {
          content: self.content,
          constraint: (self.constraint | other.constraint).simplify(),
        }  
      ]
    } else {
      vec![self, other]
    }
  }
}

/// Impose another constraint.
impl<'ctx, T> BitAnd<Bool<'ctx>> for Constrained<'ctx, T> {
  type Output = Self;

  fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
    Constrained {
      constraint: self.constraint & rhs,
      ..self
    }
  }
}

impl<'ctx, T> BitAnd<&Bool<'ctx>> for Constrained<'ctx, T> {
  type Output = Self;

  fn bitand(self, rhs: &Bool<'ctx>) -> Self::Output {
    Constrained {
      constraint: self.constraint & rhs,
      ..self
    }
  }
}

impl<'ctx, T: Clone> BitAnd<Bool<'ctx>> for &Constrained<'ctx, T> {
  type Output = Constrained<'ctx, T>;

  fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
    Constrained {
      constraint: &self.constraint & rhs,
      content: self.content.clone(),
    }
  }
}

impl<'ctx, T: Clone> BitAnd<&Bool<'ctx>> for &Constrained<'ctx, T> {
  type Output = Constrained<'ctx, T>;

  fn bitand(self, rhs: &Bool<'ctx>) -> Self::Output {
    Constrained {
      constraint: &self.constraint & rhs,
      content: self.content.clone(),
    }
  }
}

impl<'ctx, T> BitAndAssign<Bool<'ctx>> for Constrained<'ctx, T> {
  fn bitand_assign(&mut self, rhs: Bool<'ctx>) {
   self.constraint &= rhs;   
  }
}

impl<'ctx, T> BitAndAssign<&Bool<'ctx>> for Constrained<'ctx, T> {
  fn bitand_assign(&mut self, rhs: &Bool<'ctx>) {
   self.constraint &= rhs;   
  }
}

impl<'ctx, T: PartialEq> PartialEq for Constrained<'ctx, T>
{
    fn eq(&self, other: &Self) -> bool {
      self.content == other.content && self.constraint == other.constraint
    }
}

impl<'ctx, T: Display> Display for Constrained<'ctx, T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({} ↩ {})", self.content, self.constraint)
  }
}

/// Collection of mutually exclusive constrained values.
pub struct Disjoints<'ctx, T>(pub Vec<Constrained<'ctx, T>>);

impl<'ctx> Disjoints<'ctx, Constraint<'ctx>> {
  /// (p, q) ... => (p & q) | ...
  pub fn to_constraint(&self, ctx: &'ctx Context) -> Constraint<'ctx> {
    self.iter().filter_map(|x| x.to_constraint_opt().map(|x| x.simplify())).fold(Bool::from_bool(ctx, false), |acc, x| acc | x)
  }

  /// Convert a constrained boolean to a branch condition.
  pub fn to_branch_condition(&self, ctx: &'ctx Context) -> BranchCondition<'ctx> {
    let mut acc = BranchCondition::or_id(ctx);
    for cv in &self.0 {
      let bc = cv.to_branch_condition();
      acc = (acc | bc).simplify();
    }
    acc
  }
}

impl<'ctx> Disjoints<'ctx, Value<'ctx>> {
  pub fn to_branch_condition(&self, ctx: &'ctx Context) -> Option<BranchCondition<'ctx>> {
    let mut acc = BranchCondition::or_id(ctx);
    for cv in &self.0 {
        match cv.to_branch_condition() {
            Some(bc) => acc = (acc | bc).simplify(),
            None => return None
        }
    }
    Some(acc)
  }
}

impl<'ctx, T: Clone> Disjoints<'ctx, Vec<T>> {
  pub fn unit(ctx: &'ctx Context) -> Self {
    Self(vec![Constrained { content: Vec::new(), constraint: Bool::from_bool(ctx, true)}])
  }
  
  /// Lifted vector append
  pub fn mappend(self, other: Self) -> Self {
    Disjoints(
      iproduct!(self.into_iter(), other.into_iter())
      .filter_map(|(x, y)| x.mappend(y).simplify().filter())
      .collect()
    )
  }
}

pub fn fmap2_disjoints<'ctx, A: Clone, B: Clone, C, F>(f: F, args: (&Disjoints<'ctx, A>, &Disjoints<'ctx, B>)) -> Disjoints<'ctx, C> 
  where F: Fn((A, B)) -> C + Clone
{
  let arg = args.0.prod(&args.1);
  arg.map(f)
}

impl<'ctx, T> Disjoints<'ctx, Disjoints<'ctx, T>> {
  pub fn flatten(self) -> Disjoints<'ctx, T> {
    Disjoints(
      self.0.into_iter()
      .map(
        |Constrained { content, constraint }| {
          (content & constraint).0
        }
      )
      .flatten()
      .collect()
    )
  }
}

impl<'ctx, T: Clone> Disjoints<'ctx, T> {
  pub fn from_constrained(x: Constrained<'ctx, T>) -> Self {
    Self(vec![x])
  }

  pub fn map<U, F>(self, f: F) -> Disjoints<'ctx, U>
    where F: Fn(T) -> U + Clone
  {
    self.into_iter().map(|x| x.map(f.clone())).collect()
  }

  pub fn prod<U: Clone>(&self, other: &Disjoints<'ctx, U>) -> Disjoints<'ctx, (T, U)> {
    Disjoints(
      iproduct!(self.iter(), other.iter())
      .filter_map(|(x, y)| x.clone().prod(y.clone()).simplify().filter())
      .collect()
    )
  }

  pub fn iter(&self) -> std::slice::Iter<'_, Constrained<'ctx, T>> {
    self.0.iter()
  }
}

impl<'ctx, T> BitAnd<Bool<'ctx>> for Disjoints<'ctx, T> {
  type Output = Self;

  fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
    self.into_iter().map(|x| x & &rhs).collect()
  }
}

impl<'ctx, T> BitAnd<&Bool<'ctx>> for Disjoints<'ctx, T> {
  type Output = Self;

  fn bitand(self, rhs: &Bool<'ctx>) -> Self::Output {
    self.into_iter().map(|x| x & rhs).collect()
  }
}

impl<'ctx, T> BitAndAssign<Bool<'ctx>> for Disjoints<'ctx, T> {
  fn bitand_assign(&mut self, rhs: Bool<'ctx>) {
      for x in &mut self.0 {
        *x &= &rhs;
      }
  }
}

impl<'ctx, T> BitAndAssign<&Bool<'ctx>> for Disjoints<'ctx, T> {
  fn bitand_assign(&mut self, rhs: &Bool<'ctx>) {
      for x in &mut self.0 {
        *x &= rhs;
      }
  }
}

impl<'ctx, T> IntoIterator for Disjoints<'ctx, T> {
  type Item = Constrained<'ctx, T>;
  type IntoIter = std::vec::IntoIter<Self::Item>;

  fn into_iter(self) -> Self::IntoIter {
      self.0.into_iter()
  }
}

impl<'ctx, T> FromIterator<Constrained<'ctx, T>> for Disjoints<'ctx, T> {
  fn from_iter<I: IntoIterator<Item=Constrained<'ctx, T>>>(iter: I) -> Self {
    Self(iter.into_iter().collect())
  }
}

impl<'ctx, T: Clone> Clone for Disjoints<'ctx, T> {
  fn clone(&self) -> Self {
    Disjoints(self.0.clone())
  }
}

impl<'ctx, T: PartialEq> PartialEq for Disjoints<'ctx, T>
{
    fn eq(&self, other: &Self) -> bool {
      self.0 == other.0
    }
}