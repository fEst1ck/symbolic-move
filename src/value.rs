//! Symolic move values.

use std::ops::{BitAnd, BitOr, BitXor, Add, Mul, Div, Rem};
use z3::{Context, ast::{Bool, BV, Ast}};
use move_stackless_bytecode::{
  stackless_bytecode::{Constant},
};

/// The type of formulae, i.e., terms of boolean sort.
pub type Constraint<'ctx> = Bool<'ctx>;

/// The type of move values.
pub enum Type {
  Bool,
  U8,
  U64,
  U128,
  U256
}

/// Symbolic move values.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value<'ctx> {
  Bool(Bool<'ctx>),
  U8(BV<'ctx>),
  U64(BV<'ctx>),
  U128(BV<'ctx>),
  U256(BV<'ctx>),
  // ...
}

impl<'ctx> Add for Value<'ctx> {
  type Output = Self;
  fn add(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
    (Value::U8(x), Value::U8(y)) => Value::U8(x + y),
    (Value::U64(x), Value::U64(y)) => Value::U64(x + y),
    (Value::U128(x), Value::U128(y)) => Value::U128(x + y),
    (Value::U256(x), Value::U256(y)) => Value::U256(x + y),
    _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Mul for Value<'ctx> {
  type Output = Self;
  fn mul(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
    (Value::U8(x), Value::U8(y)) => Value::U8(x * y),
    (Value::U64(x), Value::U64(y)) => Value::U64(x * y),
    (Value::U128(x), Value::U128(y)) => Value::U128(x * y),
    (Value::U256(x), Value::U256(y)) => Value::U256(x * y),
    _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Div for Value<'ctx> {
  type Output = Self;
  fn div(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
    (Value::U8(x), Value::U8(y)) => Value::U8(x.bvudiv(&y)),
    (Value::U64(x), Value::U64(y)) => Value::U64(x.bvudiv(&y)),
    (Value::U128(x), Value::U128(y)) => Value::U128(x.bvudiv(&y)),
    (Value::U256(x), Value::U256(y)) => Value::U256(x.bvudiv(&y)),
    _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Rem for Value<'ctx> {
  type Output = Self;
  fn rem(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::U8(x.bvurem(&y)),
      (Value::U64(x), Value::U64(y)) => Value::U64(x.bvurem(&y)),
      (Value::U128(x), Value::U128(y)) => Value::U128(x.bvurem(&y)),
      (Value::U256(x), Value::U256(y)) => Value::U256(x.bvurem(&y)),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitOr<Self> for Value<'ctx> {
  type Output = Self;
  fn bitor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::U8(x | y),
      (Value::U64(x), Value::U64(y)) => Value::U64(x | y),
      (Value::U128(x), Value::U128(y)) => Value::U128(x | y),
      (Value::U256(x), Value::U256(y)) => Value::U256(x | y),
      _ => panic!("Type mismatches.")
    }
  }
}

impl<'ctx> BitAnd<Self> for Value<'ctx> {
  type Output = Self;
  fn bitand(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::U8(x & y),
      (Value::U64(x), Value::U64(y)) => Value::U64(x & y),
      (Value::U128(x), Value::U128(y)) => Value::U128(x & y),
      (Value::U256(x), Value::U256(y)) => Value::U256(x & y),
      _ => panic!("Type mismatches.")
    }
  }
}

impl<'ctx> BitXor<Self> for Value<'ctx> {
  type Output = Self;
  fn bitxor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::U8(x ^ y),
      (Value::U64(x), Value::U64(y)) => Value::U64(x ^ y),
      (Value::U128(x), Value::U128(y)) => Value::U128(x ^ y),
      (Value::U256(x), Value::U256(y)) => Value::U256(x ^ y),
      _ => panic!("Type mismatches.")
    }
  }
}

impl<'ctx> Value<'ctx> {
  /// Injection from closed values.
  pub fn from_constant(c: &Constant, context: &'ctx Context) -> Self {
    match c {
      Constant::Bool(b) => Value::Bool(Bool::from_bool(context, *b)),
      Constant::U8(x) => Value::U8(BV::from_u64(context, *x as u64, 8)),
      Constant::U64(x) => Value::U64(BV::from_u64(context, *x as u64, 64)),
      _ => todo!(),
    }
  }

  /// Construct a fresh value of type `t`.
  pub fn from_type(t: &Type, context: &'ctx Context) -> Self {
    match t {
      Type::Bool => Value::Bool(Bool::fresh_const(context, "")),
      Type::U8 => Value::U8(BV::fresh_const(context, "", 8)),
      Type::U64 => Value::U64(BV::fresh_const(context, "", 64)),
      Type::U128 => Value::U128(BV::fresh_const(context, "", 128)),
      Type::U256 => Value::U256(BV::fresh_const(context, "", 256)),
    }
  }

  pub fn lt(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::Bool(x.bvult(&y)),
      (Value::U64(x), Value::U64(y)) => Value::Bool(x.bvult(&y)),
      (Value::U128(x), Value::U128(y)) => Value::Bool(x.bvult(&y)),
      (Value::U256(x), Value::U256(y)) => Value::Bool(x.bvult(&y)),
      _ => panic!("Type mismatches."),
      }
  }

  pub fn le(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::Bool(x.bvule(&y)),
      (Value::U64(x), Value::U64(y)) => Value::Bool(x.bvule(&y)),
      (Value::U128(x), Value::U128(y)) => Value::Bool(x.bvule(&y)),
      (Value::U256(x), Value::U256(y)) => Value::Bool(x.bvule(&y)),
      _ => panic!("Type mismatches."),
      }
  }

  pub fn gt(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::Bool(x.bvugt(&y)),
      (Value::U64(x), Value::U64(y)) => Value::Bool(x.bvugt(&y)),
      (Value::U128(x), Value::U128(y)) => Value::Bool(x.bvugt(&y)),
      (Value::U256(x), Value::U256(y)) => Value::Bool(x.bvugt(&y)),
      _ => panic!("Type mismatches."),
      }
  }

  pub fn ge(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::U8(x), Value::U8(y)) => Value::Bool(x.bvuge(&y)),
      (Value::U64(x), Value::U64(y)) => Value::Bool(x.bvuge(&y)),
      (Value::U128(x), Value::U128(y)) => Value::Bool(x.bvuge(&y)),
      (Value::U256(x), Value::U256(y)) => Value::Bool(x.bvuge(&y)),
      _ => panic!("Type mismatches."),
      }
  }

  pub fn and(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::Bool(x), Value::Bool(y)) => Value::Bool(x & y),
      _ => panic!("Type mismatches."),
    }
  }

  pub fn or(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::Bool(x), Value::Bool(y)) => Value::Bool(x | y),
      _ => panic!("Type mismatches."),
    }
  }

  pub fn eq(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::Bool(x), Value::Bool(y)) => Value::Bool(x._eq(&y)),
      (Value::U8(x), Value::U8(y)) => Value::Bool(x._eq(&y)),
      (Value::U64(x), Value::U64(y)) => Value::Bool(x._eq(&y)),
      (Value::U128(x), Value::U128(y)) => Value::Bool(x._eq(&y)),
      (Value::U256(x), Value::U256(y)) => Value::Bool(x._eq(&y)),
      _ => panic!("Type mismatches."),
    }
  }

  pub fn neq(self, rhs: Self) -> Self {
    match (self, rhs) {
      (Value::Bool(x), Value::Bool(y)) => Value::Bool(!x._eq(&y)),
      (Value::U8(x), Value::U8(y)) => Value::Bool(!x._eq(&y)),
      (Value::U64(x), Value::U64(y)) => Value::Bool(!x._eq(&y)),
      (Value::U128(x), Value::U128(y)) => Value::Bool(!x._eq(&y)),
      (Value::U256(x), Value::U256(y)) => Value::Bool(!x._eq(&y)),
      _ => panic!("Type mismatches."),
    }
  }
}

/// The product of `Value` and `Constraint`.
#[derive(Clone, Debug)]
pub struct ConstrainedValue<'ctx> {
  value: Value<'ctx>,
  constraint: Constraint<'ctx>,
}

use std::fmt;
impl<'ctx> fmt::Display for ConstrainedValue<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      write!(f, "({:?}, {:?})", self.value, self.constraint)
  }
}

/// Impose another constraint.
impl<'ctx> BitAnd<Bool<'ctx>> for ConstrainedValue<'ctx> {
  type Output = Self;

  fn bitand(self, rhs: Bool<'ctx>) -> Self::Output {
    ConstrainedValue {
      constraint: self.constraint & rhs,
      ..self
    }
  }
}

impl<'ctx> ConstrainedValue<'ctx> {
  pub fn new(value: Value<'ctx>, constraint: Constraint<'ctx>) -> Self {
    Self { value, constraint }
  }

  /// Simplify the constraint.
  pub fn simplify(self) -> Self {
    Self {
      constraint: self.constraint.simplify(),
      ..self
    }
  }

  /// Construct a new symbolic value of type `t` constrained by true.
  pub fn from_type(t: &Type, context: &'ctx Context) -> Self {
    Self { value: Value::from_type(t, context), constraint: Bool::from_bool(context, true) }
  }

  pub fn decompose(self) -> (Value<'ctx>, Constraint<'ctx>) {
    (self.value, self.constraint)
  }

  /// Turn a constrained boolean value to a constraint,
  /// which is the conjunction of the value and the constraint.
  pub fn to_constraint(self) -> Constraint<'ctx> {
    match self {
      ConstrainedValue { value: Value::Bool(b), constraint } => b & constraint,
      _ => panic!("Only values of boolean sort can be turned into a constraint."),
    }
  }

  /// Return a single merged value if `self` and `other` have identical values,
  /// otherwise a union of `self` and `other`.
  pub fn merge(self, other: Self) -> Vec<Self> {
    if self.value == other.value {
      vec![Self::new(self.value, (self.constraint | other.constraint).simplify())]
    } else {
      vec![self, other]
    }
  }
}

