//! Symolic move values.

use move_core_types::account_address::AccountAddress;
use move_model::model::{ModuleId, StructId};
pub use move_model::ty::{PrimitiveType, Type};
use move_stackless_bytecode::stackless_bytecode::Constant;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Not, Rem};
use z3::{
  Context,
  ast::{Ast, Bool, Dynamic, BV, Datatype},
  DatatypeAccessor, DatatypeBuilder, Sort, Symbol, FuncDecl
};

/// Construct a z3 sort from a move type.
pub fn type_to_sort<'ctx>(t: &Type, ctx: &'ctx Context) -> Sort<'ctx> {
  match t {
    Type::Primitive(t) => match t {
      PrimitiveType::Bool => Sort::bool(ctx),
      PrimitiveType::U8 => Sort::bitvector(ctx, 8),
      PrimitiveType::U64 => Sort::bitvector(ctx, 64),
      PrimitiveType::U128 => Sort::bitvector(ctx, 8),
      PrimitiveType::Address => Sort::bitvector(ctx, PrimitiveValue::LENGTH),
      PrimitiveType::Signer => Sort::bitvector(ctx, PrimitiveValue::LENGTH),
    },
    // tuple
    // vector
    Type::Struct(mod_id, struct_id, types) => {
      let data_type = DatatypeBuilder::new(ctx, format!("{:?}::{:?}", mod_id, struct_id))
        .variant(
          "",
          (0..types.len())
            .zip(types.iter())
            .map(|(i, t)| {
              (
                &i.to_string()[..],
                DatatypeAccessor::Sort(type_to_sort(t, ctx)),
              )
            })
            .collect(),
        )
        .finish();
      data_type.sort
    }
    Type::TypeParameter(id) => Sort::uninterpreted(ctx, Symbol::from(*id as u32)),
    _ => todo!(),
  }
}

/// The type of formulae, i.e., terms of boolean sort.
pub type Constraint<'ctx> = Bool<'ctx>;

/// Primitive values.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PrimitiveValue<'ctx> {
  Bool(Bool<'ctx>),
  U8(BV<'ctx>),
  U64(BV<'ctx>),
  U128(BV<'ctx>),
  Address(BV<'ctx>),
  Signer(BV<'ctx>),
}

impl<'ctx> PrimitiveValue<'ctx> {
  pub const LENGTH: u32 = 8 * AccountAddress::LENGTH as u32;

  /// Construct a constant symbolic value with the given primitive type and name.
  pub fn new_const<S: Into<Symbol>>(x: S, t: &PrimitiveType, ctx: &'ctx Context) -> Self {
    match t {
      PrimitiveType::Bool => PrimitiveValue::Bool(Bool::new_const(ctx, x)),
      PrimitiveType::U8 => PrimitiveValue::U8(BV::new_const(ctx, x, 8)),
      PrimitiveType::U64 => PrimitiveValue::U64(BV::new_const(ctx, x, 64)),
      PrimitiveType::U128 => PrimitiveValue::U128(BV::new_const(ctx, x, 128)),
      PrimitiveType::Address => PrimitiveValue::Address(BV::new_const(ctx, x, Self::LENGTH)),
      PrimitiveType::Signer => PrimitiveValue::Signer(BV::new_const(ctx, x, Self::LENGTH)),
      _ => unreachable!(),
    }
  }

  /// Injection from `Constant`.
  pub fn from_constant(c: &Constant, ctx: &'ctx Context) -> Self {
    match c {
      Constant::Bool(b) => PrimitiveValue::Bool(Bool::from_bool(ctx, *b)),
      Constant::U8(x) => PrimitiveValue::U8(BV::from_u64(ctx, *x as u64, 8)),
      Constant::U64(x) => PrimitiveValue::U64(BV::from_u64(ctx, *x as u64, 64)),
      Constant::U128(x) => PrimitiveValue::U128(
        BV::from_u64(ctx, (*x >> 64) as u64, 64).concat(&BV::from_u64(ctx, *x as u64, 64)),
      ),
      Constant::Address(addr) => PrimitiveValue::Address({
        let mut res = addr
          .iter_u64_digits()
          .fold(BV::from_u64(ctx, 0, 1), |acc, x| {
            BV::from_u64(ctx, x, 64).concat(&acc)
          });
        res = res.extract(res.get_size() - 1, 1);
        res.zero_ext(Self::LENGTH - res.get_size())
      }),
      // U256, Bytearray
      _ => unimplemented!(),
    }
  }

  /// Arithmetic less than.
  pub fn lt(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::Bool(x.bvult(y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::Bool(x.bvult(y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::Bool(x.bvult(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Arithmetic less or equal.
  pub fn le(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::Bool(x.bvule(y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::Bool(x.bvule(y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::Bool(x.bvule(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Arithmetic greater.
  pub fn gt(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::Bool(x.bvugt(y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::Bool(x.bvugt(y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::Bool(x.bvugt(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Arithmetic greater of equal.
  pub fn ge(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::Bool(x.bvuge(y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::Bool(x.bvuge(y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::Bool(x.bvuge(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Logical and.
  pub fn and(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (PrimitiveValue::Bool(x), PrimitiveValue::Bool(y)) => PrimitiveValue::Bool(x & y),
      _ => panic!("Type mismatches."),
    }
  }

  /// Logical or.
  pub fn or(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (PrimitiveValue::Bool(x), PrimitiveValue::Bool(y)) => PrimitiveValue::Bool(x | y),
      _ => panic!("Type mismatches."),
    }
  }

  /// Equality comparison.
  pub fn eq(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (PrimitiveValue::Bool(x), PrimitiveValue::Bool(y)) => PrimitiveValue::Bool(x._eq(y)),
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::Bool(x._eq(y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::Bool(x._eq(y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::Bool(x._eq(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Nonequality comparison.
  pub fn neq(&self, rhs: &Self) -> Self {
    !self.eq(rhs)
  }
}

impl<'ctx> Add for PrimitiveValue<'ctx> {
  type Output = Self;
  fn add(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x + y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x + y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x + y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Add for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn add(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x + y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x + y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x + y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Mul for PrimitiveValue<'ctx> {
  type Output = Self;
  fn mul(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x * y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x * y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x * y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Mul for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn mul(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x * y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x * y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x * y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Div for PrimitiveValue<'ctx> {
  type Output = Self;
  fn div(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x.bvudiv(&y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x.bvudiv(&y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x.bvudiv(&y)),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Div for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn div(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x.bvudiv(&y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x.bvudiv(&y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x.bvudiv(&y)),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Rem for PrimitiveValue<'ctx> {
  type Output = Self;
  fn rem(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x.bvurem(&y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x.bvurem(&y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x.bvurem(&y)),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Rem for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn rem(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x.bvurem(&y)),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x.bvurem(&y)),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x.bvurem(&y)),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitOr<Self> for PrimitiveValue<'ctx> {
  type Output = Self;
  fn bitor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x | y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x | y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x | y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitOr<Self> for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn bitor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x | y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x | y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x | y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitAnd<Self> for PrimitiveValue<'ctx> {
  type Output = Self;
  fn bitand(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x & y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x & y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x & y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitAnd<Self> for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn bitand(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x & y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x & y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x & y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitXor<Self> for PrimitiveValue<'ctx> {
  type Output = Self;
  fn bitxor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x ^ y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x ^ y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x ^ y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitXor<Self> for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn bitxor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x ^ y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x ^ y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x ^ y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Not for PrimitiveValue<'ctx> {
  type Output = Self;

  fn not(self) -> Self::Output {
    match self {
      PrimitiveValue::Bool(b) => PrimitiveValue::Bool(!b),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Not for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;

  fn not(self) -> Self::Output {
    match self {
      PrimitiveValue::Bool(b) => PrimitiveValue::Bool(!b),
      _ => panic!("Type mismatches."),
    }
  }
}

/// Symbolic move values.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value<'ctx> {
  Primitive(PrimitiveValue<'ctx>),
  Struct(Datatype<'ctx>),
  TypeParameter(Dynamic<'ctx>),
}

impl<'ctx> Add for Value<'ctx> {
  type Output = Self;
  fn add(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x + y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Add for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn add(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x + y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Mul for Value<'ctx> {
  type Output = Self;
  fn mul(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x * y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Mul for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn mul(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x * y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Div for Value<'ctx> {
  type Output = Self;
  fn div(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x / y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Div for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn div(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x / y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Rem for Value<'ctx> {
  type Output = Self;
  fn rem(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x % y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Rem for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn rem(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x % y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitOr<Self> for Value<'ctx> {
  type Output = Self;
  fn bitor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x | y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitOr<Self> for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn bitor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x | y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitAnd<Self> for Value<'ctx> {
  type Output = Self;
  fn bitand(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x & y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitAnd<Self> for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn bitand(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x & y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitXor<Self> for Value<'ctx> {
  type Output = Self;
  fn bitxor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x ^ y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> BitXor<Self> for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn bitxor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x ^ y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Not for Value<'ctx> {
  type Output = Self;

  fn not(self) -> Self::Output {
    match self {
      Value::Primitive(b) => Value::Primitive(!b),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Not for &Value<'ctx> {
  type Output = Value<'ctx>;

  fn not(self) -> Self::Output {
    match self {
      Value::Primitive(b) => Value::Primitive(!b),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Value<'ctx> {
  /// Injection from closed values.
  pub fn from_constant(c: &Constant, ctx: &'ctx Context) -> Self {
    Value::Primitive(PrimitiveValue::from_constant(c, ctx))
  }

  /// Construct a new symbolic constant with the given type and name.
  pub fn new_const<S: Into<Symbol>>(x: S, t: &Type, ctx: &'ctx Context) -> Self {
    match t {
      Type::Primitive(t) => Value::Primitive(PrimitiveValue::new_const(x, t, ctx)),
      // Tuple
      // Vector
      Type::Struct(mod_id, struct_id, types) => {
        let data_type = DatatypeBuilder::new(ctx, format!("{:?}::{:?}", mod_id, struct_id))
          .variant(
            "",
            (0..types.len())
              .zip(types.iter())
              .map(|(i, t)| {
                (
                  &i.to_string()[..],
                  DatatypeAccessor::Sort(type_to_sort(t, ctx)),
                )
              })
              .collect(),
          )
          .finish();
        Value::Struct(Datatype::new_const(&ctx, x, &data_type.sort))
      }
      Type::TypeParameter(x) =>
        Value::TypeParameter(FuncDecl::new(ctx, *x as u32, &[], &type_to_sort(t, ctx)).apply(&[])),
      _ => unimplemented!(),
    }
  }

  /// Arithmetic less than.
  pub fn lt(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x.lt(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Arithmetic less or equal.
  pub fn le(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x.le(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Arithmetic greater than.
  pub fn gt(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x.gt(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Arithmetic greater of equal.
  pub fn ge(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x.ge(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Logical and.
  pub fn and(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x.and(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Logical or.
  pub fn or(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x.or(y)),
      _ => panic!("Type mismatches."),
    }
  }

  /// Equality comparison.
  pub fn eq(&self, rhs: &Self) -> Self {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x.eq(y)),
      (Value::Struct(x), Value::Struct(y)) => Value::Primitive(PrimitiveValue::Bool(x._eq(y))),
      (Value::TypeParameter(x), Value::TypeParameter(y)) => Value::Primitive(PrimitiveValue::Bool(x._eq(y))),
      _ => todo!(),
      _ => panic!("Type mismatches."),
    }
  }

  /// Nonequality comparison.
  pub fn neq(&self, rhs: &Self) -> Self {
    !self.eq(rhs)
  }
}

/// Product of `Value` and `Constraint`.
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

  /// Construct a new symbolic constant with the given name and type.
  pub fn new_const<S: Into<Symbol>>(x: S, t: &Type, context: &'ctx Context) -> Self {
    Self {
      value: Value::new_const(x, t, context),
      constraint: Bool::from_bool(context, true),
    }
  }

  pub fn decompose(self) -> (Value<'ctx>, Constraint<'ctx>) {
    (self.value, self.constraint)
  }

  /// Turn a constrained boolean value to a constraint,
  /// which is the conjunction of the value and the constraint.
  pub fn to_constraint(self) -> Constraint<'ctx> {
    match self {
      ConstrainedValue {
        value: Value::Primitive(PrimitiveValue::Bool(b)),
        constraint,
      } => b & constraint,
      _ => panic!("Only values of boolean sort can be turned into a constraint."),
    }
  }

  /// Return a single merged value if `self` and `other` have identical values,
  /// otherwise a union of `self` and `other`.
  pub fn merge(self, other: Self) -> Vec<Self> {
    if self.value == other.value {
      vec![Self::new(
        self.value,
        (self.constraint | other.constraint).simplify(),
      )]
    } else {
      vec![self, other]
    }
  }
}
