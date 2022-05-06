//! Symolic move values.

use move_core_types::account_address::AccountAddress;
use move_model::ast::TempIndex;
use crate::{ty::{PrimitiveType, Type, Datatypes, new_resource_id, ResourceId}, state::BranchCondition};
use move_stackless_bytecode::stackless_bytecode::{Constant};
use std::{ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Not, Rem, Sub}, fmt::{Display, self}, rc::Rc, cell::RefCell};
use z3::{
  Context,
  ast::{Ast, Bool, Dynamic, BV, Datatype},
  Symbol,
};

use crate::constraint::{Constrained, Constraint, constraint_filter};

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
  pub const ADDR_LENGTH: u32 = 8 * AccountAddress::LENGTH as u32;

  /// Construct a constant symbolic value with the given primitive type and name.
  pub fn new_const<S: Into<Symbol>>(x: S, t: &PrimitiveType, ctx: &'ctx Context) -> Self {
    match t {
      PrimitiveType::Bool => PrimitiveValue::Bool(Bool::new_const(ctx, x)),
      PrimitiveType::U8 => PrimitiveValue::U8(BV::new_const(ctx, x, 8)),
      PrimitiveType::U64 => PrimitiveValue::U64(BV::new_const(ctx, x, 64)),
      PrimitiveType::U128 => PrimitiveValue::U128(BV::new_const(ctx, x, 128)),
      PrimitiveType::Address => PrimitiveValue::Address(BV::new_const(ctx, x, Self::ADDR_LENGTH)),
      PrimitiveType::Signer => PrimitiveValue::Signer(BV::new_const(ctx, x, Self::ADDR_LENGTH)),
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
        res.zero_ext(Self::ADDR_LENGTH - res.get_size())
      }),
      // U256, Bytearray
      _ => unimplemented!(),
    }
  }

  pub fn to_bool(&self) -> Option<&Bool<'ctx>> {
    match self {
      PrimitiveValue::Bool(x) => Some(x),
      _ => None,
    }
  }

  /// Simplify the wrapped z3 ast.
  pub fn simplify(self) -> Self {
    match self {
      PrimitiveValue::Bool(x) => PrimitiveValue::Bool(x.simplify()),
      PrimitiveValue::U8(x) => PrimitiveValue::U8(x.simplify()),
      PrimitiveValue::U64(x) => PrimitiveValue::U64(x.simplify()),
      PrimitiveValue::U128(x) => PrimitiveValue::U128(x.simplify()),
      PrimitiveValue::Address(x) => PrimitiveValue::Address(x.simplify()),
      PrimitiveValue::Signer(x) => PrimitiveValue::Signer(x.simplify()),
    }
  }

  /// Convert to the underlying z3 ast.
  pub fn unwrap(&self) -> &dyn Ast<'ctx> {
    match self {
      PrimitiveValue::Bool(x) => x,
      PrimitiveValue::U8(x) => x,
      PrimitiveValue::U64(x) => x,
      PrimitiveValue::U128(x) => x,
      PrimitiveValue::Address(x) => x,
      PrimitiveValue::Signer(x) => x,
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

impl<'ctx> Display for PrimitiveValue<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      PrimitiveValue::Bool(x) => write!(f, "{}", x),
      PrimitiveValue::Address(x) => write!(f, "addr: {}", x),
      _ => write!(f, "{:?}", self),
    }
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

impl<'ctx> Sub for PrimitiveValue<'ctx> {
  type Output = Self;
  fn sub(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x - y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x - y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x - y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Sub for &PrimitiveValue<'ctx> {
  type Output = PrimitiveValue<'ctx>;
  fn sub(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (PrimitiveValue::U8(x), PrimitiveValue::U8(y)) => PrimitiveValue::U8(x - y),
      (PrimitiveValue::U64(x), PrimitiveValue::U64(y)) => PrimitiveValue::U64(x - y),
      (PrimitiveValue::U128(x), PrimitiveValue::U128(y)) => PrimitiveValue::U128(x - y),
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

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Root<'ctx> {
  Global(ResourceId, BV<'ctx>),
  Local(TempIndex),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Loc<'ctx> {
  pub root: Root<'ctx>,
  pub access_path: Vec<usize>,
}

/// Symbolic move values.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value<'ctx> {
  Primitive(PrimitiveValue<'ctx>),
  Struct(Datatype<'ctx>),
  TypeParameter(Dynamic<'ctx>),
  Reference(Loc<'ctx>),
}

impl<'ctx> Value<'ctx> {
  /// Injection from closed values.
  pub fn from_constant(c: &Constant, ctx: &'ctx Context) -> Self {
    Value::Primitive(PrimitiveValue::from_constant(c, ctx))
  }

  /// Construct a new symbolic constant with the given type and name.
  pub fn new_const<'env, S: Into<Symbol>>(x: S, t: &Type, ctx: &'ctx Context, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>) -> Self {
    match t {
      Type::Primitive(t) => Value::Primitive(PrimitiveValue::new_const(x, t, ctx)),
      // Tuple
      // Vector
      Type::Struct(module_id, struct_id, type_params) => {
        let mut datatypes_mut_ref = datatypes.borrow_mut();
        let data_type = datatypes_mut_ref.from_struct(&new_resource_id(*module_id, *struct_id, type_params.clone()));
        Value::Struct(Datatype::new_const(&ctx, x, &data_type.sort))
      }
      Type::TypeParameter(_) =>
        unimplemented!(),
      Type::Reference(_, _) => todo!(),
      _ => unimplemented!(),
    }
  }

  /// Simplify the wrapped z3 ast.
  pub fn simplify(self) -> Self {
    match self {
      Value::Primitive(x) => Value::Primitive(x.simplify()),
      Value::Struct(x) => Value::Struct(x.simplify()),
      Value::Reference(x) => Value::Reference(x), // todo: maybe need to simpl when x is a global ref
      _ => unimplemented!(),
    }
  }

  pub fn wrap(x: &Dynamic<'ctx>, t: &Type) -> Self {
    match t {
      Type::Primitive(pt) => {
        match pt {
          PrimitiveType::Address => Value::Primitive(PrimitiveValue::Address(x.as_bv().unwrap())),
          PrimitiveType::Bool => Value::Primitive(PrimitiveValue::Bool(x.as_bool().unwrap())),
          PrimitiveType::U8 => Value::Primitive(PrimitiveValue::U8(x.as_bv().unwrap())),
          PrimitiveType::U64 => Value::Primitive(PrimitiveValue::U64(x.as_bv().unwrap())),
          PrimitiveType::U128 => Value::Primitive(PrimitiveValue::U128(x.as_bv().unwrap())),
          PrimitiveType::Signer => Value::Primitive(PrimitiveValue::Signer(x.as_bv().unwrap())),
          _ => unreachable!(),
        }
      }
      Type::Struct(_, _, _) => {
        Value::Struct(x.as_datatype().unwrap())
      }
      _ => unimplemented!(),
    }
  }

  pub fn as_bool(&self) -> Option<&Bool<'ctx>> {
    match self {
      Value::Primitive(PrimitiveValue::Bool(x)) => Some(x),
      _ => None,
    }
  }

  pub fn as_addr(&self) -> Option<&BV<'ctx>> {
    match self {
      Value::Primitive(PrimitiveValue::Address(x)) => Some(x),
      Value::Primitive(PrimitiveValue::Signer(x)) => Some(x),
      _ => None,
    }
  }

  pub fn as_datatype(&self) -> Option<&Datatype<'ctx>> {
    match self {
      Value::Struct(x) => Some(x),
      _ => None,
    }
  }

  /// Reference to the wrapped z3 ast.
  pub fn unwrap(&self) -> &dyn Ast<'ctx> {
    match self {
      Value::Primitive(x) => x.unwrap(),
      Value::Struct(x) => x,
      Value::TypeParameter(x) => x,
      // Value::Reference(x, _) => (*x.as_ref()).unwrap(),
      _ => todo!(),
    }
  }

    /// Reference to the wrapped z3 ast.
    pub fn as_dynamic(self) -> Dynamic<'ctx> {
      Dynamic::from_ast(self.unwrap())
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
    }
  }

  /// Nonequality comparison.
  pub fn neq(&self, rhs: &Self) -> Self {
    !self.eq(rhs)
  }
}

impl<'ctx> Display for Value<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Value::Primitive(x) => write!(f, "{}", x),
      Value::Struct(x) => write!(f, "{}", x),
      _ => write!(f, "{:?}", self),
    }
  }
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

impl<'ctx> Sub for Value<'ctx> {
  type Output = Self;
  fn sub(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x - y),
      _ => panic!("Type mismatches."),
    }
  }
}

impl<'ctx> Sub for &Value<'ctx> {
  type Output = Value<'ctx>;
  fn sub(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Value::Primitive(x), Value::Primitive(y)) => Value::Primitive(x - y),
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

impl<'ctx> Constrained<'ctx, Constraint<'ctx>> {
  /// (x, p) => x & p
  pub fn to_constraint(&self) -> Constraint<'ctx> {
    &self.content & &self.constraint
  }

  /// Return none if the constraint is unsatisfiable.
  pub fn to_constraint_opt(&self) -> Option<Constraint<'ctx>> {
    constraint_filter(self.to_constraint())
  }

  pub fn to_branch_condition(&self) -> BranchCondition<'ctx> {
    match self {
      Constrained { 
        content: b,
        constraint,
      } => 
        BranchCondition {
          true_branch: b & constraint,
          false_branch: !b & constraint,
        }
    }
  }
}

pub type ConstrainedValue<'ctx> = Constrained<'ctx, Value<'ctx>>;

impl<'ctx> ConstrainedValue<'ctx> {
  /// Construct a new symbolic constant with the given name and type.
  pub fn new_const<'env, S: Into<Symbol>>(x: S, t: &Type, context: &'ctx Context, datatypes: Rc<RefCell<Datatypes<'ctx, 'env>>>) -> Self {
    Constrained::pure(Value::new_const(x, t, context, datatypes), context)
  }

  /// Convert a constrained boolean to a branch condition.
  pub fn to_branch_condition(&self) -> Option<BranchCondition<'ctx>> {
    match self {
      Constrained { 
        content: Value::Primitive(PrimitiveValue::Bool(b)),
        constraint,
      } => Some(
        BranchCondition {
          true_branch: b & constraint,
          false_branch: !b & constraint,
        }
      ),
      _ => None,
    }
  }
}