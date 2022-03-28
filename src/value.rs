//! Symolic move values.

use itertools::{Itertools, iproduct};
use move_core_types::account_address::AccountAddress;
use move_model::{model::{ModuleId, StructId, QualifiedInstId, GlobalEnv, StructEnv, FieldEnv}};
pub use move_model::ty::{PrimitiveType, Type};
use move_stackless_bytecode::stackless_bytecode::Constant;
use std::{ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Not, Rem}, collections::BTreeMap, iter::FromIterator, rc::Rc, cell::{Cell, RefCell}};
use z3::{
  Context,
  Solver, SatResult,
  ast::{Ast, Bool, Dynamic, BV, Datatype},
  Sort, Symbol, FuncDecl,
  DatatypeAccessor, DatatypeBuilder, DatatypeSort,
};

pub struct Datatypes<'ctx, 'env> {
  ctx: &'ctx Context,
  global_env: &'env GlobalEnv,
  table: BTreeMap<QualifiedInstId<StructId>, DatatypeSort<'ctx>>, 
}

impl<'ctx, 'env> Datatypes<'ctx, 'env> {
  pub fn new(ctx: &'ctx Context, global_env: &'env GlobalEnv) -> Self {
    Self {
      ctx,
      global_env,
      table: BTreeMap::new(),
    }
  }

  pub fn get_ctx(&self) -> &'ctx Context {
    self.ctx
  }

  fn update(&mut self, module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) {
    let module_env = self.global_env.get_module(module_id);
    let struct_env: StructEnv = module_env.get_struct(struct_id);
    let field_names: Vec<String> = struct_env.get_fields().map(|field_env| get_field_name(&struct_env, &field_env)).collect();
    let data_type = DatatypeBuilder::new(self.get_ctx(), format!("{}<{:?}>", struct_env.get_full_name_str(), type_params.iter().format(", ")))
      .variant(
        "",
        field_names.iter().map(|x| &x[..])
        .zip(
          type_params.iter().map(|t| DatatypeAccessor::Sort(self.type_to_sort(t)))
        ).collect()
      )
      .finish();
    let resource_id = QualifiedInstId { module_id, inst: type_params.clone(), id: struct_id };
    self.table.insert(resource_id, data_type);
  }

  /// Turn a resource id to a Z3 datatype, memoized.
  pub fn from_struct1(&mut self, module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) -> &DatatypeSort<'ctx> {
    let resource_id = QualifiedInstId { module_id, inst: type_params.clone(), id: struct_id };
    // cannot directly match self.table.get here, 
    if self.table.contains_key(&resource_id) {
      self.table.get(&resource_id).unwrap()
    } else {
      self.update(module_id, struct_id, type_params.clone());
      self.from_struct1(module_id, struct_id, type_params)
    }
  }

  /// Turn a resource id to a Z3 datatype, memoized.
  pub fn from_struct(&mut self, resource: &QualifiedInstId<StructId>) -> &DatatypeSort<'ctx> {
    self.from_struct1(resource.module_id, resource.id, resource.inst)
  }

  /// From move type to z3 sort.
  pub fn type_to_sort(&mut self, t: &Type) -> Sort<'ctx> {
    match t {
      Type::Primitive(t) => primitive_type_to_sort(t, self.get_ctx()),
      Type::Struct(module_id, struct_id, type_params) => self.from_struct1(*module_id, *struct_id, type_params.clone()).sort.clone(),
      _ => todo!(),
    }
  }
}

/// The type of formulae, i.e., terms of boolean sort.
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

pub struct Constrained<'ctx, T> {
  pub content: T,
  pub constraint: Constraint<'ctx>,
}

impl<'ctx> Constrained<'ctx, Constraint<'ctx>> {
  pub fn to_constraint(&self) -> Constraint<'ctx> {
    &self.content & &self.constraint
  }

  pub fn to_constraint_opt(&self) -> Option<Constraint<'ctx>> {
    let res = self.to_constraint();
    if sat(&res) {
      Some(res)
    } else {
      None
    }
  }
}

impl<'ctx> Constrained<'ctx, Value<'ctx>> {
  pub fn to_constrained_value(self) -> ConstrainedValue<'ctx> {
    ConstrainedValue { value: self.content, constraint: self.constraint }
  }

  pub fn from_constrained_value(x: ConstrainedValue<'ctx>) -> Self {
    Self {
      content: x.value,
      constraint: x.constraint,
    }
  }
}

impl<'ctx, T> Constrained<'ctx, T> {
  pub fn unconstrained(x: T, ctx: &'ctx Context) -> Self {
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

  /// Apply on the content field.
  pub fn map<U, F>(self, f: F) -> Constrained<'ctx, U>
  where F: Fn(T) -> U
  {
    Constrained { content: f(self.content), constraint: self.constraint }
  }

  /// (x, p) => pred(x) & p
  pub fn pred<F>(self, pred: F) -> Constraint<'ctx>
  where F: Fn(T) -> Constraint<'ctx>
  {
    self.map(pred).to_constraint()
  }

  /// (x, p) * (y, q) = ((x, y), p & q)
  pub fn prod<U>(self, other: Constrained<'ctx, U>) -> Constrained<'ctx, (T, U)> {
    Constrained { content: (self.content, other.content), constraint: self.constraint & other.constraint }
  }

  pub fn prod_opt<U>(self, other: Constrained<'ctx, U>) -> Option<Constrained<'ctx, (T, U)>> {
    let prod = self.prod(other).simplify();
    if sat(&prod.constraint) {
      Some(prod)
    } else {
      None
    }
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

/// Set of disjoint constrained values.
pub type Union<'ctx> = Vec<ConstrainedValue<'ctx>>;

pub struct Disjoints<'ctx, T>(pub Vec<Constrained<'ctx, T>>);

impl<'ctx, T: Clone> Disjoints<'ctx, T> {
  pub fn map<U, F>(self, f: F) -> Disjoints<'ctx, U>
    where F: Fn(T) -> U
  {
    self.into_iter().map(|x| x.map(f)).collect()
  }

  pub fn iter(&self) -> std::slice::Iter<'_, Constrained<'ctx, T>> {
    self.0.iter()
  }

  pub fn filter_prod<U: Clone>(&self, other: &Disjoints<'ctx, U>) -> Disjoints<'ctx, (T, U)> {
    Disjoints(
      iproduct!(self.iter(), other.iter())
      .filter_map(|(x, y)| x.clone().prod_opt(y.clone()))
      .collect()
    )
  }
}

impl<'ctx> Disjoints<'ctx, Constraint<'ctx>> {
  pub fn to_constraint(&self, ctx: &'ctx Context) -> Constraint<'ctx> {
    self.iter().filter_map(|x| x.to_constraint_opt().map(|x| x.simplify())).fold(Bool::from_bool(ctx, false), |acc, x| acc | x)
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

/// A pair of disjoint constraints. So true_branch & false_branch is never satisfiable.
pub struct BranchCondition<'ctx> {
  pub true_branch: Constraint<'ctx>,
  pub false_branch: Constraint<'ctx>,
}

impl<'ctx> BitOr for BranchCondition<'ctx> {
  type Output = Self;
  fn bitor(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (
        BranchCondition { true_branch: t1, false_branch: f1 },
        BranchCondition { true_branch: t2, false_branch: f2 },
      ) => BranchCondition { true_branch: t1 | t2, false_branch: f1 | f2 },
    }
  }
}

impl<'ctx> BranchCondition<'ctx> {
  /// The identity element of the | operation.
  pub fn or_id(ctx: &'ctx Context) -> Self {
    BranchCondition { true_branch: Bool::from_bool(ctx, false), false_branch: Bool::from_bool(ctx, false) }
  }

  /// Simplify fields.
  pub fn simplify(self) -> Self {
    match self {
      BranchCondition { true_branch, false_branch } => BranchCondition { true_branch: true_branch.simplify(), false_branch: false_branch.simplify() }
    }
  }
}

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

  pub fn to_bool(&self) -> Option<&Bool<'ctx>> {
    match self {
      PrimitiveValue::Bool(x) => Some(x),
      _ => None,
    }
  }

  /// Convert to the underlying ast.
  pub fn to_ast(&self) -> &dyn Ast<'ctx> {
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
        let data_type = struct_type_to_datatype_sort(*mod_id, *struct_id, types, ctx);
        Value::Struct(Datatype::new_const(&ctx, x, &data_type.sort))
      }
      Type::TypeParameter(x) =>
        Value::TypeParameter(FuncDecl::new(ctx, *x as u32, &[], &type_to_sort(t, ctx)).apply(&[])),
      _ => unimplemented!(),
    }
  }

  pub fn as_bool(&self) -> Option<&Bool<'ctx>> {
    match self {
      Value::Primitive(PrimitiveValue::Bool(x)) => Some(x),
      _ => None,
    }
  }

  pub fn as_datatype(&self) -> Option<&Datatype<'ctx>> {
    match self {
      Value::Struct(x) => Some(x),
      _ => None,
    }
  }

  pub fn to_ast(&self) -> &dyn Ast<'ctx> {
    match self {
      Value::Primitive(x) => x.to_ast(),
      Value::Struct(x) => x,
      Value::TypeParameter(x) => x,
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

  /// Convert a constrainted boolean to a branch condition.
  pub fn to_branch_condition(&self) -> BranchCondition<'ctx> {
    match self {
      ConstrainedValue { 
        value: Value::Primitive(PrimitiveValue::Bool(b)),
        constraint,
      } => BranchCondition {
        true_branch: b & constraint,
        false_branch: !b & constraint,
      },
      _ => panic!("Runtime type error. {:?} is not a boolean.", self),
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

// Utilities
/// Get the types of the fields of a struct.
pub fn get_field_types(global_env: &GlobalEnv, mod_id: ModuleId, struct_id: StructId) -> Vec<Type> {
  let struct_env = global_env.get_struct(mod_id.qualified(struct_id));
  struct_env
    .get_fields()
    .map(|field_env| {
      field_env.get_type()
    })
    .collect()
}

pub fn get_field_name<'env>(struct_env: &StructEnv<'env>, field_env: &FieldEnv<'env>) -> String {
  let symbol_pool = struct_env.symbol_pool();
  symbol_pool.string(field_env.get_name()).to_string()
}

// warning!!
// wrong when the struct is initiated differently.
pub(crate) fn struct_type_to_datatype_sort<'ctx>(mod_id: ModuleId, struct_id: StructId, types: &[Type], ctx: &'ctx Context) -> DatatypeSort<'ctx> {
  let field_names: Vec<String> = (0..types.len()).map(|i| i.to_string()).collect();
  let field_names1: Vec<&str> = field_names.iter().map(|x| &x[..]).collect();
  DatatypeBuilder::new(ctx, format!("{:?}::{:?}", mod_id, struct_id))
  .variant(
    "",
    field_names1.into_iter().
    zip(
      types.into_iter().map(|t| DatatypeAccessor::Sort(type_to_sort(t, ctx)))
    ).collect()
  )
  .finish()
}

pub fn primitive_type_to_sort<'ctx>(t: &PrimitiveType, ctx: &'ctx Context) -> Sort<'ctx> {
  match t {
    PrimitiveType::Bool => Sort::bool(ctx),
    PrimitiveType::U8 => Sort::bitvector(ctx, 8),
    PrimitiveType::U64 => Sort::bitvector(ctx, 64),
    PrimitiveType::U128 => Sort::bitvector(ctx, 8),
    PrimitiveType::Address => Sort::bitvector(ctx, PrimitiveValue::LENGTH),
    PrimitiveType::Signer => Sort::bitvector(ctx, PrimitiveValue::LENGTH),
    _ => todo!(),
  }
}

// TODO: this is wrong! use Datatype::type_to_sort instead.
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
      _ => todo!(),
    },
    // tuple
    // vector
    Type::Struct(mod_id, struct_id, types) => {
      let data_type = struct_type_to_datatype_sort(*mod_id, *struct_id, types, ctx);
      data_type.sort
    }
    Type::TypeParameter(id) => Sort::uninterpreted(ctx, Symbol::from(*id as u32)),
    _ => todo!(),
  }
}