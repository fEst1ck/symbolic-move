use std::collections::BTreeMap;
use itertools::Itertools;
use move_model::model::{GlobalEnv, QualifiedInstId, StructId, ModuleId, StructEnv, FieldEnv};
use z3::{Context, DatatypeSort, DatatypeBuilder, DatatypeAccessor, Sort};

pub use move_model::ty::{PrimitiveType, Type};

use crate::value::PrimitiveValue;

pub fn primitive_type_to_sort<'ctx>(t: &PrimitiveType, ctx: &'ctx Context) -> Sort<'ctx> {
  match t {
    PrimitiveType::Bool => Sort::bool(ctx),
    PrimitiveType::U8 => Sort::bitvector(ctx, 8),
    PrimitiveType::U64 => Sort::bitvector(ctx, 64),
    PrimitiveType::U128 => Sort::bitvector(ctx, 8),
    PrimitiveType::Address => Sort::bitvector(ctx, PrimitiveValue::ADDR_LENGTH),
    PrimitiveType::Signer => Sort::bitvector(ctx, PrimitiveValue::ADDR_LENGTH),
    _ => todo!(),
  }
}

pub type ResourceId = QualifiedInstId<StructId>;

pub fn new_resource_id(module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) -> ResourceId {
  QualifiedInstId { module_id, inst: type_params.clone(), id: struct_id }
}

/// Table from resource id to z3 sort. Used to create a memoized function
/// converting a move type to a z3 sort.
pub struct Datatypes<'ctx, 'env> {
  ctx: &'ctx Context,
  global_env: &'env GlobalEnv,
  table: BTreeMap<ResourceId, DatatypeSort<'ctx>>, 
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

  // Get the uninitiated struct type.
  pub fn get_struct_type(&self, mod_id: ModuleId, struct_id: StructId) -> Type {
    let struct_env = self.global_env.get_struct(mod_id.qualified(struct_id));
    let field_types: Vec<Type> = struct_env
        .get_fields()
        .map(|field_env| field_env.get_type())
        .collect();
    Type::Struct(mod_id, struct_id, field_types)
  }

  // Get the uninitiated struct type.
  pub fn get_field_types(&self, mod_id: ModuleId, struct_id: StructId) -> Vec<Type> {
    get_field_types(self.global_env, mod_id, struct_id)
  }

  fn insert(&mut self, module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) {
    let struct_type = self.get_struct_type(module_id, struct_id);
    let instantiated_struct_type = struct_type.instantiate(&type_params);
    match instantiated_struct_type {
      Type::Struct(_, _, field_types) => {
        let module_env = self.global_env.get_module(module_id);
        let struct_env: StructEnv = module_env.get_struct(struct_id);
        let field_names: Vec<String> = struct_env.get_fields().map(|field_env| get_field_name(&struct_env, &field_env)).collect();
        let data_type = DatatypeBuilder::new(self.get_ctx(), format!("{}<{:?}>", struct_env.get_full_name_str(), type_params.iter().format(", ")))
          .variant(
            &struct_env.get_full_name_str(),
            field_names.iter().map(|x| &x[..])
            .zip(
              field_types.iter().map(|t| DatatypeAccessor::Sort(self.type_to_sort(t)))
            ).collect()
          )
          .finish();
        let resource_id = QualifiedInstId { module_id, inst: type_params.clone(), id: struct_id };
        self.table.insert(resource_id, data_type);
      }
      _ => unreachable!(),
    }
  }

  /// Turn a resource id to a Z3 datatype, memoized.
  fn from_struct1(&mut self, module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) -> &DatatypeSort<'ctx> {
    let resource_id = QualifiedInstId { module_id, inst: type_params.clone(), id: struct_id };
    // cannot directly match self.table.get here, 
    if self.table.contains_key(&resource_id) {
      self.table.get(&resource_id).unwrap()
    } else {
      self.insert(module_id, struct_id, type_params.clone());
      self.from_struct1(module_id, struct_id, type_params)
    }
  }

  /// Turn a resource id to a Z3 datatype, memoized.
  pub fn from_struct(&mut self, resource: &ResourceId) -> &DatatypeSort<'ctx> {
    self.from_struct1(resource.module_id, resource.id, resource.inst.clone())
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

pub fn get_field_name<'env>(struct_env: &StructEnv<'env>, field_env: &FieldEnv<'env>) -> String {
  let symbol_pool = struct_env.symbol_pool();
  symbol_pool.string(field_env.get_name()).to_string()
}

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