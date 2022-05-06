use std::collections::BTreeMap;
use itertools::Itertools;
use move_model::model::{GlobalEnv, QualifiedInstId, StructId, ModuleId, StructEnv, FieldEnv};
use z3::{Context, DatatypeSort, DatatypeBuilder, DatatypeAccessor, Sort, FuncDecl};

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

pub type FieldId = usize;
pub type ResourceId = QualifiedInstId<StructId>;

pub fn new_resource_id(module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) -> ResourceId {
  QualifiedInstId { module_id, inst: type_params.clone(), id: struct_id }
}

/// Table from closed types to z3 sort. Used to create a memoized function
/// converting a move type to a z3 sort.
pub struct Datatypes<'ctx, 'env> {
  ctx: &'ctx Context,
  global_env: &'env GlobalEnv,
  table: BTreeMap<Type, DatatypeSort<'ctx>>, 
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

  pub fn get_resource_type(&self, resource_id: ResourceId) -> Type {
    self.get_struct_type(resource_id.module_id, resource_id.id).instantiate(&resource_id.inst)
  }

  // Get the uninitiated struct type.
  pub fn get_field_types(&self, mod_id: ModuleId, struct_id: StructId) -> Vec<Type> {
    get_field_types(self.global_env, mod_id, struct_id)
  }

  pub fn insert(&mut self, module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) {
    if !self.table.contains_key(&Type::Struct(module_id.clone(), struct_id.clone(), type_params.clone())) {
      let field_types = Type::instantiate_vec(self.get_field_types(module_id.clone(), struct_id.clone()), &type_params);
      let module_env = self.global_env.get_module(module_id);
      let struct_env: StructEnv = module_env.get_struct(struct_id);
      let struct_name = &struct_env.get_full_name_str();
      let field_names: Vec<String> = struct_env.get_fields().map(|field_env| get_field_name(&struct_env, &field_env)).collect();
      let qualified_field_names: Vec<String> = field_names.into_iter().map(|field_name| format!("{}-{}", struct_name, field_name)).collect();
      let data_type = DatatypeBuilder::new(self.get_ctx(), format!("{}<{:?}>", struct_env.get_full_name_str(), type_params.iter().format(", ")))
        .variant(
          struct_name,
          qualified_field_names.iter().map(|qualified_field_name| &qualified_field_name[..])
          .zip(
            field_types.iter().map(|t| DatatypeAccessor::Sort(self.type_to_sort(t)))
          ).collect()
        )
        .finish();
      self.table.insert(Type::Struct(module_id, struct_id, type_params), data_type);
    }
  }

  /// Turn a resource id to a Z3 datatype, memoized.
  fn from_struct1(&mut self, module_id: ModuleId, struct_id: StructId, type_params: Vec<Type>) -> &DatatypeSort<'ctx> {
    let struct_type = Type::Struct(module_id.clone(), struct_id.clone(), type_params.clone());
    // cannot directly match self.table.get here, 
    if self.table.contains_key(&struct_type) {
      self.table.get(&struct_type).unwrap()
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

  // should only be called when `t` is cached!
  pub fn pack(&self, t: &Type) -> Option<&FuncDecl<'ctx>> {
    match t {
      Type::Struct(mod_id, struct_id, type_params) => {
        // if !self.table.contains_key(t) {
        //   self.insert(*mod_id, *struct_id, type_params.clone());
        // }
        self.table.get(t).map(|x| &x.variants[0].constructor)
      }
      _ => None,
    }
  }

  // should only be called when `t` is cached!
  pub fn unpack(&self, t: &Type) -> Option<&Vec<FuncDecl<'ctx>>> {
    match t {
      Type::Struct(mod_id, struct_id, type_params) => {
        // if !self.table.contains_key(t) {
        //   self.insert(*mod_id, *struct_id, type_params.clone());
        // }
        self.table.get(t).map(|x| &x.variants[0].accessors)
      }
      _ => None,
    }
  }

  // should only be called when `t` is cached!
  pub fn pack_unpack(&mut self, t: &Type) -> Option<(&FuncDecl<'ctx>, &Vec<FuncDecl<'ctx>>)> {
    match t {
      Type::Struct(mod_id, struct_id, type_params) => {
        if !self.table.contains_key(t) {
          self.insert(*mod_id, *struct_id, type_params.clone());
        }
        self.table.get(t).map(|x| 
        (&x.variants[0].constructor, &x.variants[0].accessors)
      )
    }
      _ => None,
    }
  }
}

// Utilities
pub fn get_field_name<'env>(struct_env: &StructEnv<'env>, field_env: &FieldEnv<'env>) -> String {
  let symbol_pool = struct_env.symbol_pool();
  symbol_pool.string(field_env.get_name()).to_string()
}

pub fn get_struct_type(global_env: &GlobalEnv, mod_id: ModuleId, struct_id: StructId) -> Type {
  let struct_env = global_env.get_struct(mod_id.qualified(struct_id));
  let field_types: Vec<Type> = struct_env
      .get_fields()
      .map(|field_env| field_env.get_type())
      .collect();
  Type::Struct(mod_id, struct_id, field_types)
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