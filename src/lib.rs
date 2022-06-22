#![feature(generic_associated_types)]
pub mod state;
pub mod value;
pub mod dynamic;
pub mod constraint;
pub mod ty;
pub mod bytecode;
pub mod traits;
pub mod context;
pub mod symbolic_tree;

use move_model::{model::{GlobalEnv, ModuleEnv, FunId, FunctionEnv}, ast::ModuleName};

fn get_module_env<'env>(global_env: &'env GlobalEnv, addr: &String, module_name: &String) -> Option<ModuleEnv<'env>>{
  let module_name = ModuleName::from_str(addr, global_env.symbol_pool().make(module_name));
  global_env.find_module(&module_name)
}

fn get_fn_by_name<'env>(module_env: &'env ModuleEnv, fn_name: &String) -> FunctionEnv<'env> {
  let fn_symbol = module_env.symbol_pool().make(fn_name);
  module_env.get_function(FunId::new(fn_symbol))
}