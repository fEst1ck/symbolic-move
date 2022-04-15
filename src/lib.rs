pub mod state;
pub mod value;
pub mod evaluation;
pub mod constraint;
pub mod ty;

use std::{io::Write, collections::BTreeMap};

use move_model::{model::{GlobalEnv, ModuleEnv, FunId, FunctionEnv}, ast::ModuleName, run_model_builder};
use move_prover::{create_and_process_bytecode, cli::Options};
use move_stackless_bytecode::function_target_pipeline::{FunctionVariant, VerificationFlavor};
use {state::MoveState, evaluation::eval};
use z3::{Context, Config};

use crate::state::LocalState;

fn get_module_env<'env>(global_env: &'env GlobalEnv, addr: &String, module_name: &String) -> Option<ModuleEnv<'env>>{
  let module_name = ModuleName::from_str(addr, global_env.symbol_pool().make(module_name));
  global_env.find_module(&module_name)
}

fn get_fn_by_name<'env>(module_env: &'env ModuleEnv, fn_name: &String) -> FunctionEnv<'env> {
  let fn_symbol = module_env.symbol_pool().make(fn_name);
  module_env.get_function(FunId::new(fn_symbol))
}

pub fn test_fn<W: Write>(
  move_sources: &[String], deps_dir: &[String],
  addr: String, module_name: String, function_name: String,
  locals: bool,
  writer: &mut W
) -> std::io::Result<()> {
  let model_ = run_model_builder::<String, String>(
    move_sources.iter().map(|p| (vec![p.clone()], BTreeMap::new())).collect(),
    deps_dir.iter().map(|p| (vec![p.clone()], BTreeMap::new())).collect()
  );
  if let Ok(model) = model_ {
    let holder = create_and_process_bytecode(&Options::default(), &model);
    if let Some(module) = get_module_env(&model, &addr, &module_name) {
      let fun_env = get_fn_by_name(&module, &function_name);
      let target = holder.get_target(&fun_env, &FunctionVariant::Verification(VerificationFlavor::Regular));
      writeln!(writer, "Testing function target:\n{}", target)?;
      let config = Config::new();
      let ctx = Context::new(&config);
      let s = MoveState::new_default(&ctx, target);
      // println!("{:?}", s.offset_to_block_id);
      let eval_res = eval(s);
      for (i, mut s) in eval_res.into_iter().enumerate() {
        s.local_state = LocalState {
          locals: s.local_state.locals.into_iter().map(|x| x.simplify()).collect(),
          ..s.local_state
        };
        if locals {
          writeln!(writer, "Evaluation result #{}:\n{}", i, s)?;
        } else {
          writeln!(writer, "Evaluation result #{}:\n{}", i, s.local_state.termination_status())?;
        }
      }
    } else {
      writeln!(writer, "Module {}::{} not found.", &addr, module_name)?;
    }
    Ok(())
  } else {
    writeln!(writer, "Failed to compile {:?}", move_sources)
  }
}