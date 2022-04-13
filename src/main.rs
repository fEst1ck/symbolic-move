use std::io::{stdout, Result};

use symbolic_move::{test_fn};
use clap::Parser;
/// Symbolic move interpreter
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    file: Vec<String>,
    /// Evaluate a function
    #[clap(short, long)]
    target: String,
}

fn main() -> Result<()> {
  let args = Args::parse();
  let fun_name: Vec<_> = args.target.split("::").collect();
  if fun_name.len() != 3 {
    println!("Invalid target name");
    Ok(())
  } else {
  test_fn(&args.file, &[],
    fun_name[0].to_string(), fun_name[1].to_string(), fun_name[2].to_string(),
    &mut stdout())
  }
}