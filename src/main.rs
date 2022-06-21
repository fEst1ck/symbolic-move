use std::io::{Result};

use clap::Parser;
/// Symbolic move interpreter
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    file: Vec<String>,
    /// Name of the function target
    #[clap(short, long)]
    target: String,
    /// Show local variables
    #[clap(short, long)]
    locals: bool,
}

fn main() -> Result<()> {
  Ok(())
}