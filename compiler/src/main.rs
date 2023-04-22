use std::path::PathBuf;

use clap::Parser;
use leek::backend::{optimization::OptimizationLevel, EmitMode};

#[derive(Parser, Debug)]
#[command(author, version, about = "A bootstrap compiler for the Leek language", long_about = None)]
struct LeekCompilerArgs {
    #[arg(required = true)]
    input_files: Vec<String>,
    #[arg(short, long, value_enum, value_name = "EMIT_MODE", default_value_t = EmitMode::default(), help = "Specifies what kind of output to generate")]
    emit: EmitMode,
    #[arg(long, help = "Builds in release mode without debugging information")]
    release: bool,
    #[arg(short, long, help = "Prints more detailed output when compiling")]
    verbose: bool,
    #[arg(
        short,
        long,
        help = "Specifies the name of the output executable. By default the name is taken from the input file with the correct output extension."
    )]
    output: Option<PathBuf>,
    #[arg(short = 'O', long, value_enum, default_value_t = OptimizationLevel::default(), help = "Specifies how to optimize the code")]
    opt_level: OptimizationLevel,
}

fn main() {
    let args = LeekCompilerArgs::parse();

    for file in &args.input_files {
        let ast = leek::frontend::parse_file(file.into()).unwrap_or_else(|e| e.report());
        println!("{ast:?}")
    }
}
