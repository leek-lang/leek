use std::path::PathBuf;

use clap::Parser;
use leek::{
    backend::codegen::CodeGenTarget,
    common::config::{BuildMode, CompilerConfig, EmitMode, OptimizationLevel},
};

#[derive(Parser, Debug)]
#[command(author, version, about = "A bootstrap compiler for the Leek language", long_about = None)]
struct CompilerArgs {
    #[arg(required = true)]
    input_files: Vec<PathBuf>,
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

impl From<CompilerArgs> for CompilerConfig {
    fn from(args: CompilerArgs) -> Self {
        CompilerConfig {
            opt_level: args.opt_level,
            build_mode: if args.release {
                BuildMode::Release
            } else {
                BuildMode::Debug
            },
            emit_mode: args.emit,
            input_files: args.input_files,
            output_name: args.output,
            verbose: args.verbose,
        }
    }
}

fn main() {
    // Get the command line arguments
    let args = CompilerArgs::parse();

    // Convert to the global config struct
    let config: CompilerConfig = args.into();

    for file in &config.input_files {
        let ast = leek::frontend::parse_file(file.into()).unwrap_or_else(|e| e.report());
        println!("{ast:#?}");

        leek::backend::compile_ast(ast, &config, CodeGenTarget::x86LinuxGNU)
            .unwrap_or_else(|e| e.report());
    }
}
