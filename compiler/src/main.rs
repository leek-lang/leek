use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about = "A bootstrap compiler for the Leek language", long_about = None)]
struct LeekCompilerArgs {
    #[arg(required = true)]
    input_files: Vec<String>,
}

fn main() {
    let args = LeekCompilerArgs::parse();

    for file in &args.input_files {
        let ast = leek::frontend::parse_file(file.into()).unwrap_or_else(|e| e.report());
        println!("{ast:?}")
    }
}
