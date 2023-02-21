use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct LeekCompilerArgs {
    input_files: Vec<String>,
}

fn main() {
    let args = LeekCompilerArgs::parse();

    for file in &args.input_files {
        let ast = leek::parse_file(file.into()).unwrap_or_else(|e| e.report());
        println!("{ast:?}")
    }
}
