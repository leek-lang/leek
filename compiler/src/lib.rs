#![feature(is_some_and)]
#![feature(is_ascii_octdigit)]

use std::path::PathBuf;

use error::LeekCompilerError;
use lexer::LeekLexer;
use parser::LeekParser;
use reader::FileReader;

use crate::{ast::LeekAst, parser::Parser};

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod position;
pub mod reader;

pub fn parse_file(path: PathBuf) -> Result<LeekAst, LeekCompilerError> {
    let reader = FileReader::new(path)?;
    let lexer = LeekLexer::new(reader);
    let parse_tree = LeekParser::parse(lexer)?;

    println!("{}", parse_tree.root);

    todo!("build ast from parse tree")
}

#[cfg(test)]
mod test {
    use crate::parse_file;

    #[test]
    fn run_examples() {
        let files = std::fs::read_dir("../examples")
            .unwrap()
            .map(|f| f.unwrap());

        for file in files {
            parse_file(file.path()).unwrap();
        }
    }
}
