#![feature(is_some_and)]
#![feature(is_ascii_octdigit)]

use std::path::PathBuf;

use error::LeekCompilerError;
use lexer::{LeekLexer, Lexer};
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
    let parse_tree = LeekParser::parse(lexer).unwrap();

    println!("{}", parse_tree);

    todo!()
}
