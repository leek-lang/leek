#![feature(is_some_and)]

use std::path::PathBuf;

use error::LeekCompilerError;
use lexer::{LeekLexer, Lexer};
use reader::FileReader;

use crate::ast::LeekAst;

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod reader;
pub mod position;

pub fn parse_file(path: PathBuf) -> Result<LeekAst, LeekCompilerError> {
    let reader = FileReader::new(path)?;
    let mut lexer = LeekLexer::new(reader);

    while lexer.has_next()? {
        println!("Got Token: {:?}", lexer.next()?)
    }

    todo!()
}
