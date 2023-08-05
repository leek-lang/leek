use std::fmt::Display;

use crate::{
    backend::CodeGenError,
    frontend::{lexer::LexerError, parser::ParserError, reader::FileReadError},
    middle::type_checking::TypeCheckingError,
};

// TODO: Refactor with thiserror

#[derive(Debug)]
pub enum CompilerError {
    FileReadError(FileReadError),         // File -> Chars
    LexerError(LexerError),               // Chars -> Tokens
    ParserError(ParserError),             // Tokens -> Parse Tree
    AstLoweringError,                     // AST -> HIR
    TypeCheckingError(TypeCheckingError), // HIR -> MIR
    LowLevelLoweringError,                // MIR -> LIR
    CodeGenError(CodeGenError),           // LIR -> ASM
}

impl CompilerError {
    /// Should print to the stderr and exit with a non-zero exit code
    pub fn report(&self) -> ! {
        eprintln!("{self}");

        std::process::exit(1);
    }
}

impl Display for CompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilerError::FileReadError(e) => write!(f, "File Read Error: \n{e}"),
            CompilerError::LexerError(e) => write!(f, "Lexer Error: \n{e}"),
            CompilerError::ParserError(e) => {
                write!(
                    f,
                    "Parser Error: {e}\n=================================\n\n{e:#?}\n"
                )
            }
            CompilerError::TypeCheckingError(e) => {
                write!(
                    f,
                    "Type Error: \n{e}\n=================================\n\n{e:#?}\n"
                )
            }

            _ => todo!("Implement other error messages"),
        }
    }
}

impl From<FileReadError> for CompilerError {
    fn from(error: FileReadError) -> Self {
        CompilerError::FileReadError(error)
    }
}

impl From<LexerError> for CompilerError {
    fn from(error: LexerError) -> Self {
        CompilerError::LexerError(error)
    }
}

impl From<ParserError> for CompilerError {
    fn from(error: ParserError) -> Self {
        CompilerError::ParserError(error)
    }
}

impl From<CodeGenError> for CompilerError {
    fn from(error: CodeGenError) -> Self {
        CompilerError::CodeGenError(error)
    }
}
