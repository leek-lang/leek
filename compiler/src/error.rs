use crate::{lexer::LexerError, reader::FileReadError};

pub enum LeekCompilerError {
    FileReadError(FileReadError),
    LexerError(LexerError),
    ParserError,
    AstError,
    TypeCheckerError,
}

impl LeekCompilerError {
    /// Should print to the stderr and exit with a non-zero exit code
    pub fn report(&self) -> ! {
        match self {
            LeekCompilerError::FileReadError(e) => eprint!("File Read Error: \n{e}"),
            LeekCompilerError::LexerError(e) => eprint!("Lexer Error: \n{e}"),

            _ => todo!("Implement other error messages"),
        }

        std::process::exit(1);
    }
}

impl From<FileReadError> for LeekCompilerError {
    fn from(error: FileReadError) -> Self {
        LeekCompilerError::FileReadError(error)
    }
}

impl From<LexerError> for LeekCompilerError {
    fn from(error: LexerError) -> Self {
        LeekCompilerError::LexerError(error)
    }
}
