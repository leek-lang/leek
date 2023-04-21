use std::{fmt::Display, path::PathBuf};

use itertools::{peek_nth, PeekNth};

use crate::frontend::position::{Position, SourceFile};

/// Generic trait representing any type of character reader
/// from a file, in a language server, or other
pub trait CharacterReader {
    fn next(&mut self) -> Option<char>;
    fn has_next(&mut self) -> bool;
    fn peek(&mut self) -> Option<&char>;
    fn peek_nth(&mut self, n: usize) -> Option<&char>;
    fn get_position(&self) -> &Position;
    fn get_source_file(&self) -> &SourceFile;
}

/// Specific file implementation of CharacterReader
pub struct FileReader {
    source_file: SourceFile,
    chars: PeekNth<std::vec::IntoIter<char>>,
    position: Position,
}

/// Represents an error when reading in a file
#[derive(Debug)]
pub enum FileReadError {
    NotFound(PathBuf),
}

impl Display for FileReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FileReadError::NotFound(path) => writeln!(f, "Could not find file: {:?}", path),
        }
    }
}

impl FileReader {
    pub fn new(path: PathBuf) -> Result<Self, FileReadError> {
        let file_contents =
            std::fs::read_to_string(&path).map_err(|_| FileReadError::NotFound(path.clone()))?;
        let chars = file_contents.chars().collect::<Vec<_>>().into_iter();
        let chars = peek_nth(chars);

        Ok(Self {
            source_file: SourceFile {
                path: Some(path.clone()),
                content: file_contents,
            },
            chars,
            position: Position::from(path),
        })
    }
}

impl From<String> for FileReader {
    fn from(value: String) -> Self {
        let chars = value.chars().collect::<Vec<_>>().into_iter();
        let chars = peek_nth(chars);

        Self {
            source_file: SourceFile {
                path: None,
                content: value,
            },
            chars,
            position: Position::new(),
        }
    }
}

impl CharacterReader for FileReader {
    fn next(&mut self) -> Option<char> {
        let Some(next_char) = self.chars.next() else {
            return None;
        };

        match next_char {
            '\n' => {
                self.position.row += 1;
                self.position.col = 0;
            }
            _ => self.position.col += 1,
        }

        Some(next_char)
    }

    fn has_next(&mut self) -> bool {
        self.peek().is_some()
    }

    fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    fn peek_nth(&mut self, n: usize) -> Option<&char> {
        self.chars.peek_nth(n)
    }

    fn get_position(&self) -> &Position {
        &self.position
    }

    fn get_source_file(&self) -> &SourceFile {
        &self.source_file
    }
}

#[cfg(test)]
mod test {
    use super::{CharacterReader, FileReader};

    #[test]
    fn similar_to_chars_peekable() {
        let file = r#"
        fn main() {
            leak a = 1
            leak b = 2
        
            leak node = Node("text")
        
            println()
            
        }
        "#;

        // Collect chars from string directly
        let chars: Vec<_> = file.chars().collect();

        // Collect chars with reader
        let mut reader = FileReader::from(file.to_owned());
        let mut reader_chars = Vec::new();

        while reader.has_next() {
            reader_chars.push(reader.next().unwrap())
        }

        assert_eq!(chars, reader_chars)
    }
}
