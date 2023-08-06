use std::{
    cell::UnsafeCell,
    collections::VecDeque,
    fmt::{Debug, Display},
};

use crate::{
    frontend::position::{Position, SourceFile, Span},
    frontend::reader::CharacterReader,
};

use self::token::{IntegerLiteralKind, KeywordKind, Token, TokenKind};

use super::position::highlight_span;

mod test;
pub mod token;

/// Represents an error when lexing a file
#[derive(Debug)]
pub struct LexerError {
    kind: LexerErrorKind,
    source_file: SourceFile,
    position: Position,
}

impl PartialEq for LexerError {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[cfg(test)]
impl From<LexerErrorKind> for LexerError {
    fn from(kind: LexerErrorKind) -> Self {
        use std::path::PathBuf;

        LexerError {
            kind,
            source_file: SourceFile {
                path: Some(PathBuf::new()),
                content: String::new(),
            },
            position: Position::new(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum LexerErrorKind {
    UnexpectedChar(char),
    UnclosedWrappedLiteral(TokenKind),
    UnexpectedEndOfFloatLiteral,
    UnexpectedCharactersInFloatLiteral,
    UnexpectedExtraPeriodInFloatLiteral,
    UnexpectedEndOfIntegerLiteral(IntegerLiteralKind),
    UnexpectedCharactersInIntegerLiteral(IntegerLiteralKind),
}

impl Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            LexerErrorKind::UnexpectedChar(c) => writeln!(f, "Unexpected char `{c}`"),
            LexerErrorKind::UnclosedWrappedLiteral(kind) => {
                writeln!(f, "Unexpected end of wrapped literal: {kind:?}")
            }
            LexerErrorKind::UnexpectedEndOfFloatLiteral => {
                writeln!(f, "Unexpected end of float literal")
            }
            LexerErrorKind::UnexpectedCharactersInFloatLiteral => {
                writeln!(f, "Unexpected characters inside float literal")
            }
            LexerErrorKind::UnexpectedExtraPeriodInFloatLiteral => {
                writeln!(f, "Unexpected extra `.` inside float literal")
            }
            LexerErrorKind::UnexpectedEndOfIntegerLiteral(kind) => {
                writeln!(f, "Unexpected end of {kind:?} integer literal")
            }
            LexerErrorKind::UnexpectedCharactersInIntegerLiteral(kind) => {
                writeln!(f, "Unexpected characters inside {kind:?} integer literal")
            }
        }?;

        highlight_span(f, &self.source_file, Span::from_position(&self.position))?;

        Ok(())
    }
}

/// This lexer implementation uses a "lazy" iterator approach such
/// that characters are not read from the input stream until a token is requested.
///
/// The lexer uses interior mutability to allow for peeking ahead in the token stream.
/// Since peeking ahead modifies the state of the character reader, this would otherwise
/// not be possible, unless the peek function took a mutable reference to the lexer.
///
/// UnsafeCell is used to allow for an optimization of the peek function that stores
/// the peeked tokens in a VecDeque. This is done to avoid having to re-lex the same
/// tokens multiple times.
pub struct Lexer {
    character_reader: UnsafeCell<Box<dyn CharacterReader>>,
    peek_forward: UnsafeCell<VecDeque<Token>>,
}

impl Lexer {
    pub fn new(character_reader: impl CharacterReader + 'static) -> Self {
        Lexer {
            character_reader: UnsafeCell::new(Box::new(character_reader)),
            peek_forward: UnsafeCell::new(VecDeque::new()),
        }
    }

    /// Read a literal that is wrapped in the provided character
    /// The wrapper character can be escaped using the backslash character `\`
    fn read_wrapped_escapable(&self, wrapper: char, kind: TokenKind) -> Result<Token, LexerError> {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        let mut text = String::new();
        let start = character_reader.get_position().clone();

        macro_rules! get_next_char {
            () => {
                if let Some(c) = character_reader.next() {
                    c
                } else {
                    return Err(LexerError {
                        kind: LexerErrorKind::UnclosedWrappedLiteral(kind),
                        source_file: character_reader.get_source_file().to_owned(),
                        position: character_reader.get_position().clone(),
                    });
                }
            };
        }

        macro_rules! peek_nth_char {
            ($n:expr) => {
                if let Some(c) = character_reader.peek_nth($n) {
                    c
                } else {
                    return Err(LexerError {
                        kind: LexerErrorKind::UnclosedWrappedLiteral(kind),
                        source_file: character_reader.get_source_file().to_owned(),
                        position: character_reader.get_position().clone(),
                    });
                }
            };
        }

        macro_rules! expect_wrapper {
            () => {
                let c = get_next_char!();

                if c != wrapper {
                    unreachable!(
                        "Not enough chars in character_reader (should be checked in advance)"
                    );
                }

                text.push(c);
            };
        }

        // First Quote
        expect_wrapper!();

        // Read until next quote
        while *peek_nth_char!(0) != wrapper {
            // If escape char was found, read it in, and read in the escaped char
            if *peek_nth_char!(0) == '\\' && *peek_nth_char!(1) == wrapper {
                text.push(get_next_char!());
            }

            text.push(get_next_char!());
        }

        // Second Quote
        expect_wrapper!();

        let end = character_reader.get_position().clone();

        Ok(Token {
            kind,
            text,
            span: Span::new(start, end),
        })
    }

    /// Reads a generic number literal into either an integer or double
    fn read_number_literal(&self) -> Result<Token, LexerError> {
        /*
         * Integer Cases:
         *
         * 1. `42069` - 1 or more dec digits
         * 2. `0xF2AB` - `0x` and then 1 or more hex digits
         * 3. `0b11010101` - `0b` and then 1 or more binary digits
         * 4. `0o01234567` - `0o` and then 1 or more octal digits
         *
         * 5. `1337u32`, `69i32` - 1 or more dec digits followed by `u<int size>` or `i<int size>` (8, 16, 32, 64, 128, or size)
         *
         * If size is not specified, i32 is the default
         *
         * Anywhere within the digits, `_` is allowed and is ignored
         *
         * Float Cases:
         *
         * 1. `0.1375454` - 1 or more dec digits, a `.`, and 1 or more dec digits
         * 2. `576.1375454f64` - 1 or more dec digits, a `.`, 1 or more dec digits followed by `f<float size>` (32 or 64)
         *
         * If size is not specified, f32 is the default
         */

        // TODO: Lex negative numbers

        let character_reader = unsafe { &mut *self.character_reader.get() };

        // Look ahead to match different literal types
        return 'number: {
            if *character_reader.peek().unwrap() == '0' {
                let Some(c) = character_reader.peek_nth(1) else {
                    // Only found `0` and nothing else so parse as int literal `0`
                    break 'number self.read_dec_int_or_float_literal();
                };

                match *c {
                    // Hex int with format `0x<more digits>`
                    'x' => self.read_based_int_literal(IntegerLiteralKind::Hexadecimal, |c| {
                        c.is_ascii_hexdigit()
                    }),
                    // Bin int with format `0b<more digits>`
                    'b' => self.read_based_int_literal(IntegerLiteralKind::Binary, |c| {
                        c == '0' || c == '1'
                    }),
                    // Oct int with format `0o<more digits>`
                    'o' => self.read_based_int_literal(IntegerLiteralKind::Octal, |c| {
                        c.is_ascii_octdigit()
                    }),
                    // Float with format `0.<more digits>`
                    '.' => self.read_dec_int_or_float_literal(),
                    // Int with format `0<a><more digits>` or potentially float with format `0<a><more digits?>.<more digits>`
                    a if a.is_ascii_digit() => self.read_dec_int_or_float_literal(),
                    // found non digit and non special specifier after leading `0`, so parse the `0` as a single dec digit
                    _ => self.read_dec_int_or_float_literal(),
                }
            } else {
                // Any dec int or float that does not start with 0
                self.read_dec_int_or_float_literal()
            }
        };
    }

    fn read_based_int_literal(
        &self,
        literal_kind: IntegerLiteralKind,
        is_in_base: fn(char) -> bool,
    ) -> Result<Token, LexerError> {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        macro_rules! create_error {
            ($kind:expr) => {
                LexerError {
                    kind: $kind,
                    source_file: character_reader.get_source_file().to_owned(),
                    position: character_reader.get_position().clone(),
                }
            };
        }

        macro_rules! get_next_char {
            () => {
                character_reader.next().ok_or_else(|| LexerError {
                    kind: LexerErrorKind::UnexpectedEndOfIntegerLiteral(literal_kind),
                    source_file: character_reader.get_source_file().to_owned(),
                    position: character_reader.get_position().clone(),
                })?
            };
        }

        let start = character_reader.get_position().clone();

        let mut text = String::new();

        // `0`
        text.push(get_next_char!());
        // special boundary
        text.push(get_next_char!());

        while character_reader.has_next() {
            let peeked_char = *character_reader.peek().unwrap();

            if peeked_char == '_' {
                // Ignore underscores
                character_reader.next().unwrap();
                continue;
            } else if !peeked_char.is_ascii_alphanumeric() {
                // Stop parsing where we are if we encounter any symbols
                break;
            }

            // TODO: add support for type specifiers like `u32` and `i32`

            if !is_in_base(peeked_char) {
                return Err(create_error!(
                    LexerErrorKind::UnexpectedCharactersInIntegerLiteral(literal_kind)
                ));
            }

            text.push(get_next_char!());
        }

        if text.len() <= 2 {
            return Err(create_error!(
                LexerErrorKind::UnexpectedEndOfIntegerLiteral(literal_kind)
            ));
        }

        let end = character_reader.get_position().clone();

        Ok(Token {
            kind: TokenKind::IntegerLiteral(literal_kind),
            text,
            span: Span::new(start, end),
        })
    }

    fn read_dec_int_or_float_literal(&self) -> Result<Token, LexerError> {
        enum NumberLexingState {
            Integer,
            Float,
        }

        let mut state = NumberLexingState::Integer;

        let character_reader = unsafe { &mut *self.character_reader.get() };

        macro_rules! create_error {
            ($kind:expr) => {
                LexerError {
                    kind: $kind,
                    source_file: character_reader.get_source_file().to_owned(),
                    position: character_reader.get_position().clone(),
                }
            };
        }

        macro_rules! get_next_char {
            () => {
                character_reader.next().ok_or_else(|| LexerError {
                    kind: match state {
                        NumberLexingState::Integer => {
                            LexerErrorKind::UnexpectedEndOfIntegerLiteral(
                                IntegerLiteralKind::Decimal,
                            )
                        }
                        NumberLexingState::Float => LexerErrorKind::UnexpectedEndOfFloatLiteral,
                    },
                    source_file: character_reader.get_source_file().to_owned(),
                    position: character_reader.get_position().clone(),
                })?
            };
        }

        let start = character_reader.get_position().clone();

        let mut text = String::new();

        // first char
        text.push(get_next_char!());

        while character_reader.has_next() {
            let peeked_char = *character_reader.peek().unwrap();

            match peeked_char {
                // Ignore underscores
                '_' => {
                    character_reader.next().unwrap();
                    continue;
                }
                // Stop lexing where we are if we encounter any symbols
                c if !c.is_ascii_alphanumeric() && c != '.' => {
                    break;
                }
                // Non digit and non `.` characters while lexing
                c if !c.is_ascii_digit() && c != '.' => {
                    return Err(create_error!(match state {
                        NumberLexingState::Integer => {
                            LexerErrorKind::UnexpectedCharactersInIntegerLiteral(
                                IntegerLiteralKind::Decimal,
                            )
                        }
                        NumberLexingState::Float =>
                            LexerErrorKind::UnexpectedCharactersInFloatLiteral,
                    }));
                }
                // Beginning of float, or an error
                '.' => {
                    match state {
                        NumberLexingState::Integer => state = NumberLexingState::Float,
                        NumberLexingState::Float => {
                            return Err(create_error!(
                                LexerErrorKind::UnexpectedExtraPeriodInFloatLiteral
                            ))
                        }
                    }
                    text.push(get_next_char!());
                }
                // Any ascii digit 0-9
                c if c.is_ascii_digit() => {
                    text.push(get_next_char!());
                }
                // All other character types have already been matched
                _ => unreachable!(),
            }

            // TODO: add support for type specifiers like `u32` and `i32`
        }

        // If we are in float mode, check if there were chars after the `.`
        if let NumberLexingState::Float = state {
            if text.ends_with('.') {
                return Err(create_error!(LexerErrorKind::UnexpectedEndOfFloatLiteral));
            }
        }

        let end = character_reader.get_position().clone();

        Ok(Token {
            kind: match state {
                NumberLexingState::Integer => {
                    TokenKind::IntegerLiteral(IntegerLiteralKind::Decimal)
                }
                NumberLexingState::Float => TokenKind::FloatLiteral,
            },
            text,
            span: Span::new(start, end),
        })
    }

    /// Advance the lexer while the next character matches the predicate, and return the resulting string
    fn read_while(&self, predicate: fn(char) -> bool) -> String {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        let mut res = String::new();

        while character_reader.has_next() {
            let c = character_reader.peek().unwrap();

            if !predicate(*c) {
                return res;
            }

            res.push(character_reader.next().unwrap());
        }

        res
    }

    /// Advance the lexer while the next character matches the predicate, and discard the matched chars
    fn ignore_while(&self, predicate: fn(char) -> bool) {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        while character_reader.has_next() {
            let c = character_reader.peek().unwrap();

            if !predicate(*c) {
                return;
            }

            character_reader.next();
        }
    }

    /// Requires character to be available
    fn read_single(&self, kind: TokenKind) -> Token {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        let start = character_reader.get_position().clone();
        let c = character_reader.next().unwrap();
        let end = character_reader.get_position().clone();

        Token {
            kind,
            text: c.into(),
            span: Span::new(start, end),
        }
    }

    /// Peeks the character reader several chars forward to look for a char sequence
    fn lookahead_has(&self, string: &str, n: usize) -> bool {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        let chars = string.chars();

        for (i, c) in chars.enumerate() {
            let Some(peeked) = character_reader.peek_nth(n + i) else {
                return false;
            };

            if *peeked != c {
                return false;
            }
        }

        true
    }

    /// Reads a fixed number of chars from the character reader and returns the resulting token
    ///
    /// Requires that the character reader be checked in advance to contain the correct sequence
    fn read_multi(&self, string: &str, kind: TokenKind) -> Token {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        let mut text = String::new();
        let start = character_reader.get_position().clone();

        for expected_char in string.chars() {
            if !character_reader.has_next() {
                unreachable!("Not enough chars in character_reader (should be checked in advance)")
            }

            let c = character_reader.peek().unwrap();

            if *c != expected_char {
                unreachable!(
                    "Char from character_reader did not match (should be checked in advance)"
                )
            }

            text.push(character_reader.next().unwrap());
        }

        let end = character_reader.get_position().clone();

        Token {
            kind,
            text,
            span: Span::new(start, end),
        }
    }

    /// Looks ahead to see if there is an `=` following the given prefix
    fn lookahead_has_equals(&self, prefix: impl Into<String>, n: usize) -> bool {
        let mut c: String = prefix.into();
        c.push('=');

        self.lookahead_has(&c, n)
    }

    /// Reads a fixed number of chars with an `=` suffixed to the given prefix from the character reader and returns the resulting token
    ///
    /// Requires that the character reader be checked in advance to contain the correct sequence
    fn read_multi_equals(&self, prefix: impl Into<String>, kind: TokenKind) -> Token {
        let mut c: String = prefix.into();
        c.push('=');

        self.read_multi(&c, kind)
    }

    fn read_single_operator(&self, c: char, single: TokenKind, equals: TokenKind) -> Token {
        if self.lookahead_has_equals(c, 0) {
            self.read_multi_equals(c, equals)
        } else {
            self.read_single(single)
        }
    }

    fn read_double_operator(&self, c: char, normal: TokenKind, equals: TokenKind) -> Token {
        if self.lookahead_has_equals(c, 1) {
            self.read_multi_equals(c.to_string().repeat(2), equals)
        } else {
            self.read_multi(&c.to_string().repeat(2), normal)
        }
    }

    fn read_next_token(&self) -> Result<Option<Token>, LexerError> {
        let character_reader = unsafe { &mut *self.character_reader.get() };

        while character_reader.has_next() {
            let start = character_reader.get_position().clone();

            // SAFETY: always checking if more characters are available before unwrapping
            let first_char = *character_reader.peek().unwrap();

            let token = Ok(Some(match first_char {
                // New lines are significant
                '\n' => self.read_single(TokenKind::Newline),

                // Whitespace
                a if a.is_ascii_whitespace() => {
                    self.ignore_while(|c| c.is_ascii_whitespace() && c != '\n');
                    continue;
                }

                // Chop Comments
                '/' if character_reader.peek_nth(1).is_some_and(|c| *c == '/') => {
                    self.ignore_while(|c| c != '\n');
                    continue;
                }

                // Words
                a if a.is_ascii_alphabetic() => {
                    let word = self.read_while(|c| c.is_ascii_alphanumeric() || c == '_');

                    Token {
                        kind: match KeywordKind::try_from(&word) {
                            Ok(kw_kind) => TokenKind::Keyword(kw_kind),
                            Err(_) => TokenKind::Identifier,
                        },
                        text: word,
                        span: Span::new(start, character_reader.get_position().clone()),
                    }
                }

                // Literals
                '"' => self.read_wrapped_escapable('"', TokenKind::StringLiteral)?,
                '\'' => self.read_wrapped_escapable('\'', TokenKind::CharLiteral)?,
                a if a.is_ascii_digit() => self.read_number_literal()?,

                // Grouping Symbols
                c @ ('(' | ')' | '[' | ']' | '{' | '}') => {
                    self.read_single(TokenKind::grouping_symbol_from(c))
                }

                // Arrows (`->`)
                '-' if character_reader.peek_nth(1).is_some_and(|c| *c == '>') => {
                    self.read_multi("->", TokenKind::Arrow)
                }

                // Bang Coalescing (`!.`)
                '!' if character_reader.peek_nth(1).is_some_and(|c| *c == '.') => {
                    self.read_multi("!.", TokenKind::BangCoalescing)
                }

                // Double Colon (`::`)
                ':' if character_reader.peek_nth(1).is_some_and(|c| *c == ':') => {
                    self.read_multi("::", TokenKind::DoubleColon)
                }

                // Double operators (must come first because of lookahead clash)
                c @ ('*' | '&' | '|' | '>' | '<')
                    if character_reader.peek_nth(1).is_some_and(|x| *x == c) =>
                {
                    self.read_double_operator(
                        c,
                        TokenKind::double_operator_from(c),
                        TokenKind::double_equals_operator_from(c),
                    )
                }

                // Single Operators
                c @ ('=' | '<' | '>' | '+' | '-' | '*' | '/' | '%' | '~' | '!' | '&' | '|'
                | '^') => self.read_single_operator(
                    c,
                    TokenKind::single_operator_from(c),
                    TokenKind::single_equals_operator_from(c),
                ),

                // Non-Operator symbols
                c @ ('?' | ',' | ';' | ':' | '.' | '\\' | '_' | '@' | '#' | '$') => {
                    self.read_single(TokenKind::other_symbol_from(c))
                }

                // Other
                c => {
                    return Err(LexerError {
                        kind: LexerErrorKind::UnexpectedChar(c),
                        source_file: character_reader.get_source_file().clone(),
                        position: character_reader.get_position().clone(),
                    })
                }
            }));

            return token;
        }

        // If got to the end of the cursor without finding any more tokens,
        // then we will never return more tokens
        Ok(None)
    }

    fn get_next_cached_or_read(&self) -> Result<Option<Token>, LexerError> {
        let peek_forward = unsafe { &mut *self.peek_forward.get() };

        // Check if more tokens have already been precomputed for us
        if !peek_forward.is_empty() {
            // Always returns `Some`
            return Ok(peek_forward.pop_front());
        }

        self.read_next_token()
    }
}

/// Lexer public interface
impl Lexer {
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<Token>, LexerError> {
        self.get_next_cached_or_read()
    }

    pub fn peek(&self) -> Result<Option<&Token>, LexerError> {
        let peek_forward = unsafe { &mut *self.peek_forward.get() };

        // Check if more tokens have already been precomputed for us
        if let Some(token) = peek_forward.front() {
            // Always returns `Some`
            return Ok(Some(token));
        }

        let peek_forward = unsafe { &mut *self.peek_forward.get() };

        // If there are more tokens
        if let Some(token) = self.get_next_cached_or_read()? {
            // Store the token for later usage
            peek_forward.push_back(token);

            // Return a reference to the token
            Ok(peek_forward.front())
        } else {
            // Otherwise, return None since there are no tokens to peek
            Ok(None)
        }
    }

    pub fn peek_nth(&self, n: usize) -> Result<Option<&Token>, LexerError> {
        let peek_forward = unsafe { &mut *self.peek_forward.get() };

        // Check if `n` tokens have already been precomputed for us
        if peek_forward.len() > n {
            // Always returns `Some`
            let peek = peek_forward;
            return Ok(peek.get(n));
        }

        // Otherwise, pre-compute the next `n` tokens from the amount we've already computed
        for _ in peek_forward.len()..=n {
            // Get the next token or return early if none more are found
            let Some(token) = self.read_next_token()? else {
                return Ok(None);
            };

            // Store the token for later usage
            peek_forward.push_back(token);
        }

        // Always returns `Some` because we would not have completed the loop otherwise.
        Ok(peek_forward.get(n))
    }

    pub fn has_next(&self) -> Result<bool, LexerError> {
        Ok(self.peek()?.is_some())
    }

    pub fn get_position(&self) -> &Position {
        let character_reader = unsafe { &*self.character_reader.get() };

        character_reader.get_position()
    }

    pub fn get_source_file(&self) -> &SourceFile {
        let character_reader = unsafe { &*self.character_reader.get() };

        character_reader.get_source_file()
    }
}
