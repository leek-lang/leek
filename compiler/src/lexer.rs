use core::num;
use std::{
    collections::VecDeque,
    fmt::{Debug, Display},
};

use crate::{position::Position, reader::CharacterReader};

#[cfg_attr(not(test), derive(Debug))]
pub struct LeekToken {
    kind: LeekTokenKind,
    text: String,
    start: Position,
    end: Position,
}

impl LeekToken {
    fn is_keyword(word: &str) -> bool {
        match word {
            "fn" | "leak" | "hold" | "if" | "else" | "while" | "for" | "yeet" => true,
            _ => false,
        }
    }
}

impl<T> From<(LeekTokenKind, T)> for LeekToken
where
    T: Into<String> + Sized,
{
    fn from((kind, text): (LeekTokenKind, T)) -> Self {
        Self {
            kind,
            text: text.into(),
            start: Position::new(),
            end: Position::new(),
        }
    }
}

#[cfg(test)]
impl Debug for LeekToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeekToken")
            .field("kind", &self.kind)
            .field("text", &self.text)
            .finish()
    }
}

impl PartialEq for LeekToken {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.text == other.text
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum IntegerLiteralKind {
    Decimal,
    Hexadecimal,
    Binary,
    Octal,
}

#[derive(Debug, Eq, PartialEq)]
pub enum LeekTokenKind {
    // Words
    Keyword,    // leak
    Identifier, // YourMom

    // Grouping
    OpenParen,         // (
    CloseParen,        // )
    OpenBracket,       // [
    CloseBracket,      // ]
    OpenCurlyBracket,  // {
    CloseCurlyBracket, // }

    // Literals
    StringLiteral,                      // "your mom"
    CharLiteral,                        // 'd'
    IntegerLiteral(IntegerLiteralKind), // 69
    FloatLiteral,                       // 420.69

    // Single Operators
    Equals,             // =
    DoubleEquals,       // ==
    LessThan,           // <
    LessThanOrEqual,    // <=
    GreaterThan,        // >
    GreaterThanOrEqual, // >=
    Plus,               // +
    PlusEquals,         // +=
    Minus,              // -
    MinusEquals,        // -=
    Asterisk,           // *
    MultiplyEquals,     // *=
    Divide,             // /
    DivideEquals,       // /=
    Modulo,             // %
    ModuloEquals,       // %=
    BitwiseNot,         // ~
    BitwiseNotEquals,   // ~=
    BitwiseXor,         // ^
    BitwiseXorEquals,   // ^=
    BitwiseOr,          // |
    BitwiseOrEquals,    // |=
    BitwiseAnd,         // &
    BitwiseAndEquals,   // &=
    LogicalNot,         // !
    LogicalNotEquals,   // !=

    // Double Operators
    Exponentiation,       // **
    ExponentiationEquals, // **=
    LeftShift,            // <<
    LeftShiftEquals,      // <<=
    RightShift,           // >>
    RightShiftEquals,     // >>=
    LogicalOr,            // ||
    LogicalOrEquals,      // ||=
    LogicalAnd,           // &&
    LogicalAndEquals,     // &&=

    // Non-Operator symbols
    Arrow,          // ->
    QuestionMark,   // ?
    Comma,          // ,
    Semicolon,      // ;
    Colon,          // :
    DoubleColon,    // ::
    Period,         // .
    BangCoalescing, // !.
    BackSlash,      // \
    Underscore,     // _
    Asperand,       // @
    Hash,           // #
    DollarSign,     // $
}

impl LeekTokenKind {
    fn grouping_symbol_from(c: char) -> LeekTokenKind {
        match c {
            '(' => Self::OpenParen,
            ')' => Self::CloseParen,
            '[' => Self::OpenBracket,
            ']' => Self::CloseBracket,
            '{' => Self::OpenCurlyBracket,
            '}' => Self::CloseCurlyBracket,
            x => unreachable!("Illegal non-grouping symbol `{}`", x),
        }
    }

    fn single_operator_from(c: char) -> LeekTokenKind {
        match c {
            '=' => Self::Equals,
            '<' => Self::LessThan,
            '>' => Self::GreaterThan,
            '!' => Self::LogicalNot,
            '+' => Self::Plus,
            '-' => Self::Minus,
            '*' => Self::Asterisk,
            '/' => Self::Divide,
            '%' => Self::Modulo,
            '~' => Self::BitwiseNot,
            '^' => Self::BitwiseXor,
            '|' => Self::BitwiseOr,
            '&' => Self::BitwiseAnd,
            x => unreachable!("Illegal single non-operator `{}`", x),
        }
    }

    fn double_operator_from(c: char) -> LeekTokenKind {
        match c {
            '*' => Self::Exponentiation,
            '<' => Self::LeftShift,
            '>' => Self::RightShift,
            '&' => Self::LogicalAnd,
            '|' => Self::LogicalOr,
            x => unreachable!("Illegal double non-operator `{}`", x),
        }
    }

    fn single_equals_operator_from(c: char) -> LeekTokenKind {
        match c {
            '=' => Self::DoubleEquals,
            '<' => Self::LessThanOrEqual,
            '>' => Self::GreaterThanOrEqual,
            '!' => Self::LogicalNotEquals,
            '+' => Self::PlusEquals,
            '-' => Self::MinusEquals,
            '*' => Self::MultiplyEquals,
            '/' => Self::DivideEquals,
            '%' => Self::ModuloEquals,
            '~' => Self::BitwiseNotEquals,
            '^' => Self::BitwiseXorEquals,
            '|' => Self::BitwiseOrEquals,
            '&' => Self::BitwiseAndEquals,
            x => unreachable!("Illegal single non-equals-operator `{}`", x),
        }
    }

    fn double_equals_operator_from(c: char) -> LeekTokenKind {
        match c {
            '*' => Self::ExponentiationEquals,
            '<' => Self::LeftShiftEquals,
            '>' => Self::RightShiftEquals,
            '&' => Self::LogicalAndEquals,
            '|' => Self::LogicalOrEquals,
            x => unreachable!("Illegal double non-equals-operator `{}`", x),
        }
    }

    fn other_symbol_from(c: impl Into<String>) -> LeekTokenKind {
        match c.into().as_str() {
            "->" => Self::Arrow,
            "?" => Self::QuestionMark,
            "!." => Self::BangCoalescing,
            "," => Self::Comma,
            ";" => Self::Semicolon,
            ":" => Self::Colon,
            "::" => Self::DoubleColon,
            "." => Self::Period,
            "\\" => Self::BackSlash,
            "_" => Self::Underscore,
            "@" => Self::Asperand,
            "#" => Self::Hash,
            "$" => Self::DollarSign,
            x => unreachable!("Illegal non-other-symbol `{}`", x),
        }
    }
}

/// Represents an error when lexing a file
#[derive(Debug)]
pub struct LexerError {
    kind: LexerErrorKind,
    contents: String,
    position: Position,
}

impl PartialEq for LexerError {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl From<LexerErrorKind> for LexerError {
    fn from(kind: LexerErrorKind) -> Self {
        LexerError {
            kind,
            contents: String::new(),
            position: Position::new(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum LexerErrorKind {
    UnexpectedChar(char),
    UnclosedWrappedLiteral(LeekTokenKind),
    UnexpectedEndOfFloatLiteral,
    UnexpectedCharactersInFloatLiteral,
    UnexpectedExtraPeriodInFloatLiteral,
    UnexpectedEndOfIntegerLiteral(IntegerLiteralKind),
    UnexpectedCharactersInIntegerLiteral(IntegerLiteralKind),
}

impl Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.position)?;

        let lines: Vec<_> = self.contents.lines().collect();

        // Print the lines around and including the one with the error
        let start = if self.position.row < 2 {
            0
        } else {
            self.position.row - 2
        } as usize;

        // Print each line and the line number
        for (n, line) in lines[start..(self.position.row + 1) as usize]
            .iter()
            .enumerate()
        {
            writeln!(f, "{:>3}: {}", n + start + 1, line)?;
        }

        // Print the space before the highlight
        for _ in 0..self.position.col + 5 {
            write!(f, " ")?;
        }

        // Print the underline highlight
        writeln!(f, "^")?;

        // Print the space before "here"
        for _ in 0..self.position.col + 5 {
            write!(f, " ")?;
        }

        writeln!(f, "{}", "here")?;
        writeln!(f)?;

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
        }
    }
}

/// Represents a generic Lexer object
pub trait Lexer {
    fn next(&mut self) -> Result<Option<LeekToken>, LexerError>;
    fn has_next(&mut self) -> Result<bool, LexerError>;
    fn peek(&mut self) -> Result<Option<&LeekToken>, LexerError>;
    fn peek_nth(&mut self, n: usize) -> Result<Option<&LeekToken>, LexerError>;
}

/// Defines a specific Lexer for Leek
///
/// This lexer implementation uses a "lazy" iterator approach such
/// that characters are not read from the input stream until a token is requested.
pub struct LeekLexer {
    character_reader: Box<dyn CharacterReader>,
    peek_forward: VecDeque<LeekToken>,
}

impl LeekLexer {
    pub fn new(character_reader: impl CharacterReader + 'static) -> Self {
        LeekLexer {
            character_reader: Box::new(character_reader),
            peek_forward: VecDeque::new(),
        }
    }

    /// Read a literal that is wrapped in the provided character
    /// The wrapper character can be escaped using the backslash character `\`
    fn read_wrapped_escapable(
        &mut self,
        wrapper: char,
        kind: LeekTokenKind,
    ) -> Result<LeekToken, LexerError> {
        let mut text = String::new();
        let start = self.character_reader.get_position().clone();

        macro_rules! get_next_char {
            () => {
                if let Some(c) = self.character_reader.next() {
                    c
                } else {
                    return Err(LexerError {
                        kind: LexerErrorKind::UnclosedWrappedLiteral(kind),
                        contents: self.character_reader.get_contents().to_owned(),
                        position: self.character_reader.get_position().clone(),
                    });
                }
            };
        }

        macro_rules! peek_nth_char {
            ($n:expr) => {
                if let Some(c) = self.character_reader.peek_nth($n) {
                    c
                } else {
                    return Err(LexerError {
                        kind: LexerErrorKind::UnclosedWrappedLiteral(kind),
                        contents: self.character_reader.get_contents().to_owned(),
                        position: self.character_reader.get_position().clone(),
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

        let end = self.character_reader.get_position().clone();

        Ok(LeekToken {
            kind,
            text,
            start,
            end,
        })
    }

    /// Reads a generic number literal into either an integer or double
    fn read_number_literal(&mut self) -> Result<LeekToken, LexerError> {
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

        // Look ahead to match different literal types
        return 'number: {
            if *self.character_reader.peek().unwrap() == '0' {
                let Some(c) = self.character_reader.peek_nth(1) else {
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
        &mut self,
        literal_kind: IntegerLiteralKind,
        is_in_base: fn(char) -> bool,
    ) -> Result<LeekToken, LexerError> {
        macro_rules! create_error {
            ($kind:expr) => {
                LexerError {
                    kind: $kind,
                    contents: self.character_reader.get_contents().to_owned(),
                    position: self.character_reader.get_position().clone(),
                }
            };
        }

        macro_rules! get_next_char {
            () => {
                self.character_reader.next().ok_or_else(|| LexerError {
                    kind: LexerErrorKind::UnexpectedEndOfIntegerLiteral(literal_kind),
                    contents: self.character_reader.get_contents().to_owned(),
                    position: self.character_reader.get_position().clone(),
                })?
            };
        }

        let start = self.character_reader.get_position().clone();

        let mut text = String::new();

        // `0`
        text.push(get_next_char!());
        // special boundary
        text.push(get_next_char!());

        while self.character_reader.has_next() {
            let peeked_char = *self.character_reader.peek().unwrap();

            if peeked_char == '_' {
                // Ignore underscores
                self.character_reader.next().unwrap();
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

        let end = self.character_reader.get_position().clone();

        Ok(LeekToken {
            kind: LeekTokenKind::IntegerLiteral(literal_kind),
            text,
            start,
            end,
        })
    }

    fn read_dec_int_or_float_literal(&mut self) -> Result<LeekToken, LexerError> {
        enum NumberLexingState {
            Integer,
            Float,
        }

        let mut state = NumberLexingState::Integer;

        macro_rules! create_error {
            ($kind:expr) => {
                LexerError {
                    kind: $kind,
                    contents: self.character_reader.get_contents().to_owned(),
                    position: self.character_reader.get_position().clone(),
                }
            };
        }

        macro_rules! get_next_char {
            () => {
                self.character_reader.next().ok_or_else(|| LexerError {
                    kind: match state {
                        NumberLexingState::Integer => {
                            LexerErrorKind::UnexpectedEndOfIntegerLiteral(
                                IntegerLiteralKind::Decimal,
                            )
                        }
                        NumberLexingState::Float => LexerErrorKind::UnexpectedEndOfFloatLiteral,
                    },
                    contents: self.character_reader.get_contents().to_owned(),
                    position: self.character_reader.get_position().clone(),
                })?
            };
        }

        let start = self.character_reader.get_position().clone();

        let mut text = String::new();

        // first char
        text.push(get_next_char!());

        while self.character_reader.has_next() {
            let peeked_char = *self.character_reader.peek().unwrap();

            match peeked_char {
                // Ignore underscores
                '_' => {
                    self.character_reader.next().unwrap();
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
            if text.ends_with(".") {
                return Err(create_error!(LexerErrorKind::UnexpectedEndOfFloatLiteral));
            }
        }

        let end = self.character_reader.get_position().clone();

        Ok(LeekToken {
            kind: match state {
                NumberLexingState::Integer => {
                    LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Decimal)
                }
                NumberLexingState::Float => LeekTokenKind::FloatLiteral,
            },
            text,
            start,
            end,
        })
    }

    /// Advance the lexer while the next character matches the predicate, and return the resulting string
    fn read_while(&mut self, predicate: fn(char) -> bool) -> String {
        let mut res = String::new();

        while self.character_reader.has_next() {
            let c = self.character_reader.peek().unwrap();

            if !predicate(*c) {
                return res;
            }

            res.push(self.character_reader.next().unwrap());
        }

        res
    }

    /// Advance the lexer while the next character matches the predicate, and discard the matched chars
    fn ignore_while(&mut self, predicate: fn(char) -> bool) {
        while self.character_reader.has_next() {
            let c = self.character_reader.peek().unwrap();

            if !predicate(*c) {
                return;
            }

            self.character_reader.next();
        }
    }

    /// Advance the lexer until the next non-whitespace character
    fn ignore_whitespace(&mut self) {
        self.ignore_while(|c| c.is_ascii_whitespace())
    }

    /// Requires character to be available
    fn read_single(&mut self, kind: LeekTokenKind) -> LeekToken {
        let start = self.character_reader.get_position().clone();
        let c = self.character_reader.next().unwrap();
        let end = self.character_reader.get_position().clone();

        LeekToken {
            kind,
            text: c.into(),
            start,
            end,
        }
    }

    /// Peeks the character reader several chars forward to look for a char sequence
    fn lookahead_has(&mut self, string: &str, n: usize) -> bool {
        let chars = string.chars();

        for (i, c) in chars.enumerate() {
            let Some(peeked) = self.character_reader.peek_nth(n + i) else {
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
    fn read_multi(&mut self, string: &str, kind: LeekTokenKind) -> LeekToken {
        let mut text = String::new();
        let start = self.character_reader.get_position().clone();

        for expected_char in string.chars() {
            if !self.character_reader.has_next() {
                unreachable!("Not enough chars in character_reader (should be checked in advance)")
            }

            let c = self.character_reader.peek().unwrap();

            if *c != expected_char {
                unreachable!(
                    "Char from character_reader did not match (should be checked in advance)"
                )
            }

            text.push(self.character_reader.next().unwrap());
        }

        let end = self.character_reader.get_position().clone();

        LeekToken {
            kind,
            text,
            start,
            end,
        }
    }

    /// Looks ahead to see if there is an `=` following the given prefix
    fn lookahead_has_equals(&mut self, prefix: impl Into<String>, n: usize) -> bool {
        let mut c: String = prefix.into();
        c.push('=');

        self.lookahead_has(&c, n)
    }

    /// Reads a fixed number of chars with an `=` suffixed to the given prefix from the character reader and returns the resulting token
    ///
    /// Requires that the character reader be checked in advance to contain the correct sequence
    fn read_multi_equals(&mut self, prefix: impl Into<String>, kind: LeekTokenKind) -> LeekToken {
        let mut c: String = prefix.into();
        c.push('=');

        self.read_multi(&c, kind)
    }

    fn read_single_operator(
        &mut self,
        c: char,
        single: LeekTokenKind,
        equals: LeekTokenKind,
    ) -> LeekToken {
        if self.lookahead_has_equals(c, 0) {
            self.read_multi_equals(c, equals)
        } else {
            self.read_single(single)
        }
    }

    fn read_double_operator(
        &mut self,
        c: char,
        normal: LeekTokenKind,
        equals: LeekTokenKind,
    ) -> LeekToken {
        if self.lookahead_has_equals(c, 1) {
            self.read_multi_equals(&c.to_string().repeat(2), equals)
        } else {
            self.read_multi(&c.to_string().repeat(2), normal)
        }
    }
}

impl Lexer for LeekLexer {
    fn next(&mut self) -> Result<Option<LeekToken>, LexerError> {
        // Check if more tokens have already been precomputed for us
        if !self.peek_forward.is_empty() {
            // Always returns `Some`
            return Ok(self.peek_forward.pop_front());
        }

        while self.character_reader.has_next() {
            let start = self.character_reader.get_position().clone();

            // SAFETY: always checking if more characters are available before unwrapping
            let first_char = *self.character_reader.peek().unwrap();

            return Ok(Some(match first_char {
                // Whitespace
                a if a.is_ascii_whitespace() => {
                    self.ignore_whitespace();
                    continue;
                }

                // Chop Comments
                '/' if self.character_reader.peek_nth(1).is_some_and(|c| *c == '/') => {
                    self.ignore_while(|c| c != '\n');
                    continue;
                }

                // Words
                a if a.is_ascii_alphabetic() => {
                    let word = self.read_while(|c| c.is_ascii_alphanumeric());

                    LeekToken {
                        kind: if LeekToken::is_keyword(&word) {
                            LeekTokenKind::Keyword
                        } else {
                            LeekTokenKind::Identifier
                        },
                        text: word,
                        start,
                        end: self.character_reader.get_position().clone(),
                    }
                }

                // Literals
                '"' => self.read_wrapped_escapable('"', LeekTokenKind::StringLiteral)?,
                '\'' => self.read_wrapped_escapable('\'', LeekTokenKind::CharLiteral)?,
                a if a.is_ascii_digit() => self.read_number_literal()?,

                // Grouping Symbols
                c @ ('(' | ')' | '[' | ']' | '{' | '}') => {
                    self.read_single(LeekTokenKind::grouping_symbol_from(c))
                }

                // Arrows (`->`)
                '-' if self.character_reader.peek_nth(1).is_some_and(|c| *c == '>') => {
                    self.read_multi("->", LeekTokenKind::Arrow)
                }

                // Bang Coalescing (`!.`)
                '!' if self.character_reader.peek_nth(1).is_some_and(|c| *c == '.') => {
                    self.read_multi("!.", LeekTokenKind::BangCoalescing)
                }

                // Double Colon (`::`)
                ':' if self.character_reader.peek_nth(1).is_some_and(|c| *c == ':') => {
                    self.read_multi("::", LeekTokenKind::DoubleColon)
                }

                // Double operators (must come first because of lookahead clash)
                c @ ('*' | '&' | '|' | '>' | '<')
                    if self.character_reader.peek_nth(1).is_some_and(|x| *x == c) =>
                {
                    self.read_double_operator(
                        c,
                        LeekTokenKind::double_operator_from(c),
                        LeekTokenKind::double_equals_operator_from(c),
                    )
                }

                // Single Operators
                c @ ('=' | '<' | '>' | '+' | '-' | '*' | '/' | '%' | '~' | '!' | '&' | '|'
                | '^') => self.read_single_operator(
                    c,
                    LeekTokenKind::single_operator_from(c),
                    LeekTokenKind::single_equals_operator_from(c),
                ),

                // Non-Operator symbols
                c @ ('?' | ',' | ';' | ':' | '.' | '\\' | '_' | '@' | '#' | '$') => {
                    self.read_single(LeekTokenKind::other_symbol_from(c))
                }

                // Other
                c => {
                    return Err(LexerError {
                        kind: LexerErrorKind::UnexpectedChar(c),
                        contents: self.character_reader.get_contents().clone(),
                        position: self.character_reader.get_position().clone(),
                    })
                }
            }));
        }

        // If got to the end of the cursor without finding any more tokens,
        // then we will never return more tokens
        Ok(None)
    }

    fn peek(&mut self) -> Result<Option<&LeekToken>, LexerError> {
        // Check if more tokens have already been precomputed for us
        if !self.peek_forward.is_empty() {
            // Always returns `Some`
            return Ok(self.peek_forward.front());
        }

        // If there are more tokens
        if let Some(token) = self.next()? {
            // Store the token for later usage
            self.peek_forward.push_back(token);

            // Return a reference to the token
            Ok(self.peek_forward.front())
        } else {
            // Otherwise, return None since there are no tokens to peek
            Ok(None)
        }
    }

    fn peek_nth(&mut self, n: usize) -> Result<Option<&LeekToken>, LexerError> {
        // Check if `n` tokens have already been precomputed for us
        if !self.peek_forward.len() >= n {
            // Always returns `Some`
            return Ok(self.peek_forward.get(n));
        }

        // Otherwise, precompute the next `n` tokens from the amount we've already computed
        for _ in self.peek_forward.len()..=n {
            // Get the next token or return early if none more are found
            let Some(token) = self.next()? else {
                return Ok(None);
            };

            // Store the token for later usage
            self.peek_forward.push_back(token);
        }

        // Always returns `Some` because we would not have completed the loop otherwise.
        Ok(self.peek_forward.get(n))
    }

    fn has_next(&mut self) -> Result<bool, LexerError> {
        Ok(self.peek()?.is_some())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        lexer::{IntegerLiteralKind::*, LeekToken as LT, LeekTokenKind::*},
        reader::FileReader,
    };

    use super::{LeekLexer, Lexer, LexerError, LexerErrorKind::*};

    fn compare_input_to_expected(input: &str, expected_tokens: Vec<LT>) {
        // Collect tokens from lexer
        let reader = FileReader::from(input.to_owned());
        let mut lexer = LeekLexer::new(reader);

        let mut lexer_tokens = Vec::new();

        while lexer.has_next().unwrap() {
            lexer_tokens.push(lexer.next().unwrap().unwrap())
        }

        assert_eq!(
            lexer_tokens, expected_tokens,
            "Lexer tokens did not match expected"
        )
    }

    fn lex_input(input: &str) -> Result<Vec<LT>, LexerError> {
        // Collect tokens from lexer
        let reader = FileReader::from(input.to_owned());
        let mut lexer = LeekLexer::new(reader);

        let mut lexer_tokens = Vec::new();

        while lexer.has_next()? {
            lexer_tokens.push(lexer.next()?.unwrap())
        }

        Ok(lexer_tokens)
    }

    #[test]
    fn basic_example() {
        compare_input_to_expected(
            r#"
                fn main() {       
                    leak node = Node()
                
                    println()
                    
                }
            "#,
            vec![
                LT::from((Keyword, "fn")),
                LT::from((Identifier, "main")),
                LT::from((OpenParen, "(")),
                LT::from((CloseParen, ")")),
                LT::from((OpenCurlyBracket, "{")),
                LT::from((Keyword, "leak")),
                LT::from((Identifier, "node")),
                LT::from((Equals, "=")),
                LT::from((Identifier, "Node")),
                LT::from((OpenParen, "(")),
                LT::from((CloseParen, ")")),
                LT::from((Identifier, "println")),
                LT::from((OpenParen, "(")),
                LT::from((CloseParen, ")")),
                LT::from((CloseCurlyBracket, "}")),
            ],
        )
    }

    #[test]
    fn removes_comments() {
        compare_input_to_expected(
            r#"
                // this is a comment
                fn main() { // this is a comment       
                    leak node = Node()
                    // this is a comment
                    println()
                    // this is a comment
                }// this is a comment
            "#,
            vec![
                LT::from((Keyword, "fn")),
                LT::from((Identifier, "main")),
                LT::from((OpenParen, "(")),
                LT::from((CloseParen, ")")),
                LT::from((OpenCurlyBracket, "{")),
                LT::from((Keyword, "leak")),
                LT::from((Identifier, "node")),
                LT::from((Equals, "=")),
                LT::from((Identifier, "Node")),
                LT::from((OpenParen, "(")),
                LT::from((CloseParen, ")")),
                LT::from((Identifier, "println")),
                LT::from((OpenParen, "(")),
                LT::from((CloseParen, ")")),
                LT::from((CloseCurlyBracket, "}")),
            ],
        )
    }

    #[test]
    fn basic_single_operators() {
        compare_input_to_expected(
            r#"= == < <= > >= + += - -= * *= / /= % %= ~ ~= ^ ^= | |= & &= ! !="#,
            vec![
                LT::from((Equals, "=")),
                LT::from((DoubleEquals, "==")),
                LT::from((LessThan, "<")),
                LT::from((LessThanOrEqual, "<=")),
                LT::from((GreaterThan, ">")),
                LT::from((GreaterThanOrEqual, ">=")),
                LT::from((Plus, "+")),
                LT::from((PlusEquals, "+=")),
                LT::from((Minus, "-")),
                LT::from((MinusEquals, "-=")),
                LT::from((Asterisk, "*")),
                LT::from((MultiplyEquals, "*=")),
                LT::from((Divide, "/")),
                LT::from((DivideEquals, "/=")),
                LT::from((Modulo, "%")),
                LT::from((ModuloEquals, "%=")),
                LT::from((BitwiseNot, "~")),
                LT::from((BitwiseNotEquals, "~=")),
                LT::from((BitwiseXor, "^")),
                LT::from((BitwiseXorEquals, "^=")),
                LT::from((BitwiseOr, "|")),
                LT::from((BitwiseOrEquals, "|=")),
                LT::from((BitwiseAnd, "&")),
                LT::from((BitwiseAndEquals, "&=")),
                LT::from((LogicalNot, "!")),
                LT::from((LogicalNotEquals, "!=")),
            ],
        )
    }

    #[test]
    fn basic_double_operators() {
        compare_input_to_expected(
            r#"** **= << <<= >> >>= || ||= && &&="#,
            vec![
                LT::from((Exponentiation, "**")),
                LT::from((ExponentiationEquals, "**=")),
                LT::from((LeftShift, "<<")),
                LT::from((LeftShiftEquals, "<<=")),
                LT::from((RightShift, ">>")),
                LT::from((RightShiftEquals, ">>=")),
                LT::from((LogicalOr, "||")),
                LT::from((LogicalOrEquals, "||=")),
                LT::from((LogicalAnd, "&&")),
                LT::from((LogicalAndEquals, "&&=")),
            ],
        )
    }

    #[test]
    fn double_non_operators() {
        compare_input_to_expected(
            r#"-> ->=-> - >"#,
            vec![
                LT::from((Arrow, "->")),
                LT::from((Arrow, "->")),
                LT::from((Equals, "=")),
                LT::from((Arrow, "->")),
                LT::from((Minus, "-")),
                LT::from((GreaterThan, ">")),
            ],
        )
    }

    #[test]
    fn simple_string() {
        compare_input_to_expected(
            r#" "your mom 1""your mom 2" "your mom 3" "#,
            vec![
                LT::from((StringLiteral, r#""your mom 1""#)),
                LT::from((StringLiteral, r#""your mom 2""#)),
                LT::from((StringLiteral, r#""your mom 3""#)),
            ],
        )
    }

    #[test]
    fn string_quote_escapes() {
        compare_input_to_expected(
            r#" "your mom \"1\"" "your mom 2" "#,
            vec![
                LT::from((StringLiteral, r#""your mom \"1\"""#)),
                LT::from((StringLiteral, r#""your mom 2""#)),
            ],
        )
    }

    #[test]
    fn unclosed_string() {
        assert_eq!(
            lex_input(r#" "this is a string that doesn't have a closing double quote"#),
            Err(LexerError::from(UnclosedWrappedLiteral(StringLiteral)))
        )
    }

    #[test]
    fn simple_chars() {
        compare_input_to_expected(
            r" 'a''b' 'c' ",
            vec![
                LT::from((CharLiteral, r"'a'")),
                LT::from((CharLiteral, r"'b'")),
                LT::from((CharLiteral, r"'c'")),
            ],
        )
    }

    #[test]
    fn char_escapes() {
        compare_input_to_expected(
            r" 'a''b' '\'' ",
            vec![
                LT::from((CharLiteral, r"'a'")),
                LT::from((CharLiteral, r"'b'")),
                LT::from((CharLiteral, r"'\''")),
            ],
        )
    }

    #[test]
    fn unclosed_char() {
        assert_eq!(
            lex_input(r#" 'a"#),
            Err(LexerError::from(UnclosedWrappedLiteral(CharLiteral)))
        )
    }

    #[test]
    fn basic_hex_literal() {
        compare_input_to_expected(
            "0xFFFF 0x123456789ABCDEF 0x01234567",
            vec![
                LT::from((IntegerLiteral(Hexadecimal), "0xFFFF")),
                LT::from((IntegerLiteral(Hexadecimal), "0x123456789ABCDEF")),
                LT::from((IntegerLiteral(Hexadecimal), "0x01234567")),
            ],
        )
    }

    #[test]
    fn underscores_in_hex_literal() {
        compare_input_to_expected(
            "0x__FF__F_F 0x_1_2_3456_789AB_CDE_F_ 0x_01_23_45_67",
            vec![
                LT::from((IntegerLiteral(Hexadecimal), "0xFFFF")),
                LT::from((IntegerLiteral(Hexadecimal), "0x123456789ABCDEF")),
                LT::from((IntegerLiteral(Hexadecimal), "0x01234567")),
            ],
        )
    }

    #[test]
    fn unexpected_end_of_hex() {
        assert_eq!(
            lex_input(r"0x"),
            Err(LexerError::from(UnexpectedEndOfIntegerLiteral(Hexadecimal)))
        )
    }

    #[test]
    fn illegal_hex_chars() {
        assert_eq!(
            lex_input(r"0xasdfgh"),
            Err(LexerError::from(UnexpectedCharactersInIntegerLiteral(
                Hexadecimal
            )))
        )
    }

    #[test]
    fn hex_literal_on_boundary() {
        compare_input_to_expected(
            "(0x42069)",
            vec![
                LT::from((OpenParen, "(")),
                LT::from((IntegerLiteral(Hexadecimal), "0x42069")),
                LT::from((CloseParen, ")")),
            ],
        )
    }

    #[test]
    fn basic_bin_literal() {
        compare_input_to_expected(
            "0b00010011 0b111010100001 0b0",
            vec![
                LT::from((IntegerLiteral(Binary), "0b00010011")),
                LT::from((IntegerLiteral(Binary), "0b111010100001")),
                LT::from((IntegerLiteral(Binary), "0b0")),
            ],
        )
    }

    #[test]
    fn underscores_in_bin_literal() {
        compare_input_to_expected(
            "0b_00_0_100_11 0b1_1_101_01000_01_ 0b_0_",
            vec![
                LT::from((IntegerLiteral(Binary), "0b00010011")),
                LT::from((IntegerLiteral(Binary), "0b111010100001")),
                LT::from((IntegerLiteral(Binary), "0b0")),
            ],
        )
    }

    #[test]
    fn unexpected_end_of_bin() {
        assert_eq!(
            lex_input(r"0b"),
            Err(LexerError::from(UnexpectedEndOfIntegerLiteral(Binary)))
        )
    }

    #[test]
    fn illegal_bin_chars() {
        assert_eq!(
            lex_input(r"0b101a"),
            Err(LexerError::from(UnexpectedCharactersInIntegerLiteral(
                Binary
            )))
        )
    }

    #[test]
    fn bin_literal_on_boundary() {
        compare_input_to_expected(
            "(0b01000101)",
            vec![
                LT::from((OpenParen, "(")),
                LT::from((IntegerLiteral(Binary), "0b01000101")),
                LT::from((CloseParen, ")")),
            ],
        )
    }

    #[test]
    fn basic_oct_literal() {
        compare_input_to_expected(
            "0o01234567 0o161343 0o00000001",
            vec![
                LT::from((IntegerLiteral(Octal), "0o01234567")),
                LT::from((IntegerLiteral(Octal), "0o161343")),
                LT::from((IntegerLiteral(Octal), "0o00000001")),
            ],
        )
    }

    #[test]
    fn underscores_in_oct_literal() {
        compare_input_to_expected(
            "0o01_234_56_7 0o_16134_3 0o000_00001_",
            vec![
                LT::from((IntegerLiteral(Octal), "0o01234567")),
                LT::from((IntegerLiteral(Octal), "0o161343")),
                LT::from((IntegerLiteral(Octal), "0o00000001")),
            ],
        )
    }

    #[test]
    fn unexpected_end_of_oct() {
        assert_eq!(
            lex_input(r"0o"),
            Err(LexerError::from(UnexpectedEndOfIntegerLiteral(Octal)))
        )
    }

    #[test]
    fn illegal_oct_chars() {
        assert_eq!(
            lex_input(r"0o1234567890abcdef"),
            Err(LexerError::from(UnexpectedCharactersInIntegerLiteral(
                Octal
            )))
        )
    }

    #[test]
    fn oct_literal_on_boundary() {
        compare_input_to_expected(
            "(0o420)",
            vec![
                LT::from((OpenParen, "(")),
                LT::from((IntegerLiteral(Octal), "0o420")),
                LT::from((CloseParen, ")")),
            ],
        )
    }

    #[test]
    fn basic_dec_literal() {
        compare_input_to_expected(
            "123456789 1 0 2",
            vec![
                LT::from((IntegerLiteral(Decimal), "123456789")),
                LT::from((IntegerLiteral(Decimal), "1")),
                LT::from((IntegerLiteral(Decimal), "0")),
                LT::from((IntegerLiteral(Decimal), "2")),
            ],
        )
    }

    #[test]
    fn underscores_in_dec_literal() {
        compare_input_to_expected(
            "1234_5_6789 1_ 0 2_2",
            vec![
                LT::from((IntegerLiteral(Decimal), "123456789")),
                LT::from((IntegerLiteral(Decimal), "1")),
                LT::from((IntegerLiteral(Decimal), "0")),
                LT::from((IntegerLiteral(Decimal), "22")),
            ],
        )
    }

    #[test]
    fn illegal_dec_chars() {
        assert_eq!(
            lex_input(r"0123456789abcdef"),
            Err(LexerError::from(UnexpectedCharactersInIntegerLiteral(
                Decimal
            )))
        )
    }

    #[test]
    fn dec_literal_on_boundary() {
        compare_input_to_expected(
            "(69)",
            vec![
                LT::from((OpenParen, "(")),
                LT::from((IntegerLiteral(Decimal), "69")),
                LT::from((CloseParen, ")")),
            ],
        )
    }

    #[test]
    fn basic_float_literal() {
        compare_input_to_expected(
            "0.0 0.1 1.0 420.69",
            vec![
                LT::from((FloatLiteral, "0.0")),
                LT::from((FloatLiteral, "0.1")),
                LT::from((FloatLiteral, "1.0")),
                LT::from((FloatLiteral, "420.69")),
            ],
        )
    }

    #[test]
    fn underscores_in_float_literal() {
        compare_input_to_expected(
            "0_.0 0._1 1.0 1337_420.69",
            vec![
                LT::from((FloatLiteral, "0.0")),
                LT::from((FloatLiteral, "0.1")),
                LT::from((FloatLiteral, "1.0")),
                LT::from((FloatLiteral, "1337420.69")),
            ],
        )
    }

    #[test]
    fn illegal_float_chars() {
        assert_eq!(
            lex_input(r"420.a69"),
            Err(LexerError::from(UnexpectedCharactersInFloatLiteral))
        );

        assert_eq!(
            lex_input(r"420.6s9"),
            Err(LexerError::from(UnexpectedCharactersInFloatLiteral))
        );
    }

    #[test]
    fn float_literal_on_boundary() {
        compare_input_to_expected(
            "(420.69)",
            vec![
                LT::from((OpenParen, "(")),
                LT::from((FloatLiteral, "420.69")),
                LT::from((CloseParen, ")")),
            ],
        )
    }

    #[test]
    fn float_double_period() {
        assert_eq!(
            lex_input(r"420.69.1337"),
            Err(LexerError::from(UnexpectedExtraPeriodInFloatLiteral))
        );
    }

    #[test]
    fn flaot_end_with_period() {
        assert_eq!(
            lex_input(r"420."),
            Err(LexerError::from(UnexpectedEndOfFloatLiteral))
        );
    }
}
