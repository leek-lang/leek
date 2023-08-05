#![cfg(test)]

use crate::{
    frontend::lexer::{IntegerLiteralKind::*, KeywordKind::*, Token as LT, TokenKind::*},
    frontend::reader::FileReader,
};

use super::{Lexer, LexerError, LexerErrorKind::*};

fn compare_input_to_expected(input: &str, expected_tokens: Vec<LT>) {
    // Collect tokens from lexer
    let reader = FileReader::from(input.to_owned());
    let mut lexer = Lexer::new(reader);

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
    let mut lexer = Lexer::new(reader);

    let mut lexer_tokens = Vec::new();

    while lexer.has_next()? {
        lexer_tokens.push(lexer.next()?.unwrap())
    }

    Ok(lexer_tokens)
}

#[test]
fn basic_example() {
    compare_input_to_expected(
        r#"fn main() {       
                leak node = Node()
            
                println()
            }"#,
        vec![
            LT::from((Keyword(Fn), "fn")),
            LT::from((Identifier, "main")),
            LT::from((OpenParen, "(")),
            LT::from((CloseParen, ")")),
            LT::from((OpenCurlyBracket, "{")),
            LT::from((Newline, "\n")),
            LT::from((Keyword(Leak), "leak")),
            LT::from((Identifier, "node")),
            LT::from((Equals, "=")),
            LT::from((Identifier, "Node")),
            LT::from((OpenParen, "(")),
            LT::from((CloseParen, ")")),
            LT::from((Newline, "\n")),
            LT::from((Newline, "\n")),
            LT::from((Identifier, "println")),
            LT::from((OpenParen, "(")),
            LT::from((CloseParen, ")")),
            LT::from((Newline, "\n")),
            LT::from((CloseCurlyBracket, "}")),
        ],
    )
}

#[test]
fn removes_comments() {
    compare_input_to_expected(
        r#"// this is a comment
            fn main() { // this is a comment       
                leak node = Node()
                // this is a comment
                println()
                // this is a comment
            }// this is a comment"#,
        vec![
            LT::from((Newline, "\n")),
            LT::from((Keyword(Fn), "fn")),
            LT::from((Identifier, "main")),
            LT::from((OpenParen, "(")),
            LT::from((CloseParen, ")")),
            LT::from((OpenCurlyBracket, "{")),
            LT::from((Newline, "\n")),
            LT::from((Keyword(Leak), "leak")),
            LT::from((Identifier, "node")),
            LT::from((Equals, "=")),
            LT::from((Identifier, "Node")),
            LT::from((OpenParen, "(")),
            LT::from((CloseParen, ")")),
            LT::from((Newline, "\n")),
            LT::from((Newline, "\n")),
            LT::from((Identifier, "println")),
            LT::from((OpenParen, "(")),
            LT::from((CloseParen, ")")),
            LT::from((Newline, "\n")),
            LT::from((Newline, "\n")),
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
fn float_end_with_period() {
    assert_eq!(
        lex_input(r"420."),
        Err(LexerError::from(UnexpectedEndOfFloatLiteral))
    );
}