use std::fmt::Display;

use crate::{
    lexer::{LeekToken, LeekTokenKind, Lexer},
    position::Span,
};

#[derive(Debug, PartialEq)]
pub enum ParseTreeNode {
    Terminal(LeekToken),
    NonTerminal {
        kind: ParseTreeNonTerminalKind,
        children: Vec<ParseTreeNode>,
    },
}

impl ParseTreeNode {
    fn fmt_recursive(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        match self {
            ParseTreeNode::Terminal(token) => {
                writeln!(f, "{}{token}", String::from(" ").repeat(indent))
            }
            ParseTreeNode::NonTerminal { kind, children } => {
                writeln!(f, "{}{kind:?}:", String::from(" ").repeat(indent))?;

                for child in children {
                    child.fmt_recursive(f, indent + 4)?;
                }

                Ok(())
            }
        }
    }
}

impl Display for ParseTreeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_recursive(f, 0)
    }
}

/// Represents non-terminal parse tree nodes
#[derive(Debug, PartialEq)]
pub enum ParseTreeNonTerminalKind {
    Program,                // List of function defs/struct defs/constants
    FunctionDefinition,     // `fn`, identifier, FunctionArguments, (`->`, Type)?, Block
    FunctionArguments,      // `(`, 0 or more FunctionArgument, `)`
    FunctionArgument,       // identifier, `:`, Type
    Block,                  // List of statements
    Type,                   // identifier OR keyword OR identifier, `<`, Type, `>`
    Statement,  // `let`, identifier, `=`, Expression, `\n` OR FunctionCallExpression, `\n`
    Expression, // FunctionCallExpression OR BinaryExpression OR UnaryExpression OR ParenExpression OR Block
    FunctionCallExpression, // identifier, FunctionParameters
    FunctionParameters, // `(`, 0 or more Expression separated by `,`, `)`
    BinaryExpression, // Expression, operator, Expression
    UnaryExpression, // operator, Expression OR Expression, operator
    ParenExpression, // `(`, Expression, `)`
    Atom,       // literal,
}

#[derive(Debug)]
pub struct ParserError {
    kind: ParserErrorKind,
    contents: String,
    span: Span,
}

#[derive(Debug)]
pub enum ParserErrorKind {
    UnexpectedToken {
        expected: LeekTokenKind,
        found: LeekTokenKind,
    },
    UnexpectedEndOfInput {
        expected: LeekTokenKind,
    },
}

pub trait Parser {
    /// Takes in a lexer and returns the root of a parse tree
    fn parse(lexer: impl Lexer + 'static) -> Result<ParseTreeNode, ParserError>;
}

pub struct LeekParser {
    lexer: Box<dyn Lexer>,
}

impl Parser for LeekParser {
    fn parse(lexer: impl Lexer + 'static) -> Result<ParseTreeNode, ParserError> {
        let mut parser = LeekParser::new(lexer);

        parser.parse_from_lexer()
    }
}

impl LeekParser {
    fn new(lexer: impl Lexer + 'static) -> Self {
        Self {
            lexer: Box::new(lexer),
        }
    }

    fn parse_from_lexer(&mut self) -> Result<ParseTreeNode, ParserError> {
        macro_rules! next_token {
            () => {
                self.lexer.next().unwrap().unwrap()
            };
        }

        Ok(ParseTreeNode::NonTerminal {
            kind: ParseTreeNonTerminalKind::Program,
            children: vec![ParseTreeNode::NonTerminal {
                kind: ParseTreeNonTerminalKind::FunctionDefinition,
                children: vec![
                    ParseTreeNode::Terminal(next_token!()), // fn
                    ParseTreeNode::Terminal(next_token!()), // main
                    ParseTreeNode::NonTerminal {
                        kind: ParseTreeNonTerminalKind::FunctionArguments,
                        children: vec![
                            ParseTreeNode::Terminal(next_token!()), // (
                            ParseTreeNode::Terminal(next_token!()), // )
                        ],
                    },
                    ParseTreeNode::NonTerminal {
                        kind: ParseTreeNonTerminalKind::Block,
                        children: vec![
                            ParseTreeNode::Terminal(next_token!()), // {
                            ParseTreeNode::Terminal(next_token!()), // \n
                            ParseTreeNode::NonTerminal {
                                kind: ParseTreeNonTerminalKind::Statement,
                                children: vec![
                                    ParseTreeNode::Terminal(next_token!()), // leak
                                    ParseTreeNode::Terminal(next_token!()), // a
                                    ParseTreeNode::Terminal(next_token!()), // =
                                    ParseTreeNode::NonTerminal {
                                        kind: ParseTreeNonTerminalKind::Expression,
                                        children: vec![
                                            ParseTreeNode::NonTerminal {
                                                kind: ParseTreeNonTerminalKind::Atom,
                                                children: vec![
                                                    ParseTreeNode::Terminal(next_token!()), // 1
                                                ],
                                            },
                                        ],
                                    },
                                    ParseTreeNode::Terminal(next_token!()), // \n
                                ],
                            },
                            ParseTreeNode::NonTerminal {
                                kind: ParseTreeNonTerminalKind::Statement,
                                children: vec![
                                    ParseTreeNode::Terminal(next_token!()), // leak
                                    ParseTreeNode::Terminal(next_token!()), // b
                                    ParseTreeNode::Terminal(next_token!()), // =
                                    ParseTreeNode::NonTerminal {
                                        kind: ParseTreeNonTerminalKind::Expression,
                                        children: vec![
                                            ParseTreeNode::NonTerminal {
                                                kind: ParseTreeNonTerminalKind::Atom,
                                                children: vec![
                                                    ParseTreeNode::Terminal(next_token!()), // 2
                                                ],
                                            },
                                        ],
                                    },
                                    ParseTreeNode::Terminal(next_token!()), // \n
                                ],
                            },
                            ParseTreeNode::NonTerminal {
                                kind: ParseTreeNonTerminalKind::Statement,
                                children: vec![
                                    ParseTreeNode::Terminal(next_token!()), // leak
                                    ParseTreeNode::Terminal(next_token!()), // node
                                    ParseTreeNode::Terminal(next_token!()), // =
                                    ParseTreeNode::NonTerminal {
                                        kind: ParseTreeNonTerminalKind::Expression,
                                        children: vec![ParseTreeNode::NonTerminal {
                                            kind: ParseTreeNonTerminalKind::FunctionCallExpression,
                                            children: vec![
                                                ParseTreeNode::Terminal(next_token!()), // Node
                                                ParseTreeNode::NonTerminal {
                                                    kind:
                                                        ParseTreeNonTerminalKind::FunctionParameters,
                                                    children: vec![
                                                        ParseTreeNode::Terminal(next_token!()), // (
                                                            ParseTreeNode::NonTerminal {
                                                                kind: ParseTreeNonTerminalKind::Expression,
                                                                children: vec![
                                                                    ParseTreeNode::NonTerminal {
                                                                        kind: ParseTreeNonTerminalKind::Atom,
                                                                        children: vec![
                                                                            ParseTreeNode::Terminal(next_token!()), // "text"
                                                                        ],
                                                                    },
                                                                ],
                                                            },
                                                        ParseTreeNode::Terminal(next_token!()), // )
                                                    ],
                                                },
                                            ],
                                        }],
                                    },
                                    ParseTreeNode::Terminal(next_token!()), // \n
                                ],
                            },
                            ParseTreeNode::Terminal(next_token!()), // \n
                            ParseTreeNode::NonTerminal {
                                kind: ParseTreeNonTerminalKind::Statement,
                                children: vec![ParseTreeNode::NonTerminal {
                                    kind: ParseTreeNonTerminalKind::FunctionCallExpression,
                                    children: vec![
                                        ParseTreeNode::Terminal(next_token!()), // println
                                        ParseTreeNode::NonTerminal {
                                            kind: ParseTreeNonTerminalKind::FunctionParameters,
                                            children: vec![
                                                ParseTreeNode::Terminal(next_token!()), // (
                                                ParseTreeNode::Terminal(next_token!()), // a
                                                ParseTreeNode::Terminal(next_token!()), // )
                                            ],
                                        },
                                    ],
                                }],
                            },
                            ParseTreeNode::Terminal(next_token!()), // \n
                            ParseTreeNode::Terminal(next_token!()), // }
                        ],
                    },
                ],
            }],
        })
    }
}

#[cfg(test)]
mod test {
    use crate::{
        lexer::{IntegerLiteralKind, LeekLexer, LeekToken, LeekTokenKind},
        reader::FileReader,
    };

    use super::{LeekParser, ParseTreeNode, ParseTreeNonTerminalKind, Parser};

    fn compare_input_to_expected(input: &str, expected_tree: ParseTreeNode) {
        // Collect tokens from lexer
        let reader = FileReader::from(input.to_owned());
        let lexer = LeekLexer::new(reader);
        let parse_tree = LeekParser::parse(lexer).expect("Could not parse input");

        assert_eq!(
            parse_tree, expected_tree,
            "Parse tree did not match expected"
        );
    }

    macro_rules! terminal {
        ($kind:expr, $text:literal) => {
            ParseTreeNode::Terminal(LeekToken::from(($kind, $text)))
        };
    }

    macro_rules! non_terminal {
        ($kind:expr, $children:expr) => {
            ParseTreeNode::NonTerminal {
                kind: $kind,
                children: $children,
            }
        };
    }

    #[test]
    fn basic_program() {
        compare_input_to_expected(r#"fn main() {
            leak a = 1
            leak b = 2 
            leak node = Node("text")
        
            println(a)  
        }
        "#, 
        non_terminal!(ParseTreeNonTerminalKind::Program, vec![
            non_terminal!(ParseTreeNonTerminalKind::FunctionDefinition, vec![
                terminal!(LeekTokenKind::Keyword, "fn"),
                terminal!(LeekTokenKind::Identifier, "main"),
                non_terminal!(ParseTreeNonTerminalKind::FunctionArguments, vec![
                    terminal!(LeekTokenKind::OpenParen, "("),
                    terminal!(LeekTokenKind::CloseParen, ")"),
                ]),
                non_terminal!(
                    ParseTreeNonTerminalKind::Block,
                    vec![
                        terminal!(LeekTokenKind::OpenCurlyBracket, "{"),
                        terminal!(LeekTokenKind::Newline, "\n"),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            terminal!(LeekTokenKind::Keyword, "leak"),
                            terminal!(LeekTokenKind::Identifier, "a"),
                            terminal!(LeekTokenKind::Equals, "="),
                            non_terminal!(ParseTreeNonTerminalKind::Expression,vec![
                                non_terminal!(ParseTreeNonTerminalKind::Atom,vec![
                                    terminal!(LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Decimal), "1"),
                                ]),
                            ]),
                            terminal!(LeekTokenKind::Newline, "\n"),
                        ]),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            terminal!(LeekTokenKind::Keyword, "leak"),
                            terminal!(LeekTokenKind::Identifier, "b"),
                            terminal!(LeekTokenKind::Equals, "="),
                            non_terminal!(ParseTreeNonTerminalKind::Expression,vec![
                                non_terminal!(ParseTreeNonTerminalKind::Atom,vec![
                                    terminal!(LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Decimal), "2"),
                                ]),
                            ]),
                            terminal!(LeekTokenKind::Newline, "\n"),
                        ]),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            terminal!(LeekTokenKind::Keyword, "leak"),
                            terminal!(LeekTokenKind::Identifier, "node"),
                            terminal!(LeekTokenKind::Equals, "="),
                            non_terminal!(ParseTreeNonTerminalKind::Expression, vec![
                                non_terminal!(ParseTreeNonTerminalKind::FunctionCallExpression, vec![
                                    terminal!(LeekTokenKind::Identifier, "Node"),
                                    non_terminal!(ParseTreeNonTerminalKind::FunctionParameters, vec![
                                        terminal!(LeekTokenKind::OpenParen, "("),
                                        non_terminal!(ParseTreeNonTerminalKind::Expression, vec![
                                            non_terminal!(ParseTreeNonTerminalKind::Atom, vec![
                                                terminal!(LeekTokenKind::StringLiteral, "\"text\""), 
                                            ]),    
                                        ]),
                                        terminal!(LeekTokenKind::CloseParen, ")"),
                                    ]),
                                ]),
                            ]),
                            terminal!(LeekTokenKind::Newline, "\n"),
                        ]),
                        terminal!(LeekTokenKind::Newline, "\n"),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            non_terminal!(ParseTreeNonTerminalKind::FunctionCallExpression, vec![
                                terminal!(LeekTokenKind::Identifier, "println"),
                                non_terminal!(ParseTreeNonTerminalKind::FunctionParameters, vec![
                                    terminal!(LeekTokenKind::OpenParen, "("),
                                    terminal!(LeekTokenKind::Identifier, "a"),
                                    terminal!(LeekTokenKind::CloseParen, ")"),
                                ]),
                            ]),
                        ]),
                        terminal!(LeekTokenKind::Newline, "\n"),
                        terminal!(LeekTokenKind::CloseCurlyBracket, "}"),
                    ]
                ),
            ]),
        ]))
    }
}
