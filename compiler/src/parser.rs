use core::panic;
use std::fmt::Display;

use crate::{
    error::LeekCompilerError,
    lexer::{KeywordKind, LeekToken, LeekTokenKind, Lexer},
    position::Span,
};

#[derive(Debug, PartialEq)]
pub enum ParseTreeNode {
    Terminal(LeekToken),
    NonTerminal(ParseTreeNodeNonTerminal),
}

#[derive(Debug, PartialEq)]
pub struct ParseTreeNodeNonTerminal {
    kind: ParseTreeNonTerminalKind,
    children: Vec<ParseTreeNode>,
}

impl ParseTreeNode {
    fn fmt_recursive(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        match self {
            ParseTreeNode::Terminal(token) => {
                writeln!(f, "{}{token}", String::from(" ").repeat(indent))
            }
            ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal { kind, children }) => {
                writeln!(f, "{}{kind:?}:", String::from(" ").repeat(indent))?;

                for child in children {
                    child.fmt_recursive(f, indent + 4)?;
                }

                Ok(())
            }
        }
    }

    #[allow(dead_code)]
    fn terminal_token(&mut self) -> &mut LeekToken {
        if let ParseTreeNode::Terminal(token) = self {
            token
        } else {
            panic!("Node is not terminal type")
        }
    }

    fn non_terminal(&mut self) -> &mut ParseTreeNodeNonTerminal {
        if let ParseTreeNode::NonTerminal(non_terminal) = self {
            non_terminal
        } else {
            panic!("Node is not non-terminal type")
        }
    }
}

macro_rules! terminal {
    ($token:expr) => {
        ParseTreeNode::Terminal($token)
    };
}

macro_rules! non_terminal {
    ($kind:expr, $children:expr) => {
        ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: $kind,
            children: $children,
        })
    };
}

impl Display for ParseTreeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_recursive(f, 0)
    }
}

/// Represents non-terminal parse tree nodes
#[derive(Debug, PartialEq)]
pub enum ParseTreeNonTerminalKind {
    Program,
    FunctionDeclaration,
    FunctionDefinition,
    FunctionParameters,
    Block,
    Statement,
    Expression,
    FunctionCallExpression,
    FunctionArguments,
    BinaryExpression,
    UnaryExpression,
    Atom,
    StructDefinition,
    TypeAssociation,
    Type,
    ConstantVariableDeclaration,
    StaticVariableDeclaration,
}

#[derive(Debug)]
pub struct ParserError {
    pub kind: ParserErrorKind,
    pub contents: String,
    pub span: Span,
}

#[derive(Debug)]
pub enum ParserErrorKind {
    UnexpectedToken {
        expected: Vec<LeekTokenKind>,
        found: LeekTokenKind,
    },
    UnexpectedKeyword {
        expected: Vec<KeywordKind>,
        found: KeywordKind,
    },
    UnexpectedEndOfInput,
}

pub trait Parser {
    /// Takes in a lexer and returns the root of a parse tree
    fn parse(lexer: impl Lexer + 'static) -> Result<ParseTreeNode, LeekCompilerError>;
}

pub struct LeekParser {
    lexer: Box<dyn Lexer>,
}

impl Parser for LeekParser {
    fn parse(lexer: impl Lexer + 'static) -> Result<ParseTreeNode, LeekCompilerError> {
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

    /// Peeks the next token or returns an error if there are non left
    fn peek_expect(&self) -> Result<&LeekToken, LeekCompilerError> {
        self.lexer.peek()?.ok_or_else(|| {
            ParserError {
                kind: ParserErrorKind::UnexpectedEndOfInput,
                contents: self.lexer.get_contents().clone(),
                span: Span::from(self.lexer.get_position()),
            }
            .into()
        })
    }

    /// Searches the next token ignoring new lines
    fn peek_after_new_line(&self) -> Result<Option<&LeekToken>, LeekCompilerError> {
        let mut n = 0;

        while self.lexer.has_next()? {
            let Some(peeked) = self.lexer.peek_nth(n)? else {
                return Ok(None);
            };

            match peeked.kind {
                LeekTokenKind::Newline => {
                    n += 1;
                    continue;
                }
                _ => return Ok(Some(peeked)),
            }
        }

        Ok(None)
    }

    /// Ignores tokens while they are new lines
    fn bleed_whitespace(&mut self) -> Result<(), LeekCompilerError> {
        while self
            .lexer
            .peek()?
            .is_some_and(|t| t.kind == LeekTokenKind::Newline)
        {
            self.lexer.next()?;
        }

        Ok(())
    }

    /// Grabs the next token or throws an error if no tokens are left
    fn next_expect(&mut self, kind: LeekTokenKind) -> Result<LeekToken, LeekCompilerError> {
        let token = self.lexer.next()?.ok_or_else(|| {
            Into::<LeekCompilerError>::into(ParserError {
                kind: ParserErrorKind::UnexpectedEndOfInput,
                contents: self.lexer.get_contents().clone(),
                span: Span::from(self.lexer.get_position()),
            })
        })?;

        if token.kind != kind {
            return Err(ParserError {
                kind: ParserErrorKind::UnexpectedToken {
                    expected: vec![kind],
                    found: token.kind,
                },
                contents: self.lexer.get_contents().clone(),
                span: Span::from(self.lexer.get_position()),
            }
            .into());
        }

        Ok(token)
    }

    /// Program ::
    ///     (
    ///         FunctionDefinition
    ///         | FunctionDeclaration
    ///         | StructDefinition
    ///         | ConstantVariableDeclaration
    ///         | StaticVariableDeclaration
    ///     )+
    ///      
    fn parse_program_part(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let peeked_token = self.peek_expect()?;

        match peeked_token.kind {
            // FunctionDefinition or FunctionDeclaration
            LeekTokenKind::Keyword(KeywordKind::Fn) => {
                self.parse_function_declaration_or_definition()
            }
            // StructDefinition
            LeekTokenKind::Keyword(KeywordKind::Struct) => self.parse_struct_definition(),
            // ConstantVariableDeclaration
            LeekTokenKind::Keyword(KeywordKind::Perm) => self.parse_constant_variable_declaration(),
            // StaticVariableDeclaration
            LeekTokenKind::Keyword(KeywordKind::Hold) => self.parse_static_variable_declaration(),
            // Unexpected keyword
            LeekTokenKind::Keyword(kw) => {
                return Err(ParserError {
                    kind: ParserErrorKind::UnexpectedKeyword {
                        expected: vec![
                            KeywordKind::Fn,
                            KeywordKind::Struct,
                            KeywordKind::Perm,
                            KeywordKind::Hold,
                        ],
                        found: kw,
                    },
                    span: peeked_token.span.clone(),
                    contents: self.lexer.get_contents().clone(),
                }
                .into());
            }
            // Any other token
            _ => {
                return Err(ParserError {
                    kind: ParserErrorKind::UnexpectedToken {
                        expected: vec![
                            LeekTokenKind::Keyword(KeywordKind::Fn),
                            LeekTokenKind::Keyword(KeywordKind::Struct),
                            LeekTokenKind::Keyword(KeywordKind::Perm),
                            LeekTokenKind::Keyword(KeywordKind::Hold),
                        ],
                        found: peeked_token.kind,
                    },
                    span: peeked_token.span.clone(),
                    contents: self.lexer.get_contents().clone(),
                }
                .into());
            }
        }
    }

    /// FunctionDefinition ::
    ///     `fn` identifier FunctionParameters (`->` Type)? Newline* Block
    ///
    /// FunctionDeclaration ::
    ///     `fn` identifier FunctionParameters (`->` Type)? Newline
    ///   
    fn parse_function_declaration_or_definition(
        &mut self,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect(LeekTokenKind::Keyword(KeywordKind::Fn))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect(LeekTokenKind::Identifier)?));
        self.bleed_whitespace()?;

        children.push(self.parse_function_parameters()?);
        self.bleed_whitespace()?;

        // TODO: Parse return type

        let mut kind = ParseTreeNonTerminalKind::FunctionDeclaration;

        if let Some(token) = self.lexer.peek()? {
            if token.kind == LeekTokenKind::OpenCurlyBracket {
                kind = ParseTreeNonTerminalKind::FunctionDefinition;
                children.push(self.parse_block()?);
            }
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind,
            children,
        }))
    }

    /// FunctionParameters ::
    ///     `(`
    ///          (
    ///              TypeAssociation
    ///              | (TypeAssociation `,`)* TypeAssociation)
    ///          )?
    ///      `)`
    fn parse_function_parameters(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect(LeekTokenKind::OpenParen)?));
        self.bleed_whitespace()?;

        // TODO: Support typed function parameters

        children.push(terminal!(self.next_expect(LeekTokenKind::CloseParen)?));
        self.bleed_whitespace()?;

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionParameters,
            children,
        }))
    }

    /// Block ::
    ///     `{`
    ///         (Block | Statement)*
    ///     `}`
    fn parse_block(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect(LeekTokenKind::OpenCurlyBracket)?));
        self.bleed_whitespace()?;

        while self.lexer.has_next()? {
            let token = self.lexer.peek()?.unwrap();

            match token.kind {
                // Ignore preceding newlines
                LeekTokenKind::Newline => {
                    self.lexer.next()?;
                }
                // Allow recursive blocks
                LeekTokenKind::OpenBracket => children.push(self.parse_block()?),
                // Break the loop if a closing bracket is found
                LeekTokenKind::CloseCurlyBracket => break,

                _ => children.push(self.parse_statement()?),
            }
        }

        children.push(terminal!(
            self.next_expect(LeekTokenKind::CloseCurlyBracket)?
        ));
        self.bleed_whitespace()?;

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Block,
            children,
        }))
    }

    /// Statement ::
    ///     (
    ///         (return Expression)
    ///         | (let identifier (`:` Type)? = Expression)
    ///         | (FunctionCallExpression)
    ///     )
    ///     (
    ///         `\n` | `}`    
    ///     )
    ///     
    fn parse_statement(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse statement")
    }

    /// Expression ::
    ///     FunctionCallExpression
    ///     | BinaryExpression
    ///     | UnaryExpression
    ///     | Atom
    fn parse_expression(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse expression")
    }

    /// FunctionCallExpression ::
    ///     identifier `(`
    ///         FunctionArguments?
    ///      `)`
    fn parse_function_call_expression(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse function call expression")
    }

    /// FunctionArguments ::
    ///     (
    ///          Expression
    ///          | ((Expression `,`)* Expression)
    ///     )
    fn parse_function_arguments(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse function arguments")
    }

    /// BinaryExpression ::
    ///     Expression binary_operator Expression
    fn parse_binary_expression(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse binary expression")
    }

    /// UnaryExpression ::
    ///     unary_operator Expression  
    fn parse_unary_expression(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse unary_operator expression")
    }

    /// Atom ::
    ///     identifier
    ///     | literal
    ///     | (
    ///         `(` Expression `)`
    ///       )
    fn parse_atom(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse atom")
    }

    /// StructDefinition ::
    ///     `struct` identifier `{`
    ///         StructDefinitionBody?
    ///     `}`
    fn parse_struct_definition(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse struct definition")
    }

    /// StructDefinitionBody ::
    ///     (
    ///         TypeAssociation
    ///         | ((TypeAssociation `,`)* TypeAssociation)
    ///     )
    fn parse_struct_definition_body(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse struct definition body")
    }

    /// TypeAssociation ::
    ///     (identifier `:` Type)
    fn parse_type_association(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse type association")
    }

    /// Type ::
    ///     identifier | keyword
    fn parse_type(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse type")
    }

    /// ConstantVariableDeclaration ::
    ///     `perm` identifier `:` Type `=` Expression
    fn parse_constant_variable_declaration(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse constant variable declaration")
    }

    /// StaticVariableDeclaration ::
    ///     `hold` identifier `:` Type `=` Expression
    fn parse_static_variable_declaration(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        todo!("parse static variable declaration")
    }

    /// Internal method to parse all the tokens from the internal lexer
    fn parse_from_lexer(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        macro_rules! next_token {
            () => {
                self.lexer.next()?.unwrap()
            };
        }

        let mut root = ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Program,
            children: vec![],
        });

        while self.lexer.has_next()? {
            root.non_terminal()
                .children
                .push(self.parse_program_part()?)
        }

        Ok(non_terminal!(
            ParseTreeNonTerminalKind::Program,
            vec![non_terminal!(
                ParseTreeNonTerminalKind::FunctionDefinition,
                vec![
                    terminal!(next_token!()), // fn
                    terminal!(next_token!()), // main
                    non_terminal!(
                        ParseTreeNonTerminalKind::FunctionParameters,
                        vec![
                            terminal!(next_token!()), // (
                            terminal!(next_token!()), // )
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::Block,
                        vec![
                            terminal!(next_token!()), // {
                            terminal!(next_token!()), // \n
                            non_terminal!(
                                ParseTreeNonTerminalKind::Statement,
                                vec![
                                    terminal!(next_token!()), // leak
                                    terminal!(next_token!()), // a
                                    terminal!(next_token!()), // =
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Expression,
                                        vec![non_terminal!(
                                            ParseTreeNonTerminalKind::Atom,
                                            vec![
                                        terminal!(next_token!()), // 1
                                    ]
                                        ),]
                                    ),
                                    terminal!(next_token!()), // \n
                                ]
                            ),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Statement,
                                vec![
                                    terminal!(next_token!()), // leak
                                    terminal!(next_token!()), // b
                                    terminal!(next_token!()), // =
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Expression,
                                        vec![non_terminal!(
                                            ParseTreeNonTerminalKind::Atom,
                                            vec![
                                                    terminal!(next_token!()), // 2
                                                ]
                                        ),]
                                    ),
                                    terminal!(next_token!()), // \n
                                ]
                            ),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Statement,
                                vec![
                                    terminal!(next_token!()), // leak
                                    terminal!(next_token!()), // node
                                    terminal!(next_token!()), // =
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Expression,
                                        vec![non_terminal!(
                                            ParseTreeNonTerminalKind::FunctionCallExpression,
                                            vec![
                                                terminal!(next_token!()), // Node
                                                non_terminal!(
                                                    ParseTreeNonTerminalKind::FunctionArguments,
                                                    vec![
                                                        terminal!(next_token!()), // (
                                                        non_terminal!(
                                                            ParseTreeNonTerminalKind::Expression,
                                                            vec![non_terminal!(
                                                                ParseTreeNonTerminalKind::Atom,
                                                                vec![
                                                                    terminal!(next_token!()), // "text"
                                                                ]
                                                            ),]
                                                        ),
                                                        terminal!(next_token!()), // )
                                                    ]
                                                ),
                                            ]
                                        )]
                                    ),
                                    terminal!(next_token!()), // \n
                                ]
                            ),
                            terminal!(next_token!()), // \n
                            non_terminal!(
                                ParseTreeNonTerminalKind::Statement,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::FunctionCallExpression,
                                    vec![
                                        terminal!(next_token!()), // println
                                        non_terminal!(
                                            ParseTreeNonTerminalKind::FunctionArguments,
                                            vec![
                                                terminal!(next_token!()), // (
                                                terminal!(next_token!()), // a
                                                terminal!(next_token!()), // )
                                            ]
                                        ),
                                    ]
                                )]
                            ),
                            terminal!(next_token!()), // \n
                            terminal!(next_token!()), // }
                        ]
                    )
                ]
            )]
        ))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        lexer::{IntegerLiteralKind, KeywordKind, LeekLexer, LeekToken, LeekTokenKind},
        reader::FileReader,
    };

    use super::{
        LeekParser, ParseTreeNode, ParseTreeNodeNonTerminal, ParseTreeNonTerminalKind, Parser,
    };

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

    macro_rules! terminal_from {
        ($kind:expr, $text:literal) => {
            ParseTreeNode::Terminal(LeekToken::from(($kind, $text)))
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
                terminal_from!(LeekTokenKind::Keyword(KeywordKind::Fn), "fn"),
                terminal_from!(LeekTokenKind::Identifier, "main"),
                non_terminal!(ParseTreeNonTerminalKind::FunctionParameters, vec![
                    terminal_from!(LeekTokenKind::OpenParen, "("),
                    terminal_from!(LeekTokenKind::CloseParen, ")"),
                ]),
                non_terminal!(
                    ParseTreeNonTerminalKind::Block,
                    vec![
                        terminal_from!(LeekTokenKind::OpenCurlyBracket, "{"),
                        terminal_from!(LeekTokenKind::Newline, "\n"),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Leak), "leak"),
                            terminal_from!(LeekTokenKind::Identifier, "a"),
                            terminal_from!(LeekTokenKind::Equals, "="),
                            non_terminal!(ParseTreeNonTerminalKind::Expression,vec![
                                non_terminal!(ParseTreeNonTerminalKind::Atom,vec![
                                    terminal_from!(LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Decimal), "1"),
                                ]),
                            ]),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Leak), "leak"),
                            terminal_from!(LeekTokenKind::Identifier, "b"),
                            terminal_from!(LeekTokenKind::Equals, "="),
                            non_terminal!(ParseTreeNonTerminalKind::Expression,vec![
                                non_terminal!(ParseTreeNonTerminalKind::Atom,vec![
                                    terminal_from!(LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Decimal), "2"),
                                ]),
                            ]),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Leak), "leak"),
                            terminal_from!(LeekTokenKind::Identifier, "node"),
                            terminal_from!(LeekTokenKind::Equals, "="),
                            non_terminal!(ParseTreeNonTerminalKind::Expression, vec![
                                non_terminal!(ParseTreeNonTerminalKind::FunctionCallExpression, vec![
                                    terminal_from!(LeekTokenKind::Identifier, "Node"),
                                    non_terminal!(ParseTreeNonTerminalKind::FunctionArguments, vec![
                                        terminal_from!(LeekTokenKind::OpenParen, "("),
                                        non_terminal!(ParseTreeNonTerminalKind::Expression, vec![
                                            non_terminal!(ParseTreeNonTerminalKind::Atom, vec![
                                                terminal_from!(LeekTokenKind::StringLiteral, "\"text\""), 
                                            ]),
                                        ]),
                                        terminal_from!(LeekTokenKind::CloseParen, ")"),
                                    ]),
                                ]),
                            ]),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]),
                        terminal_from!(LeekTokenKind::Newline, "\n"),
                        non_terminal!(ParseTreeNonTerminalKind::Statement, vec![
                            non_terminal!(ParseTreeNonTerminalKind::FunctionCallExpression, vec![
                                terminal_from!(LeekTokenKind::Identifier, "println"),
                                non_terminal!(ParseTreeNonTerminalKind::FunctionArguments, vec![
                                    terminal_from!(LeekTokenKind::OpenParen, "("),
                                    terminal_from!(LeekTokenKind::Identifier, "a"),
                                    terminal_from!(LeekTokenKind::CloseParen, ")"),
                                ]),
                            ]),
                        ]),
                        terminal_from!(LeekTokenKind::Newline, "\n"),
                        terminal_from!(LeekTokenKind::CloseCurlyBracket, "}"),
                    ]
                ),
            ]),
        ]))
    }
}
