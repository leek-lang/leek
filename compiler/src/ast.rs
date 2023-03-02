use core::panic;
use std::fmt::Display;

use crate::{
    lexer::{LeekToken, LeekTokenKind},
    parser::{ParseTree, ParseTreeNode, ParseTreeNodeNonTerminal, ParseTreeNonTerminalKind},
    position::{SourceFile, Span},
};

#[derive(Debug)]
pub struct AstBuildError {
    pub kind: AstBuildErrorKind,
}

impl Display for AstBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            AstBuildErrorKind::InvalidNode(node) => {
                writeln!(f, "Invalid ParseTreeNode: {:?}", node)
            }
        }
    }
}

#[derive(Debug)]
pub enum AstBuildErrorKind {
    InvalidNode(ParseTreeNode),
}

#[derive(Debug)]
pub struct LeekAst {
    source_file: SourceFile,
    root: Program,
}

impl LeekAst {
    pub fn build_from(parse_tree: ParseTree) -> Result<Self, AstBuildError> {
        let root = Program {
            constant_variables: vec![],
            static_variables: vec![],
            function_definitions: vec![],
            struct_definitions: vec![],
            enum_definitions: vec![],
        };

        let mut ast = Self {
            source_file: parse_tree.source_file.clone(),
            root,
        };

        ast.populate(parse_tree)?;

        Ok(ast)
    }

    fn populate(&mut self, parse_tree: ParseTree) -> Result<(), AstBuildError> {
        let program = parse_tree.root.non_terminal();
        assert!(program.kind == ParseTreeNonTerminalKind::Program);

        for node in &program.children {
            let ParseTreeNode::NonTerminal(top_level_node) = node else {
                return Err(node.into())
            };

            match top_level_node.kind {
                ParseTreeNonTerminalKind::ConstantVariableDeclaration => self
                    .root
                    .constant_variables
                    .push(VariableDeclaration::from_node(top_level_node)?),
                ParseTreeNonTerminalKind::StaticVariableDeclaration => self
                    .root
                    .static_variables
                    .push(VariableDeclaration::from_node(top_level_node)?),
                ParseTreeNonTerminalKind::FunctionDefinition => self
                    .root
                    .function_definitions
                    .push(FunctionDefinition::from_node(top_level_node)?),
                ParseTreeNonTerminalKind::StructDefinition => self
                    .root
                    .struct_definitions
                    .push(StructDefinition::from_node(top_level_node)?),
                _ => return Err(node.into()),
            }
        }

        Ok(())
    }
}

fn assert_nt_kind(
    node: &ParseTreeNodeNonTerminal,
    kind: ParseTreeNonTerminalKind,
) -> Result<(), AstBuildError> {
    if node.kind != kind {
        return Err(node.to_owned().into());
    }

    Ok(())
}

impl From<ParseTreeNode> for AstBuildError {
    fn from(node: ParseTreeNode) -> Self {
        AstBuildError {
            kind: AstBuildErrorKind::InvalidNode(node),
        }
    }
}

impl From<ParseTreeNodeNonTerminal> for AstBuildError {
    fn from(node: ParseTreeNodeNonTerminal) -> Self {
        AstBuildError {
            kind: AstBuildErrorKind::InvalidNode(ParseTreeNode::NonTerminal(node)),
        }
    }
}

impl From<&ParseTreeNode> for AstBuildError {
    fn from(node: &ParseTreeNode) -> Self {
        node.to_owned().into()
    }
}

impl From<&ParseTreeNodeNonTerminal> for AstBuildError {
    fn from(node: &ParseTreeNodeNonTerminal) -> Self {
        node.to_owned().into()
    }
}

#[derive(Debug)]
pub struct Program {
    constant_variables: Vec<VariableDeclaration>,
    static_variables: Vec<VariableDeclaration>,
    function_definitions: Vec<FunctionDefinition>,
    struct_definitions: Vec<StructDefinition>,
    enum_definitions: Vec<EnumDefinition>,
}

trait FromNode
where
    Self: Sized,
{
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError>;
}

#[derive(Debug)]
pub enum Type {
    Primitive(PrimitiveKind),
    Identifier(QualifiedIdentifier),
}

#[derive(Debug)]
pub struct QualifiedIdentifier {
    namespace: Option<Vec<String>>,
    name: String,
}

impl FromNode for QualifiedIdentifier {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert!(node.children.len() >= 1);

        let name = node.children.last().unwrap().terminal_token().text.clone();

        let mut namespace = None;

        if node.children.len() > 1 {
            assert!(node.children.len() % 2 == 1);

            let mut parts = vec![];

            for i in 0..(node.children.len() - 1) / 2 {
                let id = node.children.get(i * 2).unwrap().terminal_token();

                parts.push(id.text.clone())
            }

            namespace = Some(parts)
        }

        Ok(QualifiedIdentifier { namespace, name })
    }
}

#[derive(Debug)]
pub enum PrimitiveKind {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

#[derive(Debug)]
pub struct VariableDeclaration {
    kind: VariableDeclarationKind,
    identifier: String,
    ty: Option<Type>,
    value: Expression,
}

impl FromNode for VariableDeclaration {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!()
    }
}

#[derive(Debug)]
pub enum VariableDeclarationKind {
    Constant,
    Static,
    Local,
}

#[derive(Debug)]
pub struct VariableAssignment {
    identifier: String,
    operator: AssignmentOperator,
    value: Expression,
}

#[derive(Debug)]
pub enum AssignmentOperator {
    Equals,
    PlusEquals,
    MinusEquals,
    MultiplyEquals,
    DivideEquals,
    ModuloEquals,
    BitwiseNotEquals,
    BitwiseXorEquals,
    BitwiseOrEquals,
    BitwiseAndEquals,
    LogicalNotEquals,
    ExponentiationEquals,
    LeftShiftEquals,
    RightShiftEquals,
    LogicalOrEquals,
    LogicalAndEquals,
}

#[derive(Debug)]
pub enum Expression {
    Atom(Atom),
    UnaryExpression(UnaryExpression),
    FunctionCallExpression(FunctionCallExpression),
    BinaryExpression(BinaryExpression),
}

#[derive(Debug)]
pub enum Atom {
    Literal(Literal),
    ParenthesizedExpression(Box<Expression>),
}

#[derive(Debug)]
pub struct Literal {
    kind: LiteralKind,
    span: Span,
}

#[derive(Debug)]
pub enum LiteralKind {
    Integer(IntegerKind),
    Float(FloatKind),
    Char(char),
    String(String),
}

#[derive(Debug)]
pub enum IntegerKind {
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
}

#[derive(Debug)]
pub enum FloatKind {
    F32(f32),
    F64(f64),
}

#[derive(Debug)]
pub struct UnaryExpression {
    unary_operator: UnaryOperator,
    expression: Box<Expression>,
}

#[derive(Debug)]
pub enum UnaryOperator {
    BitwiseNot,
    LogicalNot,
    Asterisk,
}

#[derive(Debug)]
pub struct BinaryExpression {
    binary_operator: BinaryOperator,
    expression: Box<Expression>,
}

#[derive(Debug)]
pub enum BinaryOperator {
    DoubleEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Plus,
    Minus,
    Asterisk,
    Divide,
    Modulo,
    BitwiseXor,
    BitwiseOr,
    BitwiseAnd,
    Exponentiation,
    LeftShift,
    RightShift,
    LogicalOr,
    LogicalAnd,
}

#[derive(Debug)]
pub struct FunctionDefinition {
    name: String,
    struct_identifier: Option<String>,
    parameters: Vec<FunctionParameter>,
    return_type: Type,
    body: Block,
}

impl FromNode for FunctionDefinition {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::FunctionDefinition)?;

        /* Get Function Def Components */

        assert!(node.children.len() >= 4 && node.children.len() <= 5);

        let (_fn, identifier, parameters, return_type, block) = match node.children.len() {
            4 => (
                &node.children[0],
                &node.children[1],
                &node.children[2],
                None,
                &node.children[3],
            ),
            5 => (
                &node.children[0],
                &node.children[1],
                &node.children[2],
                Some(&node.children[3]),
                &node.children[4],
            ),
            _ => unreachable!(),
        };

        /* Build the function identifier and struct identifier (if any) */

        let QualifiedIdentifier { name, namespace } =
            QualifiedIdentifier::from_node(identifier.non_terminal())?;

        let struct_identifier = match namespace {
            Some(n) => {
                if n.len() == 1 {
                    n.first().map(|s| s.to_owned())
                } else {
                    panic!("Function name qualified identifier had more than one namespace value");
                    return Err(node.into());
                }
            }
            None => None,
        };

        /* Build the function parameters */

        // Make sure that the param node is correct
        assert_nt_kind(
            &parameters.non_terminal(),
            ParseTreeNonTerminalKind::FunctionParameters,
        )?;

        let parameter_nodes = &parameters.non_terminal().children;

        // Make sure we have enough nodes
        assert!(
            parameter_nodes.len() >= 2,
            "Less than 2 nodes in function parameters. Expected parens."
        );

        // Make sure nodes are correct
        assert_eq!(
            parameter_nodes.first().unwrap().terminal_token().kind,
            LeekTokenKind::OpenParen,
            "Expected first token of params to be open paren"
        );

        assert_eq!(
            parameter_nodes.last().unwrap().terminal_token().kind,
            LeekTokenKind::CloseParen,
            "Expected last token of params to be close paren"
        );

        let mut parameters = Vec::new();

        for i in 1..parameter_nodes.len() - 1 {
            parameters.push(FunctionParameter::from_node(parameter_nodes.get(i).unwrap().non_terminal())?)
        }

        Ok(FunctionDefinition {
            name,
            struct_identifier,
            parameters,
            return_type: todo!(),
            body: todo!(),
        })
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    identifier: String,
    ty: Type,
}

impl FromNode for FunctionParameter {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!()
    }
}

#[derive(Debug)]
pub struct Block {
    statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    Yeet(Expression),
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionCall(FunctionCallExpression),
}

#[derive(Debug)]
pub struct FunctionCallExpression {
    identifier: QualifiedIdentifier,
    arguments: Vec<Expression>,
}

#[derive(Debug)]
pub struct StructDefinition {
    name: String,
    fields: Vec<StructField>,
}

impl FromNode for StructDefinition {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!()
    }
}

#[derive(Debug)]
pub struct StructField {
    identifier: String,
    ty: Type,
}

#[derive(Debug)]
pub struct EnumDefinition {
    name: String,
    variants: Vec<String>,
}
