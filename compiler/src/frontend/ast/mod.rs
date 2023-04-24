use crate::common::lang::{AssignmentOperator, BinaryOperator, PrimitiveKind, UnaryOperator};

use super::position::{SourceFile, Span};

pub mod builder;

#[derive(Debug)]
pub struct LeekAst {
    pub source_file: SourceFile,
    pub root: Program,
}

#[derive(Debug)]
pub struct Program {
    pub constant_variables: Vec<VariableDeclaration>,
    pub static_variables: Vec<VariableDeclaration>,
    pub function_definitions: Vec<FunctionDefinition>,
    pub struct_definitions: Vec<StructDefinition>,
    pub enum_definitions: Vec<EnumDefinition>,
}

#[derive(Debug)]
pub enum Type {
    Primitive(PrimitiveKind),
    Identifier(QualifiedIdentifier),
}

#[derive(Debug, PartialEq, Eq)]
pub struct QualifiedIdentifier {
    pub namespace: Option<Vec<String>>,
    pub name: String,
}

impl QualifiedIdentifier {
    pub fn new(namespace: Option<Vec<String>>, name: String) -> Self {
        Self { namespace, name }
    }

    pub fn namespace(&self) -> Option<&Vec<String>> {
        self.namespace.as_ref()
    }

    pub fn has_namespace(&self) -> bool {
        self.namespace.is_some()
    }

    pub fn name(&self) -> &String {
        &self.name
    }
}

#[derive(Debug)]
pub struct VariableDeclaration {
    pub kind: VariableDeclarationKind,
    pub identifier: String,
    pub ty: Option<Type>,
    pub value: Expression,
}

#[derive(Debug)]
pub enum VariableDeclarationKind {
    Constant,
    Static,
    Local,
}

#[derive(Debug)]
pub struct VariableAssignment {
    pub identifier: QualifiedIdentifier,
    pub operator: AssignmentOperator,
    pub value: Expression,
}

#[derive(Debug)]
pub enum Expression {
    Atom(Atom),
    UnaryExpression(UnaryExpression),
    FunctionCallExpression(FunctionCallExpression),
    BinaryExpression(BinaryExpression),
    StructInitialization(StructInitialization),
    StructFieldAccess(StructFieldAccess),
    StructMethodCall(StructMethodCall),
}

#[derive(Debug)]
pub enum Atom {
    QualifiedIdentifier(QualifiedIdentifier),
    Literal(Literal),
    ParenthesizedExpression(Box<Expression>),
}

#[derive(Debug)]
pub struct Literal {
    pub kind: LiteralKind,
    pub span: Span,
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
    pub unary_operator: UnaryOperator,
    pub expression: Box<Expression>,
}

#[derive(Debug)]
pub struct BinaryExpression {
    pub binary_operator: BinaryOperator,
    pub expression: Box<Expression>,
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub name: String,
    pub struct_identifier: Option<String>,
    pub parameters: Vec<FunctionParameter>,
    pub return_type: Type,
    pub body: Block,
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub identifier: String,
    pub ty: Type,
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    Block(Block),
    Yeet(Expression),
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionCall(FunctionCallExpression),
}

#[derive(Debug)]
pub struct FunctionCallExpression {
    pub identifier: QualifiedIdentifier,
    pub arguments: Vec<Expression>,
}

#[derive(Debug)]
pub struct StructDefinition {
    pub name: String,
    pub fields: Vec<StructField>,
}

#[derive(Debug)]
pub struct StructField {
    pub identifier: String,
    pub ty: Type,
}

#[derive(Debug)]
pub struct EnumDefinition {
    pub name: String,
    pub variants: Vec<String>,
}

#[derive(Debug)]
pub struct StructInitialization {
    pub identifier: QualifiedIdentifier,
    pub arguments: Vec<StructInitializationField>,
}

#[derive(Debug)]
pub struct StructInitializationField {
    pub identifier: String,
    pub value: Expression,
}

#[derive(Debug)]
pub struct StructFieldAccess {
    pub identifier: QualifiedIdentifier,
    pub field: String,
}

#[derive(Debug)]
pub struct StructMethodCall {
    pub identifier: QualifiedIdentifier,
    pub method: String,
    pub arguments: Vec<Expression>,
}
