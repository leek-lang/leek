use crate::{
    parser::ParseTree,
    position::{SourceFile, Span},
};

#[derive(Debug)]
pub struct LeekAst {
    source_file: SourceFile,
    root: Program,
}

impl From<ParseTree> for LeekAst {
    fn from(parse_tree: ParseTree) -> Self {
        let root = Program {
            constant_variables: todo!(),
            static_variables: todo!(),
            function_definitions: todo!(),
            struct_definitions: todo!(),
            enum_definitions: todo!(),
        };

        Self {
            source_file: parse_tree.source_file,
            root,
        }
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

#[derive(Debug)]
pub enum Type {
    Primitive(PrimitiveKind),
    Identifier(QualifiedIdentifier),
}

#[derive(Debug)]
pub struct QualifiedIdentifier {
    namespace: Vec<String>,
    name: String,
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
    parameters: Vec<FunctionParameter>,
    return_type: Type,
    body: Block,
}

#[derive(Debug)]
pub struct FunctionParameter {
    identifier: String,
    ty: Type,
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
