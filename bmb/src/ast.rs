//! Abstract Syntax Tree definitions for BMB
//!
//! The AST represents the structure of BMB programs after parsing.

use std::fmt;

/// A complete BMB program consisting of one or more nodes
#[derive(Debug, Clone)]
pub struct Program {
    pub nodes: Vec<Node>,
}

/// A function node in BMB
#[derive(Debug, Clone)]
pub struct Node {
    pub name: Identifier,
    pub params: Vec<Parameter>,
    pub returns: Type,
    pub precondition: Option<Expr>,
    pub postcondition: Option<Expr>,
    pub body: Vec<Instruction>,
    pub span: Span,
}

/// A function parameter
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: Identifier,
    pub ty: Type,
    pub span: Span,
}

/// BMB types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    I32,
    I64,
    F32,
    F64,
    Bool,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::Bool => write!(f, "bool"),
        }
    }
}

/// An instruction in the function body
#[derive(Debug, Clone)]
pub enum Instruction {
    /// Label for jump targets
    Label(Identifier),
    /// Statement (opcode with operands)
    Statement(Statement),
}

/// A statement is an opcode with its operands
#[derive(Debug, Clone)]
pub struct Statement {
    pub opcode: Opcode,
    pub operands: Vec<Operand>,
    pub span: Span,
}

/// BMB opcodes
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Opcode {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Control flow
    Ret,
    Jmp,
    Jif,
    Call,

    // Variables
    Mov,
    Load,
    Store,
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Opcode::Add => write!(f, "add"),
            Opcode::Sub => write!(f, "sub"),
            Opcode::Mul => write!(f, "mul"),
            Opcode::Div => write!(f, "div"),
            Opcode::Mod => write!(f, "mod"),
            Opcode::Eq => write!(f, "eq"),
            Opcode::Ne => write!(f, "ne"),
            Opcode::Lt => write!(f, "lt"),
            Opcode::Le => write!(f, "le"),
            Opcode::Gt => write!(f, "gt"),
            Opcode::Ge => write!(f, "ge"),
            Opcode::Ret => write!(f, "ret"),
            Opcode::Jmp => write!(f, "jmp"),
            Opcode::Jif => write!(f, "jif"),
            Opcode::Call => write!(f, "call"),
            Opcode::Mov => write!(f, "mov"),
            Opcode::Load => write!(f, "load"),
            Opcode::Store => write!(f, "store"),
        }
    }
}

/// An operand in a statement
#[derive(Debug, Clone)]
pub enum Operand {
    /// Register reference: %r, %n1, %base
    Register(Identifier),
    /// Label reference: _one, _loop
    Label(Identifier),
    /// Integer literal: 0, 1, 42
    IntLiteral(i64),
    /// Float literal: 3.14, 2.0
    FloatLiteral(f64),
    /// Identifier (variable or function name)
    Identifier(Identifier),
}

/// An expression (used in contracts)
#[derive(Debug, Clone)]
pub enum Expr {
    /// Binary operation: a + b, x == y
    Binary {
        left: Box<Expr>,
        op: BinaryOp,
        right: Box<Expr>,
    },
    /// Unary operation: !x, -n
    Unary { op: UnaryOp, operand: Box<Expr> },
    /// Variable reference
    Var(Identifier),
    /// Integer literal
    IntLit(i64),
    /// Float literal
    FloatLit(f64),
    /// Boolean literal
    BoolLit(bool),
    /// Return value reference (for postconditions)
    Ret,
}

/// Binary operators
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Logical
    And,
    Or,
}

/// Unary operators
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

/// An identifier (variable, function, label name)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
    pub name: String,
    pub span: Span,
}

impl Identifier {
    pub fn new(name: impl Into<String>, span: Span) -> Self {
        Self {
            name: name.into(),
            span,
        }
    }
}

/// Source location span
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_display() {
        assert_eq!(Type::I32.to_string(), "i32");
        assert_eq!(Type::Bool.to_string(), "bool");
    }

    #[test]
    fn test_opcode_display() {
        assert_eq!(Opcode::Add.to_string(), "add");
        assert_eq!(Opcode::Jif.to_string(), "jif");
    }
}
