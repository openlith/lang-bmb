//! Abstract Syntax Tree definitions for BMB
//!
//! The AST represents the structure of BMB programs after parsing.

use std::fmt;

/// A complete BMB program consisting of imports, type definitions, and nodes
#[derive(Debug, Clone)]
pub struct Program {
    /// External function imports (@import)
    pub imports: Vec<Import>,
    /// Module imports (@use)
    pub uses: Vec<ModuleUse>,
    pub structs: Vec<StructDef>,
    pub enums: Vec<EnumDef>,
    pub nodes: Vec<Node>,
}

/// A module import: @use "path/to/module.bmb" as alias
#[derive(Debug, Clone)]
pub struct ModuleUse {
    /// The module path (either a file path or module name)
    pub path: ModulePath,
    /// Optional alias for the module
    pub alias: Option<Identifier>,
    pub span: Span,
}

/// Module path variants
#[derive(Debug, Clone)]
pub enum ModulePath {
    /// A file path: "path/to/module.bmb"
    FilePath(String),
    /// A module name: math
    Name(Identifier),
}

/// A struct definition
#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: Identifier,
    pub fields: Vec<StructField>,
    pub span: Span,
}

/// A field in a struct
#[derive(Debug, Clone)]
pub struct StructField {
    pub name: Identifier,
    pub ty: Type,
    pub span: Span,
}

/// An enum definition
#[derive(Debug, Clone)]
pub struct EnumDef {
    pub name: Identifier,
    pub variants: Vec<EnumVariant>,
    pub span: Span,
}

/// A variant in an enum
#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: Identifier,
    pub payload: Option<Type>,
    pub span: Span,
}

/// An external function import
#[derive(Debug, Clone)]
pub struct Import {
    pub name: Identifier,
    pub param_types: Vec<Type>,
    pub span: Span,
}

/// A loop invariant attached to a label
#[derive(Debug, Clone)]
pub struct Invariant {
    pub label: Identifier,
    pub condition: Expr,
    pub span: Span,
}

/// A function node in BMB
#[derive(Debug, Clone)]
pub struct Node {
    pub name: Identifier,
    pub params: Vec<Parameter>,
    pub returns: Type,
    pub precondition: Option<Expr>,
    pub postcondition: Option<Expr>,
    /// Loop invariants: @invariant _label condition
    pub invariants: Vec<Invariant>,
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
    // Primitive types
    I32,
    I64,
    F32,
    F64,
    Bool,
    Void,

    // Compound types
    /// Fixed-size array: [T; N]
    Array {
        element: Box<Type>,
        size: usize,
    },
    /// User-defined struct type
    Struct(String),
    /// User-defined enum type
    Enum(String),
    /// Reference type: &T
    Ref(Box<Type>),
}

impl Type {
    /// Returns true if this is a primitive type
    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            Type::I32 | Type::I64 | Type::F32 | Type::F64 | Type::Bool | Type::Void
        )
    }

    /// Returns true if this is a numeric type
    pub fn is_numeric(&self) -> bool {
        matches!(self, Type::I32 | Type::I64 | Type::F32 | Type::F64)
    }

    /// Returns true if this is an integer type
    pub fn is_integer(&self) -> bool {
        matches!(self, Type::I32 | Type::I64)
    }

    /// Returns true if this is a float type
    pub fn is_float(&self) -> bool {
        matches!(self, Type::F32 | Type::F64)
    }

    /// Returns the size in bytes for primitive types
    pub fn size_bytes(&self) -> Option<usize> {
        match self {
            Type::I32 | Type::F32 => Some(4),
            Type::I64 | Type::F64 => Some(8),
            Type::Bool => Some(1),
            Type::Void => Some(0),
            _ => None, // Compound types need context to determine size
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::Bool => write!(f, "bool"),
            Type::Void => write!(f, "void"),
            Type::Array { element, size } => write!(f, "[{}; {}]", element, size),
            Type::Struct(name) => write!(f, "{}", name),
            Type::Enum(name) => write!(f, "{}", name),
            Type::Ref(inner) => write!(f, "&{}", inner),
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
    /// External call (void function, no return value)
    Xcall,

    // Variables
    Mov,
    Load,
    Store,

    // I/O
    /// Print a string literal to stdout
    Print,
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
            Opcode::Xcall => write!(f, "xcall"),
            Opcode::Mov => write!(f, "mov"),
            Opcode::Load => write!(f, "load"),
            Opcode::Store => write!(f, "store"),
            Opcode::Print => write!(f, "print"),
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
    /// String literal: "Hello, World!\n"
    StringLiteral(String),
    /// Identifier (variable or function name)
    Identifier(Identifier),
    /// Qualified identifier: module::function
    QualifiedIdent {
        module: Identifier,
        name: Identifier,
    },
    /// Field access: obj.field
    FieldAccess {
        base: Identifier,
        field: Identifier,
    },
    /// Array access: arr[index]
    ArrayAccess {
        base: Identifier,
        index: Box<Operand>,
    },
}

/// Index for array access
#[derive(Debug, Clone)]
pub enum ArrayIndex {
    /// Constant index
    Const(usize),
    /// Register-based index
    Register(Identifier),
    /// Variable-based index
    Var(Identifier),
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
    /// Old value reference (for postconditions): old(x) refers to x's value at function entry
    Old(Box<Expr>),
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
