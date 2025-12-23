//! Abstract Syntax Tree definitions for BMB
//!
//! The AST represents the structure of BMB programs after parsing.

use std::fmt;

/// A complete BMB program consisting of imports, type definitions, contracts, and nodes
#[derive(Debug, Clone)]
pub struct Program {
    /// Module declaration (@module / @.) - Index system
    pub module: Option<ModuleDecl>,
    /// External function imports (@import)
    pub imports: Vec<Import>,
    /// Module imports (@use)
    pub uses: Vec<ModuleUse>,
    /// Refined type definitions (@type) - v0.8+
    pub type_defs: Vec<TypeDef>,
    pub structs: Vec<StructDef>,
    pub enums: Vec<EnumDef>,
    /// Named contract definitions (@contract)
    pub contracts: Vec<ContractDef>,
    pub nodes: Vec<Node>,
}

/// Module declaration for the Index system (replaces documentation)
/// @module math.arithmetic  OR  @. math.arithmetic
#[derive(Debug, Clone)]
pub struct ModuleDecl {
    /// Dot-separated module path: ["math", "arithmetic"]
    pub path: Vec<Identifier>,
    pub span: Span,
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

/// A named contract definition (@contract / @#c)
/// Reusable contract templates that can be referenced by @requires
#[derive(Debug, Clone)]
pub struct ContractDef {
    /// Contract name (e.g., "positive_range")
    pub name: Identifier,
    /// Contract parameters with types
    pub params: Vec<Parameter>,
    /// Preconditions (@pre)
    pub preconditions: Vec<Expr>,
    /// Postconditions (@post)
    pub postconditions: Vec<Expr>,
    pub span: Span,
}

/// A refined type definition (@type / @#t) - v0.8+
/// Signal Density Optimization: constraints embedded in type names
/// Example: @type nz_i32 i32 where self != 0
#[derive(Debug, Clone)]
pub struct TypeDef {
    /// Type name (e.g., "nz_i32", "pos_i32")
    pub name: Identifier,
    /// Type parameters for parameterized refined types (e.g., [N] in index[N])
    pub params: Vec<Identifier>,
    /// Base type being refined
    pub base_type: Type,
    /// Constraint expression (uses `self` to refer to the value)
    pub constraint: Expr,
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

/// A termination proof variant (@variant / @%)
/// The measure expression must decrease with each recursive call or loop iteration
#[derive(Debug, Clone)]
pub struct Variant {
    /// The measure expression that must decrease toward a base case
    pub measure: Expr,
    pub span: Span,
}

/// A contract reference (@requires / @&)
/// References a named contract or another node's contract for reuse
#[derive(Debug, Clone)]
pub struct Requires {
    /// The referenced contract name
    pub contract: Identifier,
    /// Arguments to bind to the contract parameters
    pub args: Vec<Expr>,
    pub span: Span,
}

/// A function node in BMB
#[derive(Debug, Clone)]
pub struct Node {
    pub name: Identifier,
    /// Tags for Index system (@tags / @#) - replaces documentation
    pub tags: Vec<Identifier>,
    pub params: Vec<Parameter>,
    pub returns: Type,
    /// Multiple preconditions allowed (@pre / @<)
    pub preconditions: Vec<Expr>,
    /// Multiple postconditions allowed (@post / @>)
    pub postconditions: Vec<Expr>,
    /// Loop invariants: @invariant _label condition (@~ compact)
    pub invariants: Vec<Invariant>,
    /// Termination proof variants: @variant measure (@% compact)
    pub variants: Vec<Variant>,
    /// Purity annotation: @pure (@! compact) - no side effects
    pub pure: bool,
    /// Contract references: @requires contract(args) (@& compact)
    pub requires: Vec<Requires>,
    /// Inline assertions: @assert condition (@!! compact)
    pub assertions: Vec<Assert>,
    /// Test cases: @test expect(...) (@? compact)
    pub tests: Vec<TestCase>,
    pub body: Vec<Instruction>,
    pub span: Span,
}

/// An inline assertion (@assert / @!!)
#[derive(Debug, Clone)]
pub struct Assert {
    pub condition: Expr,
    pub span: Span,
}

/// A test case (@test / @?)
#[derive(Debug, Clone)]
pub struct TestCase {
    /// Test function name (e.g., "expect")
    pub function: Identifier,
    /// Test arguments
    pub args: Vec<TestArg>,
    pub span: Span,
}

/// Argument in a test case
#[derive(Debug, Clone)]
pub enum TestArg {
    /// Integer literal
    Int(i64),
    /// Float literal
    Float(f64),
    /// Boolean literal
    Bool(bool),
    /// Variable reference
    Var(Identifier),
    /// Function call: factorial(5)
    Call { func: Identifier, args: Vec<TestArg> },
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
    // Signed integer types
    I8,
    I16,
    I32,
    I64,

    // Unsigned integer types
    U8,
    U16,
    U32,
    U64,

    // Floating-point types
    F32,
    F64,

    // Other primitive types
    Bool,
    Char,
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
    /// Pointer type: *T (raw pointer for low-level memory access)
    Ptr(Box<Type>),
    /// Refined type reference (v0.8+)
    /// References a refined type by name, e.g., nz_i32, pos_i32
    /// The constraint is expanded at verification time
    Refined {
        /// Name of the refined type
        name: String,
        /// Type arguments for parameterized refined types (e.g., [N] values as strings)
        args: Vec<String>,
    },
}

impl Type {
    /// Returns true if this is a primitive type
    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            Type::I8
                | Type::I16
                | Type::I32
                | Type::I64
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::F32
                | Type::F64
                | Type::Bool
                | Type::Char
                | Type::Void
        )
    }

    /// Returns true if this is a numeric type (integers and floats)
    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float()
    }

    /// Returns true if this is an integer type (signed or unsigned)
    pub fn is_integer(&self) -> bool {
        self.is_signed_integer() || self.is_unsigned_integer()
    }

    /// Returns true if this is a signed integer type
    pub fn is_signed_integer(&self) -> bool {
        matches!(self, Type::I8 | Type::I16 | Type::I32 | Type::I64)
    }

    /// Returns true if this is an unsigned integer type
    pub fn is_unsigned_integer(&self) -> bool {
        matches!(self, Type::U8 | Type::U16 | Type::U32 | Type::U64)
    }

    /// Returns true if this is a float type
    pub fn is_float(&self) -> bool {
        matches!(self, Type::F32 | Type::F64)
    }

    /// Returns true if this is a pointer type
    pub fn is_pointer(&self) -> bool {
        matches!(self, Type::Ptr(_))
    }

    /// Returns true if this is a reference type
    pub fn is_reference(&self) -> bool {
        matches!(self, Type::Ref(_))
    }

    /// Returns the size in bytes for primitive types
    pub fn size_bytes(&self) -> Option<usize> {
        match self {
            Type::I8 | Type::U8 | Type::Bool => Some(1),
            Type::I16 | Type::U16 => Some(2),
            Type::I32 | Type::U32 | Type::F32 | Type::Char => Some(4),
            Type::I64 | Type::U64 | Type::F64 => Some(8),
            Type::Ptr(_) | Type::Ref(_) => Some(4), // 32-bit pointers for WASM32
            Type::Void => Some(0),
            _ => None, // Compound types need context to determine size
        }
    }

    /// Returns the inner type for pointer and reference types
    pub fn inner_type(&self) -> Option<&Type> {
        match self {
            Type::Ptr(inner) | Type::Ref(inner) => Some(inner),
            _ => None,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::Bool => write!(f, "bool"),
            Type::Char => write!(f, "char"),
            Type::Void => write!(f, "void"),
            Type::Array { element, size } => write!(f, "[{}; {}]", element, size),
            Type::Struct(name) => write!(f, "{}", name),
            Type::Enum(name) => write!(f, "{}", name),
            Type::Ref(inner) => write!(f, "&{}", inner),
            Type::Ptr(inner) => write!(f, "*{}", inner),
            Type::Refined { name, args } => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}[{}]", name, args.join(", "))
                }
            }
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

    // Bitwise operations
    /// Bitwise AND: and %r a b → a & b
    And,
    /// Bitwise OR: or %r a b → a | b
    Or,
    /// Bitwise XOR: xor %r a b → a ^ b
    Xor,
    /// Shift left: shl %r a n → a << n
    Shl,
    /// Shift right: shr %r a n → a >> n
    Shr,
    /// Bitwise NOT: not %r a → ~a
    Not,

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
            Opcode::And => write!(f, "and"),
            Opcode::Or => write!(f, "or"),
            Opcode::Xor => write!(f, "xor"),
            Opcode::Shl => write!(f, "shl"),
            Opcode::Shr => write!(f, "shr"),
            Opcode::Not => write!(f, "not"),
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
    /// Self reference (for refined type constraints): refers to the value being constrained
    SelfRef,
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
