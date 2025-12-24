//! IR Type Definitions
//!
//! Core data structures for the intermediate representation.

use std::collections::HashMap;

use crate::ast::Type;

/// Virtual register identifier
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Reg(pub String);

impl Reg {
    pub fn new(name: impl Into<String>) -> Self {
        Reg(name.into())
    }

    pub fn result() -> Self {
        Reg("result".to_string())
    }

    pub fn temp(n: usize) -> Self {
        Reg(format!("t{}", n))
    }
}

impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}

/// Label identifier for control flow
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Label(pub String);

impl Label {
    pub fn new(name: impl Into<String>) -> Self {
        Label(name.into())
    }

    pub fn numbered(prefix: &str, n: usize) -> Self {
        Label(format!("{}_{}", prefix, n))
    }
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}", self.0)
    }
}

/// Constant values in IR
#[derive(Debug, Clone, PartialEq)]
pub enum IrConst {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Bool(bool),
}

impl IrConst {
    pub fn ir_type(&self) -> IrType {
        match self {
            IrConst::I32(_) => IrType::I32,
            IrConst::I64(_) => IrType::I64,
            IrConst::F32(_) => IrType::F32,
            IrConst::F64(_) => IrType::F64,
            IrConst::Bool(_) => IrType::Bool,
        }
    }
}

/// Types in IR (simplified from AST types)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrType {
    I32,
    I64,
    F32,
    F64,
    Bool,
    Void,
}

impl From<&Type> for IrType {
    fn from(ty: &Type) -> Self {
        match ty {
            // Signed integers: 8/16/32-bit → I32, 64-bit → I64
            Type::I8 | Type::I16 | Type::I32 => IrType::I32,
            Type::I64 => IrType::I64,

            // Unsigned integers: 8/16/32-bit → I32, 64-bit → I64
            Type::U8 | Type::U16 | Type::U32 => IrType::I32,
            Type::U64 => IrType::I64,

            // Floating-point types
            Type::F32 => IrType::F32,
            Type::F64 => IrType::F64,

            // Other primitives
            Type::Bool => IrType::Bool,
            Type::Char => IrType::I32, // UTF-32 codepoint stored as i32
            Type::Void => IrType::Void,

            // Pointer/reference types: 32-bit pointers for WASM32
            Type::Ptr(_) | Type::Ref(_) => IrType::I32,

            // Complex types lowered to I32 (pointer for WASM32)
            Type::Array { .. } | Type::Struct(_) | Type::Enum(_) => IrType::I32,

            // Refined types use their base type's IR representation
            // (resolved during type checking)
            Type::Refined { .. } => IrType::I32,

            // Generic built-in types - represented as i32 pointers in WASM32
            Type::Option(_) | Type::Result { .. } | Type::Vector(_) | Type::Slice(_) => IrType::I32,
            // String types (v0.9+) - represented as pointers
            Type::BmbString | Type::BmbStr => IrType::I32,
            // Box type (v0.13+) - heap-allocated pointer
            Type::BmbBox(_) => IrType::I32,
        }
    }
}

/// Binary operations in IR
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Bitwise operations
    And,
    Or,
    Xor,
    Shl,
    Shr,
    // Comparisons
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl std::fmt::Display for IrBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IrBinOp::Add => write!(f, "add"),
            IrBinOp::Sub => write!(f, "sub"),
            IrBinOp::Mul => write!(f, "mul"),
            IrBinOp::Div => write!(f, "div"),
            IrBinOp::Mod => write!(f, "mod"),
            IrBinOp::And => write!(f, "and"),
            IrBinOp::Or => write!(f, "or"),
            IrBinOp::Xor => write!(f, "xor"),
            IrBinOp::Shl => write!(f, "shl"),
            IrBinOp::Shr => write!(f, "shr"),
            IrBinOp::Eq => write!(f, "eq"),
            IrBinOp::Ne => write!(f, "ne"),
            IrBinOp::Lt => write!(f, "lt"),
            IrBinOp::Le => write!(f, "le"),
            IrBinOp::Gt => write!(f, "gt"),
            IrBinOp::Ge => write!(f, "ge"),
        }
    }
}

/// Unary operations in IR
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrUnaryOp {
    Neg,
    Not,
}

impl std::fmt::Display for IrUnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IrUnaryOp::Neg => write!(f, "neg"),
            IrUnaryOp::Not => write!(f, "not"),
        }
    }
}

/// IR instruction
#[derive(Debug, Clone, PartialEq)]
pub enum IrInst {
    /// Move constant to register: %dest = const
    MovConst { dest: Reg, value: IrConst },

    /// Move between registers: %dest = %src
    MovReg { dest: Reg, src: Reg },

    /// Binary operation: %dest = %left op %right
    BinOp {
        dest: Reg,
        op: IrBinOp,
        left: Reg,
        right: Reg,
    },

    /// Unary operation: %dest = op %operand
    UnaryOp { dest: Reg, op: IrUnaryOp, operand: Reg },

    /// Function call: %dest = call func(%args...)
    Call {
        dest: Option<Reg>,
        func: String,
        args: Vec<Reg>,
    },

    /// Return: ret %value or ret void
    Ret { value: Option<Reg> },

    /// Conditional branch: br %cond, label
    BranchIf { cond: Reg, target: Label },

    /// Unconditional jump: jmp label
    Jump { target: Label },

    /// Label definition
    Label { name: Label },

    /// External call (imported function)
    ExternCall {
        dest: Option<Reg>,
        module: String,
        func: String,
        args: Vec<Reg>,
    },

    /// No operation (placeholder for removed instructions)
    Nop,
}

impl IrInst {
    /// Get the destination register if this instruction defines one
    pub fn dest(&self) -> Option<&Reg> {
        match self {
            IrInst::MovConst { dest, .. }
            | IrInst::MovReg { dest, .. }
            | IrInst::BinOp { dest, .. }
            | IrInst::UnaryOp { dest, .. } => Some(dest),
            IrInst::Call { dest, .. } | IrInst::ExternCall { dest, .. } => dest.as_ref(),
            _ => None,
        }
    }

    /// Get registers used (read) by this instruction
    pub fn uses(&self) -> Vec<&Reg> {
        match self {
            IrInst::MovReg { src, .. } => vec![src],
            IrInst::BinOp { left, right, .. } => vec![left, right],
            IrInst::UnaryOp { operand, .. } => vec![operand],
            IrInst::Call { args, .. } | IrInst::ExternCall { args, .. } => {
                args.iter().collect()
            }
            IrInst::Ret { value } => value.iter().collect(),
            IrInst::BranchIf { cond, .. } => vec![cond],
            _ => vec![],
        }
    }

    /// Check if this is a terminator instruction
    pub fn is_terminator(&self) -> bool {
        matches!(self, IrInst::Ret { .. } | IrInst::Jump { .. })
    }
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct IrParam {
    pub name: String,
    pub ty: IrType,
}

/// IR function
#[derive(Debug, Clone)]
pub struct IrFunction {
    pub name: String,
    pub params: Vec<IrParam>,
    pub return_type: IrType,
    pub body: Vec<IrInst>,

    /// Register types for type checking
    pub reg_types: HashMap<String, IrType>,

    /// Inlining metadata
    pub inline_hint: InlineHint,
    pub instruction_count: usize,
}

impl IrFunction {
    pub fn new(name: impl Into<String>) -> Self {
        IrFunction {
            name: name.into(),
            params: Vec::new(),
            return_type: IrType::Void,
            body: Vec::new(),
            reg_types: HashMap::new(),
            inline_hint: InlineHint::Auto,
            instruction_count: 0,
        }
    }

    /// Count actual instructions (excluding labels and nops)
    pub fn count_instructions(&self) -> usize {
        self.body
            .iter()
            .filter(|inst| !matches!(inst, IrInst::Label { .. } | IrInst::Nop))
            .count()
    }

    /// Check if function is a candidate for inlining
    pub fn should_inline(&self, threshold: usize) -> bool {
        match self.inline_hint {
            InlineHint::Always => true,
            InlineHint::Never => false,
            InlineHint::Auto => {
                // Small functions are good inline candidates
                self.count_instructions() <= threshold
            }
        }
    }

    /// Get all labels defined in this function
    pub fn labels(&self) -> Vec<&Label> {
        self.body
            .iter()
            .filter_map(|inst| {
                if let IrInst::Label { name } = inst {
                    Some(name)
                } else {
                    None
                }
            })
            .collect()
    }
}

/// Inlining hint for functions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineHint {
    /// Let optimizer decide
    Auto,
    /// Always inline this function
    Always,
    /// Never inline this function
    Never,
}

impl Default for InlineHint {
    fn default() -> Self {
        InlineHint::Auto
    }
}

/// Import declaration in IR
#[derive(Debug, Clone)]
pub struct IrImport {
    pub module: String,
    pub func: String,
    pub params: Vec<IrType>,
    pub return_type: IrType,
}

/// Complete IR program
#[derive(Debug, Clone)]
pub struct IrProgram {
    pub imports: Vec<IrImport>,
    pub functions: Vec<IrFunction>,
}

impl IrProgram {
    pub fn new() -> Self {
        IrProgram {
            imports: Vec::new(),
            functions: Vec::new(),
        }
    }

    /// Find a function by name
    pub fn find_function(&self, name: &str) -> Option<&IrFunction> {
        self.functions.iter().find(|f| f.name == name)
    }

    /// Find a mutable function by name
    pub fn find_function_mut(&mut self, name: &str) -> Option<&mut IrFunction> {
        self.functions.iter_mut().find(|f| f.name == name)
    }
}

impl Default for IrProgram {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics about IR transformations
#[derive(Debug, Default)]
pub struct IrStats {
    pub functions_inlined: usize,
    pub instructions_before: usize,
    pub instructions_after: usize,
    pub dead_code_removed: usize,
    pub constants_propagated: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reg_display() {
        assert_eq!(format!("{}", Reg::new("x")), "%x");
        assert_eq!(format!("{}", Reg::result()), "%result");
        assert_eq!(format!("{}", Reg::temp(0)), "%t0");
    }

    #[test]
    fn test_label_display() {
        assert_eq!(format!("{}", Label::new("loop")), "_loop");
        assert_eq!(format!("{}", Label::numbered("bb", 3)), "_bb_3");
    }

    #[test]
    fn test_ir_const_type() {
        assert_eq!(IrConst::I32(42).ir_type(), IrType::I32);
        assert_eq!(IrConst::I64(42).ir_type(), IrType::I64);
        assert_eq!(IrConst::Bool(true).ir_type(), IrType::Bool);
    }

    #[test]
    fn test_instruction_dest() {
        let inst = IrInst::MovConst {
            dest: Reg::new("x"),
            value: IrConst::I32(42),
        };
        assert_eq!(inst.dest(), Some(&Reg::new("x")));

        let inst = IrInst::Ret {
            value: Some(Reg::new("x")),
        };
        assert_eq!(inst.dest(), None);
    }

    #[test]
    fn test_instruction_uses() {
        let inst = IrInst::BinOp {
            dest: Reg::new("z"),
            op: IrBinOp::Add,
            left: Reg::new("x"),
            right: Reg::new("y"),
        };
        let uses = inst.uses();
        assert_eq!(uses.len(), 2);
    }

    #[test]
    fn test_function_inline_decision() {
        let mut func = IrFunction::new("small");
        func.body = vec![
            IrInst::MovConst {
                dest: Reg::result(),
                value: IrConst::I32(42),
            },
            IrInst::Ret {
                value: Some(Reg::result()),
            },
        ];

        // Small function should inline with threshold 5
        assert!(func.should_inline(5));

        // But not with threshold 1
        assert!(!func.should_inline(1));

        // Force never inline
        func.inline_hint = InlineHint::Never;
        assert!(!func.should_inline(100));

        // Force always inline
        func.inline_hint = InlineHint::Always;
        assert!(func.should_inline(0));
    }
}
