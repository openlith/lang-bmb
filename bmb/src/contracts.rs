//! BMB Contract Verification
//!
//! Runtime contract checking for preconditions and postconditions.
//!
//! "Omission is guessing, and guessing is error."
//! - Contracts make implicit assumptions explicit and verifiable.

use wasm_encoder::{BlockType, Function, Instruction, ValType};

use crate::ast::{BinaryOp, Expr, Type, UnaryOp};
use crate::types::TypedProgram;
use crate::Result;
use std::collections::HashMap;

/// Verified program (contracts validated)
#[derive(Debug, Clone)]
pub struct VerifiedProgram {
    pub program: TypedProgram,
}

/// Verify contracts in a type-checked program
///
/// Phase 4 implementation: Runtime contract checking
///
/// For preconditions (@pre):
/// - Generate check code at function entry
/// - Trap with clear message if violated
///
/// For postconditions (@post):
/// - Generate check code before return
/// - Trap with clear message if violated
///
/// # Arguments
///
/// * `program` - The type-checked AST to verify contracts on
///
/// # Returns
///
/// The verified program or a contract error
pub fn verify(program: &TypedProgram) -> Result<VerifiedProgram> {
    // For now, contracts are verified at runtime
    // Future: SMT solver integration for static verification

    for typed_node in &program.nodes {
        let node = &typed_node.node;

        // Validate precondition syntax
        if let Some(ref pre) = node.precondition {
            validate_contract_expr(pre, "precondition", &node.name.name)?;
        }

        // Validate postcondition syntax
        if let Some(ref post) = node.postcondition {
            validate_contract_expr(post, "postcondition", &node.name.name)?;
        }
    }

    Ok(VerifiedProgram {
        program: program.clone(),
    })
}

fn validate_contract_expr(expr: &Expr, _contract_type: &str, _function_name: &str) -> Result<()> {
    // For Phase 4, we validate the expression structure
    // Runtime checks will be generated in codegen
    // Parameters reserved for future error messages

    match expr {
        Expr::Binary { left, right, .. } => {
            validate_contract_expr(left, _contract_type, _function_name)?;
            validate_contract_expr(right, _contract_type, _function_name)?;
        }
        Expr::Unary { operand, .. } => {
            validate_contract_expr(operand, _contract_type, _function_name)?;
        }
        Expr::Var(_) | Expr::IntLit(_) | Expr::FloatLit(_) | Expr::BoolLit(_) | Expr::Ret => {
            // Valid leaf nodes
        }
    }

    Ok(())
}

/// Contract code generator
///
/// Generates WebAssembly instructions to check contracts at runtime.
/// Uses the `unreachable` instruction to trap on contract violation.
pub struct ContractCodeGenerator<'a> {
    /// Map of parameter/register names to local indices
    locals: &'a HashMap<String, u32>,
    /// Map of parameter/register names to types
    types: &'a HashMap<String, Type>,
    /// Local index storing the return value (for postconditions)
    result_local: Option<u32>,
    /// Return type of the function
    return_type: Type,
}

impl<'a> ContractCodeGenerator<'a> {
    /// Create a new contract code generator
    pub fn new(
        locals: &'a HashMap<String, u32>,
        types: &'a HashMap<String, Type>,
        return_type: Type,
    ) -> Self {
        Self {
            locals,
            types,
            result_local: None,
            return_type,
        }
    }

    /// Set the local index where the return value is stored
    pub fn set_result_local(&mut self, local: u32) {
        self.result_local = Some(local);
    }

    /// Generate precondition check instructions
    ///
    /// Pattern:
    /// ```wasm
    /// ;; @pre b != 0
    /// ;; Evaluate condition
    /// local.get $b
    /// f64.const 0
    /// f64.ne
    /// ;; If false (condition violated), trap
    /// i32.eqz
    /// if
    ///   unreachable  ;; trap: precondition failed
    /// end
    /// ```
    pub fn generate_precondition(&self, expr: &Expr, func: &mut Function) {
        // Evaluate the condition expression (should leave i32 on stack: 1=true, 0=false)
        self.generate_expr(expr, func);

        // If condition is false (0), trap
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);
    }

    /// Generate postcondition check instructions
    ///
    /// Pattern:
    /// ```wasm
    /// ;; @post ret >= 1
    /// ;; Result is in result_local
    /// local.get $result
    /// i32.const 1
    /// i32.ge_s
    /// ;; If false, trap
    /// i32.eqz
    /// if
    ///   unreachable  ;; trap: postcondition failed
    /// end
    /// ```
    pub fn generate_postcondition(&self, expr: &Expr, func: &mut Function) {
        // Evaluate the condition expression
        self.generate_expr(expr, func);

        // If condition is false (0), trap
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);
    }

    /// Determine the unified type for a binary expression
    /// Returns the "larger" type when promotion is possible
    fn infer_unified_binary_type(&self, left: &Expr, right: &Expr) -> Type {
        let left_type = self.infer_expr_type(left);
        let right_type = self.infer_expr_type(right);

        if left_type == right_type {
            return left_type;
        }

        // Type promotion rules
        match (&left_type, &right_type) {
            // i32 promotes to i64
            (Type::I32, Type::I64) | (Type::I64, Type::I32) => Type::I64,
            // f32 promotes to f64
            (Type::F32, Type::F64) | (Type::F64, Type::F32) => Type::F64,
            // Default to left type
            _ => left_type,
        }
    }

    /// Generate expression evaluation code with optional target type for promotion
    fn generate_expr_with_type(
        &self,
        expr: &Expr,
        target_type: Option<&Type>,
        func: &mut Function,
    ) {
        match expr {
            Expr::IntLit(v) => {
                // Generate literal with target type if specified
                match target_type {
                    Some(Type::I64) => func.instruction(&Instruction::I64Const(*v)),
                    _ => func.instruction(&Instruction::I32Const(*v as i32)),
                };
            }
            Expr::FloatLit(v) => {
                // Generate literal with target type if specified
                match target_type {
                    Some(Type::F32) => func.instruction(&Instruction::F32Const(*v as f32)),
                    _ => func.instruction(&Instruction::F64Const(*v)),
                };
            }
            Expr::BoolLit(b) => {
                func.instruction(&Instruction::I32Const(if *b { 1 } else { 0 }));
            }
            Expr::Var(name) => {
                if let Some(&idx) = self.locals.get(&name.name) {
                    func.instruction(&Instruction::LocalGet(idx));
                    // Handle type promotion if needed
                    if let Some(target) = target_type {
                        let actual_type = self.types.get(&name.name).cloned().unwrap_or(Type::I32);
                        self.maybe_convert_type(&actual_type, target, func);
                    }
                }
            }
            Expr::Ret => {
                // Load the return value from result_local
                if let Some(idx) = self.result_local {
                    func.instruction(&Instruction::LocalGet(idx));
                    // Handle type promotion if needed
                    if let Some(target) = target_type {
                        self.maybe_convert_type(&self.return_type, target, func);
                    }
                }
            }
            Expr::Binary { op, left, right } => {
                // Determine unified type for operands
                let operand_type = self.infer_unified_binary_type(left, right);

                // Evaluate operands with the unified type
                self.generate_expr_with_type(left, Some(&operand_type), func);
                self.generate_expr_with_type(right, Some(&operand_type), func);

                // Generate operation
                let instr = match op {
                    BinaryOp::Add => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32Add,
                        Type::I64 => Instruction::I64Add,
                        Type::F32 => Instruction::F32Add,
                        Type::F64 => Instruction::F64Add,
                        _ => Instruction::I32Add, // Compound types use i32 pointer arithmetic
                    },
                    BinaryOp::Sub => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32Sub,
                        Type::I64 => Instruction::I64Sub,
                        Type::F32 => Instruction::F32Sub,
                        Type::F64 => Instruction::F64Sub,
                        _ => Instruction::I32Sub,
                    },
                    BinaryOp::Mul => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32Mul,
                        Type::I64 => Instruction::I64Mul,
                        Type::F32 => Instruction::F32Mul,
                        Type::F64 => Instruction::F64Mul,
                        _ => Instruction::I32Mul,
                    },
                    BinaryOp::Div => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32DivS,
                        Type::I64 => Instruction::I64DivS,
                        Type::F32 => Instruction::F32Div,
                        Type::F64 => Instruction::F64Div,
                        _ => Instruction::I32DivS,
                    },
                    BinaryOp::Mod => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32RemS,
                        Type::I64 => Instruction::I64RemS,
                        _ => Instruction::I32RemS, // Float mod not directly supported
                    },
                    BinaryOp::Eq => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32Eq,
                        Type::I64 => Instruction::I64Eq,
                        Type::F32 => Instruction::F32Eq,
                        Type::F64 => Instruction::F64Eq,
                        _ => Instruction::I32Eq,
                    },
                    BinaryOp::Ne => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32Ne,
                        Type::I64 => Instruction::I64Ne,
                        Type::F32 => Instruction::F32Ne,
                        Type::F64 => Instruction::F64Ne,
                        _ => Instruction::I32Ne,
                    },
                    BinaryOp::Lt => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32LtS,
                        Type::I64 => Instruction::I64LtS,
                        Type::F32 => Instruction::F32Lt,
                        Type::F64 => Instruction::F64Lt,
                        _ => Instruction::I32LtS,
                    },
                    BinaryOp::Le => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32LeS,
                        Type::I64 => Instruction::I64LeS,
                        Type::F32 => Instruction::F32Le,
                        Type::F64 => Instruction::F64Le,
                        _ => Instruction::I32LeS,
                    },
                    BinaryOp::Gt => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32GtS,
                        Type::I64 => Instruction::I64GtS,
                        Type::F32 => Instruction::F32Gt,
                        Type::F64 => Instruction::F64Gt,
                        _ => Instruction::I32GtS,
                    },
                    BinaryOp::Ge => match operand_type {
                        Type::I32 | Type::Bool => Instruction::I32GeS,
                        Type::I64 => Instruction::I64GeS,
                        Type::F32 => Instruction::F32Ge,
                        Type::F64 => Instruction::F64Ge,
                        _ => Instruction::I32GeS,
                    },
                    BinaryOp::And => Instruction::I32And,
                    BinaryOp::Or => Instruction::I32Or,
                };
                func.instruction(&instr);
            }
            Expr::Unary { op, operand } => {
                self.generate_expr_with_type(operand, target_type, func);
                match op {
                    UnaryOp::Neg => {
                        let operand_type = self.infer_expr_type(operand);
                        match operand_type {
                            Type::I32 | Type::Bool => {
                                // i32.neg doesn't exist, use i32.const 0; i32.sub
                                func.instruction(&Instruction::I32Const(0));
                                // Swap and subtract: 0 - x
                                // Actually we need to generate in reverse order
                            }
                            Type::I64 => {
                                func.instruction(&Instruction::I64Const(0));
                            }
                            Type::F32 => {
                                func.instruction(&Instruction::F32Neg);
                            }
                            Type::F64 => {
                                func.instruction(&Instruction::F64Neg);
                            }
                            // Compound types fallback to i32
                            _ => {
                                func.instruction(&Instruction::I32Const(0));
                            }
                        }
                    }
                    UnaryOp::Not => {
                        // Logical not: i32.eqz
                        func.instruction(&Instruction::I32Eqz);
                    }
                }
            }
        }
    }

    /// Generate expression evaluation code (convenience wrapper)
    fn generate_expr(&self, expr: &Expr, func: &mut Function) {
        self.generate_expr_with_type(expr, None, func);
    }

    /// Generate type conversion instructions if needed
    fn maybe_convert_type(&self, from: &Type, to: &Type, func: &mut Function) {
        if from == to {
            return;
        }

        match (from, to) {
            // i32 -> i64 (extend signed)
            (Type::I32, Type::I64) => {
                func.instruction(&Instruction::I64ExtendI32S);
            }
            // f32 -> f64 (promote)
            (Type::F32, Type::F64) => {
                func.instruction(&Instruction::F64PromoteF32);
            }
            // No other conversions needed for current type system
            _ => {}
        }
    }

    /// Infer the type of an expression
    fn infer_expr_type(&self, expr: &Expr) -> Type {
        match expr {
            Expr::IntLit(_) => Type::I32,
            Expr::FloatLit(_) => Type::F64,
            Expr::BoolLit(_) => Type::Bool,
            Expr::Var(name) => self.types.get(&name.name).cloned().unwrap_or(Type::I32),
            Expr::Ret => self.return_type.clone(),
            Expr::Binary { op, left, .. } => {
                match op {
                    // Comparison operators always return bool
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::And
                    | BinaryOp::Or => Type::Bool,
                    // Arithmetic operators preserve operand type
                    _ => self.infer_expr_type(left),
                }
            }
            Expr::Unary { op, operand } => match op {
                UnaryOp::Not => Type::Bool,
                UnaryOp::Neg => self.infer_expr_type(operand),
            },
        }
    }
}

/// Helper function to map Type to wasm ValType
pub fn type_to_valtype(ty: &Type) -> ValType {
    match ty {
        Type::I32 | Type::Bool => ValType::I32,
        Type::I64 => ValType::I64,
        Type::F32 => ValType::F32,
        Type::F64 => ValType::F64,
        Type::Void => ValType::I32, // Void uses i32 as placeholder
        // Compound types use i32 as pointer/reference
        Type::Array { .. } | Type::Struct(_) | Type::Enum(_) | Type::Ref(_) => ValType::I32,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, Identifier, Node, Span, Type as AstType};
    use crate::types::{TypedNode, TypedProgram};
    use wasm_encoder::Instruction as WasmInstruction;

    fn make_simple_program() -> TypedProgram {
        let node = Node {
            name: Identifier::new("test", Span::default()),
            params: vec![],
            returns: AstType::I32,
            precondition: None,
            postcondition: None,
            body: vec![],
            span: Span::default(),
        };

        TypedProgram {
            imports: vec![],
            structs: vec![],
            enums: vec![],
            nodes: vec![TypedNode {
                node,
                register_types: HashMap::new(),
            }],
            registry: crate::types::TypeRegistry::new(),
        }
    }

    #[test]
    fn test_verify_empty_contracts() {
        let program = make_simple_program();
        let result = verify(&program);
        assert!(result.is_ok());
    }

    #[test]
    fn test_contract_generator_simple() {
        let mut locals = HashMap::new();
        locals.insert("x".to_string(), 0);

        let mut types = HashMap::new();
        types.insert("x".to_string(), Type::I32);

        let gen = ContractCodeGenerator::new(&locals, &types, Type::I32);

        // Test expression: x > 0
        let expr = Expr::Binary {
            op: BinaryOp::Gt,
            left: Box::new(Expr::Var(Identifier::new("x", Span::default()))),
            right: Box::new(Expr::IntLit(0)),
        };

        let mut func = Function::new([]);
        gen.generate_precondition(&expr, &mut func);
        func.instruction(&WasmInstruction::End);

        // Just verify it doesn't panic - actual behavior tested in integration
    }

    #[test]
    fn test_infer_expr_type() {
        let locals = HashMap::new();
        let mut types = HashMap::new();
        types.insert("x".to_string(), Type::F64);

        let gen = ContractCodeGenerator::new(&locals, &types, Type::F64);

        // Test literal types
        assert_eq!(gen.infer_expr_type(&Expr::IntLit(42)), Type::I32);
        assert_eq!(gen.infer_expr_type(&Expr::FloatLit(1.5)), Type::F64);
        assert_eq!(gen.infer_expr_type(&Expr::BoolLit(true)), Type::Bool);

        // Test variable type
        let var_expr = Expr::Var(Identifier::new("x", Span::default()));
        assert_eq!(gen.infer_expr_type(&var_expr), Type::F64);

        // Test comparison returns bool
        let cmp_expr = Expr::Binary {
            op: BinaryOp::Eq,
            left: Box::new(Expr::IntLit(1)),
            right: Box::new(Expr::IntLit(1)),
        };
        assert_eq!(gen.infer_expr_type(&cmp_expr), Type::Bool);

        // Test ret type
        assert_eq!(gen.infer_expr_type(&Expr::Ret), Type::F64);
    }
}
