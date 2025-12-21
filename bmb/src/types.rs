//! BMB Type System
//!
//! Type checking and inference for BMB programs.

use std::collections::HashMap;

use crate::ast::*;
use crate::{BmbError, Result};

/// Type-checked AST (extends AST with type annotations)
#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub nodes: Vec<TypedNode>,
}

/// A type-checked node
#[derive(Debug, Clone)]
pub struct TypedNode {
    pub node: Node,
    pub register_types: HashMap<String, Type>,
}

/// Type environment for tracking variable types
#[derive(Debug, Default)]
pub struct TypeEnv {
    /// Parameter types
    params: HashMap<String, Type>,
    /// Register types (inferred during type checking)
    registers: HashMap<String, Type>,
    /// Function signatures (for call type checking)
    functions: HashMap<String, FunctionSig>,
    /// Current function's return type (for postcondition 'ret' keyword)
    return_type: Option<Type>,
}

/// Function signature for type checking calls
#[derive(Debug, Clone)]
pub struct FunctionSig {
    pub params: Vec<Type>,
    pub returns: Type,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_param(&mut self, name: &str, ty: Type) {
        self.params.insert(name.to_string(), ty);
    }

    pub fn add_register(&mut self, name: &str, ty: Type) {
        self.registers.insert(name.to_string(), ty);
    }

    pub fn add_function(&mut self, name: &str, sig: FunctionSig) {
        self.functions.insert(name.to_string(), sig);
    }

    pub fn set_return_type(&mut self, ty: Type) {
        self.return_type = Some(ty);
    }

    pub fn get_return_type(&self) -> Option<&Type> {
        self.return_type.as_ref()
    }

    pub fn get_type(&self, name: &str) -> Option<&Type> {
        self.params.get(name).or_else(|| self.registers.get(name))
    }

    pub fn get_function(&self, name: &str) -> Option<&FunctionSig> {
        self.functions.get(name)
    }
}

/// Perform type checking on a parsed program
///
/// # Arguments
///
/// * `program` - The parsed AST to type check
///
/// # Returns
///
/// The type-checked AST or a type error
pub fn typecheck(program: &Program) -> Result<TypedProgram> {
    let mut typed_nodes = Vec::new();
    let mut global_env = TypeEnv::new();

    // First pass: collect function signatures
    for node in &program.nodes {
        let sig = FunctionSig {
            params: node.params.iter().map(|p| p.ty.clone()).collect(),
            returns: node.returns.clone(),
        };
        global_env.add_function(&node.name.name, sig);
    }

    // Second pass: type check each function
    for node in &program.nodes {
        let typed_node = typecheck_node(node, &global_env)?;
        typed_nodes.push(typed_node);
    }

    Ok(TypedProgram { nodes: typed_nodes })
}

fn typecheck_node(node: &Node, global_env: &TypeEnv) -> Result<TypedNode> {
    let mut env = TypeEnv::new();

    // Copy function signatures
    for (name, sig) in &global_env.functions {
        env.add_function(name, sig.clone());
    }

    // Add parameters to environment
    for param in &node.params {
        env.add_param(&param.name.name, param.ty.clone());
    }

    // Store return type for contract checking
    env.set_return_type(node.returns.clone());

    // Type check body
    for instruction in &node.body {
        match instruction {
            Instruction::Label(_) => {
                // Labels don't affect types
            }
            Instruction::Statement(stmt) => {
                typecheck_statement(stmt, &mut env, &node.returns)?;
            }
        }
    }

    // Type check contracts
    if let Some(ref pre) = node.precondition {
        let pre_type = typecheck_expr(pre, &env)?;
        if pre_type != Type::Bool {
            return Err(BmbError::TypeError {
                message: format!("Precondition must be bool, got {}", pre_type),
            });
        }
    }

    if let Some(ref post) = node.postcondition {
        let post_type = typecheck_expr(post, &env)?;
        if post_type != Type::Bool {
            return Err(BmbError::TypeError {
                message: format!("Postcondition must be bool, got {}", post_type),
            });
        }
    }

    Ok(TypedNode {
        node: node.clone(),
        register_types: env.registers,
    })
}

fn typecheck_statement(stmt: &Statement, env: &mut TypeEnv, return_type: &Type) -> Result<()> {
    match stmt.opcode {
        Opcode::Add | Opcode::Sub | Opcode::Mul | Opcode::Div | Opcode::Mod => {
            // Arithmetic: %dest = op %a %b
            // All operands must be same numeric type
            if stmt.operands.len() != 3 {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} requires 3 operands, got {}",
                        stmt.opcode,
                        stmt.operands.len()
                    ),
                });
            }

            let (type_a, type_b) = get_operand_types(&stmt.operands[1], &stmt.operands[2], env)?;

            if type_a != type_b {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} operands must have same type: {} vs {}",
                        stmt.opcode, type_a, type_b
                    ),
                });
            }

            // Set result register type
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, type_a);
            }
        }

        Opcode::Eq | Opcode::Ne | Opcode::Lt | Opcode::Le | Opcode::Gt | Opcode::Ge => {
            // Comparison: %dest = op %a %b
            // Operands must be same type, result is bool
            if stmt.operands.len() != 3 {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} requires 3 operands, got {}",
                        stmt.opcode,
                        stmt.operands.len()
                    ),
                });
            }

            let (type_a, type_b) = get_operand_types(&stmt.operands[1], &stmt.operands[2], env)?;

            if type_a != type_b {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} operands must have same type: {} vs {}",
                        stmt.opcode, type_a, type_b
                    ),
                });
            }

            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, Type::Bool);
            }
        }

        Opcode::Ret => {
            // Return: ret %value or ret literal
            if stmt.operands.len() != 1 {
                return Err(BmbError::TypeError {
                    message: format!("ret requires 1 operand, got {}", stmt.operands.len()),
                });
            }

            let ret_type = get_operand_type(&stmt.operands[0], env)?;
            if ret_type != *return_type {
                return Err(BmbError::TypeError {
                    message: format!(
                        "Return type mismatch: expected {}, got {}",
                        return_type, ret_type
                    ),
                });
            }
        }

        Opcode::Jmp => {
            // Jump: jmp _label
            if stmt.operands.len() != 1 {
                return Err(BmbError::TypeError {
                    message: format!("jmp requires 1 operand, got {}", stmt.operands.len()),
                });
            }
        }

        Opcode::Jif => {
            // Conditional jump: jif %cond _label
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!("jif requires 2 operands, got {}", stmt.operands.len()),
                });
            }

            let cond_type = get_operand_type(&stmt.operands[0], env)?;
            if cond_type != Type::Bool {
                return Err(BmbError::TypeError {
                    message: format!("jif condition must be bool, got {}", cond_type),
                });
            }
        }

        Opcode::Call => {
            // Call: %dest = call func %args...
            if stmt.operands.len() < 2 {
                return Err(BmbError::TypeError {
                    message: "call requires at least 2 operands".to_string(),
                });
            }

            // Get function name
            if let Operand::Identifier(ref func) = stmt.operands[1] {
                if let Some(sig) = env.get_function(&func.name) {
                    // Set result register type
                    if let Operand::Register(ref r) = stmt.operands[0] {
                        env.add_register(&r.name, sig.returns.clone());
                    }
                } else {
                    return Err(BmbError::TypeError {
                        message: format!("Unknown function: {}", func.name),
                    });
                }
            }
        }

        Opcode::Mov => {
            // Move: mov %dest %src or mov %dest literal
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!("mov requires 2 operands, got {}", stmt.operands.len()),
                });
            }

            let src_type = get_operand_type(&stmt.operands[1], env)?;
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, src_type);
            }
        }

        Opcode::Load | Opcode::Store => {
            // Memory operations (future expansion)
        }
    }

    Ok(())
}

fn get_operand_type(operand: &Operand, env: &TypeEnv) -> Result<Type> {
    match operand {
        Operand::Register(r) => env
            .get_type(&r.name)
            .cloned()
            .ok_or_else(|| BmbError::TypeError {
                message: format!("Unknown register: %{}", r.name),
            }),
        Operand::Identifier(id) => {
            env.get_type(&id.name)
                .cloned()
                .ok_or_else(|| BmbError::TypeError {
                    message: format!("Unknown variable: {}", id.name),
                })
        }
        Operand::IntLiteral(_) => Ok(Type::I32), // Default integer type
        Operand::FloatLiteral(_) => Ok(Type::F64), // Default float type
        Operand::Label(_) => Err(BmbError::TypeError {
            message: "Label cannot be used as value".to_string(),
        }),
    }
}

fn get_operand_types(a: &Operand, b: &Operand, env: &TypeEnv) -> Result<(Type, Type)> {
    Ok((get_operand_type(a, env)?, get_operand_type(b, env)?))
}

/// Determine the common type for comparison, with literal promotion
/// Returns Some(unified_type) if types are compatible, None otherwise
fn unified_comparison_type(left: &Type, right: &Type) -> Option<Type> {
    if left == right {
        return Some(left.clone());
    }

    // Integer promotion: i32 can be promoted to i64
    match (left, right) {
        (Type::I32, Type::I64) | (Type::I64, Type::I32) => Some(Type::I64),
        // Float promotion: f32 can be compared with f64 (f32 promoted to f64)
        (Type::F32, Type::F64) | (Type::F64, Type::F32) => Some(Type::F64),
        _ => None,
    }
}

fn typecheck_expr(expr: &Expr, env: &TypeEnv) -> Result<Type> {
    match expr {
        Expr::Binary { left, op, right } => {
            let left_type = typecheck_expr(left, env)?;
            let right_type = typecheck_expr(right, env)?;

            match op {
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                    // Arithmetic: try promotion for contracts, strict match otherwise
                    if let Some(unified) = unified_comparison_type(&left_type, &right_type) {
                        Ok(unified)
                    } else {
                        Err(BmbError::TypeError {
                            message: format!(
                                "Arithmetic type mismatch: {} vs {}",
                                left_type, right_type
                            ),
                        })
                    }
                }
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge => {
                    // Comparison: allow type promotion (i32 <-> i64, f32 <-> f64)
                    if unified_comparison_type(&left_type, &right_type).is_some() {
                        Ok(Type::Bool)
                    } else {
                        Err(BmbError::TypeError {
                            message: format!(
                                "Comparison type mismatch: {} vs {}",
                                left_type, right_type
                            ),
                        })
                    }
                }
                BinaryOp::And | BinaryOp::Or => {
                    if left_type != Type::Bool || right_type != Type::Bool {
                        return Err(BmbError::TypeError {
                            message: "Logical operators require bool operands".to_string(),
                        });
                    }
                    Ok(Type::Bool)
                }
            }
        }
        Expr::Unary { op, operand } => {
            let operand_type = typecheck_expr(operand, env)?;
            match op {
                UnaryOp::Neg => Ok(operand_type),
                UnaryOp::Not => {
                    if operand_type != Type::Bool {
                        return Err(BmbError::TypeError {
                            message: format!("Not operator requires bool, got {}", operand_type),
                        });
                    }
                    Ok(Type::Bool)
                }
            }
        }
        Expr::Var(id) => env
            .get_type(&id.name)
            .cloned()
            .ok_or_else(|| BmbError::TypeError {
                message: format!("Unknown variable: {}", id.name),
            }),
        Expr::IntLit(_) => Ok(Type::I32),
        Expr::FloatLit(_) => Ok(Type::F64),
        Expr::BoolLit(_) => Ok(Type::Bool),
        Expr::Ret => env
            .get_return_type()
            .cloned()
            .ok_or_else(|| BmbError::TypeError {
                message: "'ret' used outside of function context".to_string(),
            }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    #[test]
    fn test_type_env_params() {
        let mut env = TypeEnv::new();
        env.add_param("x", Type::I32);
        assert_eq!(env.get_type("x"), Some(&Type::I32));
    }

    #[test]
    fn test_type_env_registers() {
        let mut env = TypeEnv::new();
        env.add_register("r1", Type::Bool);
        assert_eq!(env.get_type("r1"), Some(&Type::Bool));
    }

    #[test]
    fn test_type_env_return_type() {
        let mut env = TypeEnv::new();
        env.set_return_type(Type::I64);
        assert_eq!(env.get_return_type(), Some(&Type::I64));
    }

    #[test]
    fn test_typecheck_simple_function() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32

  add %r a b
  ret %r
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Type check failed: {:?}", result.err());

        let typed = result.unwrap();
        assert_eq!(typed.nodes.len(), 1);
        // %r should be i32
        assert_eq!(typed.nodes[0].register_types.get("r"), Some(&Type::I32));
    }

    #[test]
    fn test_typecheck_with_contracts() {
        let source = r#"
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0.0
@post ret >= 0.0

  div %r a b
  ret %r
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Type check failed: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_comparison() {
        let source = r#"
@node compare
@params a:i32 b:i32
@returns i32

  lt %cmp a b
  jif %cmp _less
  ret b
_less:
  ret a
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Type check failed: {:?}", result.err());

        let typed = result.unwrap();
        // %cmp should be bool
        assert_eq!(typed.nodes[0].register_types.get("cmp"), Some(&Type::Bool));
    }

    #[test]
    fn test_typecheck_type_mismatch() {
        let source = r#"
@node bad
@params a:i32 b:f64
@returns i32

  add %r a b
  ret %r
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_err(), "Should fail due to type mismatch");

        if let Err(BmbError::TypeError { message }) = result {
            assert!(
                message.contains("same type"),
                "Error should mention type mismatch: {}",
                message
            );
        }
    }

    #[test]
    fn test_typecheck_return_type_mismatch() {
        let source = r#"
@node bad
@params a:i32
@returns f64

  ret a
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_err(), "Should fail due to return type mismatch");

        if let Err(BmbError::TypeError { message }) = result {
            assert!(
                message.contains("Return type mismatch"),
                "Error message: {}",
                message
            );
        }
    }

    #[test]
    fn test_typecheck_factorial() {
        let source = include_str!("../tests/examples/factorial.bmb");
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Type check failed: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_fibonacci() {
        let source = include_str!("../tests/examples/fibonacci.bmb");
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Type check failed: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_gcd() {
        let source = include_str!("../tests/examples/gcd.bmb");
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Type check failed: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_divide() {
        let source = include_str!("../tests/examples/divide.bmb");
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Type check failed: {:?}", result.err());
    }
}
