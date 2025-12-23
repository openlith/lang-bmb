//! BMB Type System
//!
//! Type checking and inference for BMB programs.
//!
//! "Omission is guessing, and guessing is error."
//! - All types must be explicit and verifiable.

use std::collections::HashMap;

use crate::ast::*;
use crate::{BmbError, Result};

/// Registry for user-defined types (structs and enums)
#[derive(Debug, Clone, Default)]
pub struct TypeRegistry {
    /// Struct definitions by name
    pub structs: HashMap<String, StructDef>,
    /// Enum definitions by name
    pub enums: HashMap<String, EnumDef>,
}

impl TypeRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a struct definition
    pub fn add_struct(&mut self, def: StructDef) {
        self.structs.insert(def.name.name.clone(), def);
    }

    /// Register an enum definition
    pub fn add_enum(&mut self, def: EnumDef) {
        self.enums.insert(def.name.name.clone(), def);
    }

    /// Get a struct definition by name
    pub fn get_struct(&self, name: &str) -> Option<&StructDef> {
        self.structs.get(name)
    }

    /// Get an enum definition by name
    pub fn get_enum(&self, name: &str) -> Option<&EnumDef> {
        self.enums.get(name)
    }

    /// Check if a type name is defined (either struct or enum)
    pub fn is_defined(&self, name: &str) -> bool {
        self.structs.contains_key(name) || self.enums.contains_key(name)
    }

    /// Get the type of a struct field
    pub fn get_field_type(&self, struct_name: &str, field_name: &str) -> Option<&Type> {
        self.structs.get(struct_name).and_then(|s| {
            s.fields
                .iter()
                .find(|f| f.name.name == field_name)
                .map(|f| &f.ty)
        })
    }
}

/// Type-checked AST (extends AST with type annotations)
#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub imports: Vec<Import>,
    pub structs: Vec<StructDef>,
    pub enums: Vec<EnumDef>,
    /// Named contract definitions for @requires expansion
    pub contracts: Vec<ContractDef>,
    pub nodes: Vec<TypedNode>,
    pub registry: TypeRegistry,
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
    let mut registry = TypeRegistry::new();

    // Phase 0: Build type registry from struct and enum definitions
    for struct_def in &program.structs {
        if registry.is_defined(&struct_def.name.name) {
            return Err(BmbError::TypeError {
                message: format!("Duplicate type definition: {}", struct_def.name.name),
            });
        }
        registry.add_struct(struct_def.clone());
    }

    for enum_def in &program.enums {
        if registry.is_defined(&enum_def.name.name) {
            return Err(BmbError::TypeError {
                message: format!("Duplicate type definition: {}", enum_def.name.name),
            });
        }
        registry.add_enum(enum_def.clone());
    }

    // Phase 1: Validate struct field types exist
    for struct_def in &program.structs {
        for field in &struct_def.fields {
            validate_type(&field.ty, &registry)?;
        }
    }

    // Phase 2: Validate enum variant types exist
    for enum_def in &program.enums {
        for variant in &enum_def.variants {
            if let Some(ref ty) = variant.payload {
                validate_type(ty, &registry)?;
            }
        }
    }

    // Phase 3: Collect imported function signatures
    // Imported functions have no return type (void), modeled as dummy i32 for now
    for import in &program.imports {
        let sig = FunctionSig {
            params: import.param_types.clone(),
            returns: Type::I32, // Void functions return nothing, but we need a type for now
        };
        global_env.add_function(&import.name.name, sig);
    }

    // Phase 4: Collect local function signatures (validate types first)
    for node in &program.nodes {
        // Validate parameter types
        for param in &node.params {
            validate_type(&param.ty, &registry)?;
        }
        // Validate return type
        validate_type(&node.returns, &registry)?;

        let sig = FunctionSig {
            params: node.params.iter().map(|p| p.ty.clone()).collect(),
            returns: node.returns.clone(),
        };
        global_env.add_function(&node.name.name, sig);
    }

    // Phase 5: Type check each function
    for node in &program.nodes {
        let typed_node = typecheck_node(node, &global_env, &registry)?;
        typed_nodes.push(typed_node);
    }

    Ok(TypedProgram {
        imports: program.imports.clone(),
        structs: program.structs.clone(),
        enums: program.enums.clone(),
        contracts: program.contracts.clone(),
        nodes: typed_nodes,
        registry,
    })
}

/// Perform type checking on a merged program with modules
///
/// This registers all module functions with qualified names before
/// typechecking the main program.
pub fn typecheck_merged(merged: &crate::modules::MergedProgram) -> Result<TypedProgram> {
    let mut typed_nodes = Vec::new();
    let mut global_env = TypeEnv::new();
    let mut registry = TypeRegistry::new();

    // Phase 0: Build type registry from struct and enum definitions
    for struct_def in &merged.main.structs {
        registry.add_struct(struct_def.clone());
    }
    for enum_def in &merged.main.enums {
        registry.add_enum(enum_def.clone());
    }

    // Phase 1: Register module functions with qualified names
    for (module_name, resolved) in &merged.modules {
        for node in &resolved.program.nodes {
            let qualified_name = format!("{}::{}", module_name, node.name.name);
            let sig = FunctionSig {
                params: node.params.iter().map(|p| p.ty.clone()).collect(),
                returns: node.returns.clone(),
            };
            global_env.add_function(&qualified_name, sig);
        }
    }

    // Phase 2: Register main program functions
    for node in &merged.main.nodes {
        let sig = FunctionSig {
            params: node.params.iter().map(|p| p.ty.clone()).collect(),
            returns: node.returns.clone(),
        };
        global_env.add_function(&node.name.name, sig);
    }

    // Phase 3: Type check main program nodes
    for node in &merged.main.nodes {
        let typed_node = typecheck_node(node, &global_env, &registry)?;
        typed_nodes.push(typed_node);
    }

    Ok(TypedProgram {
        imports: merged.main.imports.clone(),
        structs: merged.main.structs.clone(),
        enums: merged.main.enums.clone(),
        contracts: merged.main.contracts.clone(),
        nodes: typed_nodes,
        registry,
    })
}

/// Validate that a type is well-formed (all referenced types exist)
fn validate_type(ty: &Type, registry: &TypeRegistry) -> Result<()> {
    match ty {
        // All primitive types are valid
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
        | Type::Void => Ok(()),
        Type::Array { element, size } => {
            if *size == 0 {
                return Err(BmbError::TypeError {
                    message: "Array size must be greater than 0".to_string(),
                });
            }
            validate_type(element, registry)
        }
        Type::Ref(inner) | Type::Ptr(inner) => validate_type(inner, registry),
        Type::Struct(name) => {
            if registry.get_struct(name).is_some() {
                Ok(())
            } else if registry.get_enum(name).is_some() {
                // User wrote MyEnum but it's parsed as Struct - remap
                Ok(())
            } else {
                Err(BmbError::TypeError {
                    message: format!("Unknown type: {}", name),
                })
            }
        }
        Type::Enum(name) => {
            if registry.get_enum(name).is_some() {
                Ok(())
            } else {
                Err(BmbError::TypeError {
                    message: format!("Unknown enum type: {}", name),
                })
            }
        }
        Type::Refined { name, .. } => {
            // TODO: Validate refined type exists in registry when type registry supports it
            // For now, accept all refined types (will be validated in Phase 2)
            if name.is_empty() {
                Err(BmbError::TypeError {
                    message: "Refined type name cannot be empty".to_string(),
                })
            } else {
                Ok(())
            }
        }
    }
}

fn typecheck_node(node: &Node, global_env: &TypeEnv, registry: &TypeRegistry) -> Result<TypedNode> {
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
                typecheck_statement(stmt, &mut env, &node.returns, registry)?;
            }
        }
    }

    // Type check contracts (multiple preconditions and postconditions allowed)
    for pre in &node.preconditions {
        let pre_type = typecheck_expr(pre, &env)?;
        if pre_type != Type::Bool {
            return Err(BmbError::TypeError {
                message: format!("Precondition must be bool, got {}", pre_type),
            });
        }
    }

    for post in &node.postconditions {
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

fn typecheck_statement(
    stmt: &Statement,
    env: &mut TypeEnv,
    return_type: &Type,
    registry: &TypeRegistry,
) -> Result<()> {
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

            let (type_a, type_b) =
                get_operand_types(&stmt.operands[1], &stmt.operands[2], env, registry)?;

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

        Opcode::And | Opcode::Or | Opcode::Xor | Opcode::Shl | Opcode::Shr => {
            // Bitwise binary: %dest = op %a %b
            // Operands must be same integer type, result is same type
            if stmt.operands.len() != 3 {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} requires 3 operands, got {}",
                        stmt.opcode,
                        stmt.operands.len()
                    ),
                });
            }

            let (type_a, type_b) =
                get_operand_types(&stmt.operands[1], &stmt.operands[2], env, registry)?;

            if type_a != type_b {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} operands must have same type: {} vs {}",
                        stmt.opcode, type_a, type_b
                    ),
                });
            }

            // Bitwise operations only work on integer types
            if !type_a.is_integer() && type_a != Type::Bool {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} requires integer operands, got {}",
                        stmt.opcode, type_a
                    ),
                });
            }

            // Set result register type (same as operands)
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, type_a);
            }
        }

        Opcode::Not => {
            // Bitwise NOT: %dest = not %a
            // Unary operation, result is same integer type
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!(
                        "not requires 2 operands, got {}",
                        stmt.operands.len()
                    ),
                });
            }

            let operand_type = get_operand_type(&stmt.operands[1], env, registry)?;

            // Bitwise NOT only works on integer types
            if !operand_type.is_integer() && operand_type != Type::Bool {
                return Err(BmbError::TypeError {
                    message: format!(
                        "not requires integer operand, got {}",
                        operand_type
                    ),
                });
            }

            // Set result register type (same as operand)
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, operand_type);
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

            let (type_a, type_b) =
                get_operand_types(&stmt.operands[1], &stmt.operands[2], env, registry)?;

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

            let ret_type = get_operand_type(&stmt.operands[0], env, registry)?;
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

            let cond_type = get_operand_type(&stmt.operands[0], env, registry)?;
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

            // Get function name (simple or qualified)
            let func_name = match &stmt.operands[1] {
                Operand::Identifier(func) => func.name.clone(),
                Operand::QualifiedIdent { module, name } => {
                    format!("{}::{}", module.name, name.name)
                }
                _ => {
                    return Err(BmbError::TypeError {
                        message: "call requires function name".to_string(),
                    });
                }
            };

            if let Some(sig) = env.get_function(&func_name) {
                // Set result register type
                if let Operand::Register(ref r) = stmt.operands[0] {
                    env.add_register(&r.name, sig.returns.clone());
                }
            } else {
                return Err(BmbError::TypeError {
                    message: format!("Unknown function: {}", func_name),
                });
            }
        }

        Opcode::Xcall => {
            // External call to void function: xcall func %args...
            if stmt.operands.is_empty() {
                return Err(BmbError::TypeError {
                    message: "xcall requires at least 1 operand (function name)".to_string(),
                });
            }

            // First operand is function name
            if let Operand::Identifier(ref func) = stmt.operands[0] {
                if env.get_function(&func.name).is_none() {
                    return Err(BmbError::TypeError {
                        message: format!("Unknown function: {}", func.name),
                    });
                }
            }
            // No result register - void function
        }

        Opcode::Mov => {
            // Move: mov %dest %src or mov %dest literal
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!("mov requires 2 operands, got {}", stmt.operands.len()),
                });
            }

            let src_type = get_operand_type(&stmt.operands[1], env, registry)?;
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, src_type);
            }
        }

        Opcode::Load | Opcode::Store => {
            // Memory operations (future expansion)
        }

        Opcode::Print => {
            // Print: print "string literal"
            if stmt.operands.len() != 1 {
                return Err(BmbError::TypeError {
                    message: format!("print requires 1 operand, got {}", stmt.operands.len()),
                });
            }

            // Verify it's a string literal
            if !matches!(stmt.operands[0], Operand::StringLiteral(_)) {
                return Err(BmbError::TypeError {
                    message: "print requires a string literal operand".to_string(),
                });
            }
        }
    }

    Ok(())
}

fn get_operand_type(operand: &Operand, env: &TypeEnv, registry: &TypeRegistry) -> Result<Type> {
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
        Operand::StringLiteral(_) => Err(BmbError::TypeError {
            message: "String literal cannot be used as value (only with print)".to_string(),
        }),
        Operand::FieldAccess { base, field } => {
            // Get base type and look up field type in registry
            let base_type = env.get_type(&base.name).ok_or_else(|| BmbError::TypeError {
                message: format!("Unknown variable: {}", base.name),
            })?;
            match base_type {
                Type::Struct(struct_name) => {
                    registry
                        .get_field_type(struct_name, &field.name)
                        .cloned()
                        .ok_or_else(|| BmbError::TypeError {
                            message: format!(
                                "Unknown field '{}' in struct '{}'",
                                field.name, struct_name
                            ),
                        })
                }
                _ => Err(BmbError::TypeError {
                    message: format!(
                        "Cannot access field '{}' on non-struct type: {}",
                        field.name, base_type
                    ),
                }),
            }
        }
        Operand::ArrayAccess { base, index } => {
            // Get base type and extract element type
            let base_type = env.get_type(&base.name).ok_or_else(|| BmbError::TypeError {
                message: format!("Unknown variable: {}", base.name),
            })?;

            // Validate index type is integer
            let index_type = get_operand_type(index, env, registry)?;
            match index_type {
                Type::I32 | Type::I64 => {}
                _ => {
                    return Err(BmbError::TypeError {
                        message: format!("Array index must be integer, got {}", index_type),
                    })
                }
            }

            match base_type {
                Type::Array { element, .. } => Ok(*element.clone()),
                _ => Err(BmbError::TypeError {
                    message: format!("Cannot index non-array type: {}", base_type),
                }),
            }
        }
        Operand::QualifiedIdent { module, name } => {
            // Qualified identifier: module::function
            // Look up the qualified function name in the environment
            let qualified_name = format!("{}::{}", module.name, name.name);
            if let Some(sig) = env.get_function(&qualified_name) {
                // Return the function's return type
                Ok(sig.returns.clone())
            } else {
                Err(BmbError::TypeError {
                    message: format!(
                        "Unknown function in module: {}::{}",
                        module.name, name.name
                    ),
                })
            }
        }
    }
}

fn get_operand_types(
    a: &Operand,
    b: &Operand,
    env: &TypeEnv,
    registry: &TypeRegistry,
) -> Result<(Type, Type)> {
    Ok((
        get_operand_type(a, env, registry)?,
        get_operand_type(b, env, registry)?,
    ))
}

/// Determine the common type for comparison, with literal promotion
/// Returns Some(unified_type) if types are compatible, None otherwise
fn unified_comparison_type(left: &Type, right: &Type) -> Option<Type> {
    if left == right {
        return Some(left.clone());
    }

    // Signed integer promotion: smaller → larger
    // i8 → i16 → i32 → i64
    if left.is_signed_integer() && right.is_signed_integer() {
        return Some(match (left, right) {
            (Type::I8, t) | (t, Type::I8) if *t != Type::I8 => t.clone(),
            (Type::I16, t) | (t, Type::I16) if *t != Type::I8 && *t != Type::I16 => t.clone(),
            (Type::I32, Type::I64) | (Type::I64, Type::I32) => Type::I64,
            _ => return None,
        });
    }

    // Unsigned integer promotion: smaller → larger
    // u8 → u16 → u32 → u64
    if left.is_unsigned_integer() && right.is_unsigned_integer() {
        return Some(match (left, right) {
            (Type::U8, t) | (t, Type::U8) if *t != Type::U8 => t.clone(),
            (Type::U16, t) | (t, Type::U16) if *t != Type::U8 && *t != Type::U16 => t.clone(),
            (Type::U32, Type::U64) | (Type::U64, Type::U32) => Type::U64,
            _ => return None,
        });
    }

    // Float promotion: f32 → f64
    if left.is_float() && right.is_float() {
        return Some(Type::F64);
    }

    None
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
        // old(expr) has the same type as the inner expression
        // Used in postconditions to reference pre-state values
        Expr::Old(inner) => typecheck_expr(inner, env),
        // SelfRef is only valid in refined type constraint contexts
        // Its type depends on the base type being refined
        Expr::SelfRef => {
            // In normal expression context, SelfRef is an error
            // It should only appear in type constraints
            Err(BmbError::TypeError {
                message: "'self' keyword is only valid in refined type constraints".to_string(),
            })
        }
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

    #[test]
    fn test_typecheck_struct_definition() {
        let source = r#"
@struct Point
  x:i32
  y:i32

@node distance
@params p:Point
@returns i32
  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Struct typecheck failed: {:?}", result.err());

        let typed = result.unwrap();
        assert_eq!(typed.structs.len(), 1);
        assert!(typed.registry.get_struct("Point").is_some());
    }

    #[test]
    fn test_typecheck_unknown_type_error() {
        let source = r#"
@node bad
@params x:UnknownType
@returns i32
  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_err(), "Should fail for unknown type");

        if let Err(BmbError::TypeError { message }) = result {
            assert!(
                message.contains("Unknown type"),
                "Should mention unknown type: {}",
                message
            );
        }
    }

    #[test]
    fn test_typecheck_enum_definition() {
        let source = r#"
@enum Color
  Red
  Green
  Blue

@node get_color
@params
@returns i32
  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Enum typecheck failed: {:?}", result.err());

        let typed = result.unwrap();
        assert_eq!(typed.enums.len(), 1);
        assert!(typed.registry.get_enum("Color").is_some());
    }

    #[test]
    fn test_typecheck_array_type() {
        let source = r#"
@node process_array
@params arr:[i32; 10]
@returns i32
  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Array typecheck failed: {:?}", result.err());
    }

    #[test]
    fn test_type_registry_field_lookup() {
        let mut registry = TypeRegistry::new();
        registry.add_struct(StructDef {
            name: Identifier {
                name: "Point".to_string(),
                span: Span::default(),
            },
            fields: vec![
                StructField {
                    name: Identifier {
                        name: "x".to_string(),
                        span: Span::default(),
                    },
                    ty: Type::I32,
                    span: Span::default(),
                },
                StructField {
                    name: Identifier {
                        name: "y".to_string(),
                        span: Span::default(),
                    },
                    ty: Type::F64,
                    span: Span::default(),
                },
            ],
            span: Span::default(),
        });

        assert_eq!(registry.get_field_type("Point", "x"), Some(&Type::I32));
        assert_eq!(registry.get_field_type("Point", "y"), Some(&Type::F64));
        assert_eq!(registry.get_field_type("Point", "z"), None);
    }

    #[test]
    fn test_typecheck_u8_function() {
        let source = r#"
@node byte_add
@params a:u8 b:u8
@returns u8

  add %r a b
  ret %r
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "u8 params should typecheck: {:?}", result.err());
        let typed = result.unwrap();
        assert_eq!(typed.nodes[0].node.returns, Type::U8);
    }

    #[test]
    fn test_typecheck_char_function() {
        let source = r#"
@node identity_char
@params c:char
@returns char

  ret c
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "char type should typecheck: {:?}", result.err());
        let typed = result.unwrap();
        assert_eq!(typed.nodes[0].node.returns, Type::Char);
    }

    #[test]
    fn test_typecheck_ptr_function() {
        let source = r#"
@node ptr_passthrough
@params ptr:*i32
@returns *i32

  ret ptr
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "pointer type should typecheck: {:?}", result.err());
        let typed = result.unwrap();
        match &typed.nodes[0].node.returns {
            Type::Ptr(inner) => assert_eq!(**inner, Type::I32),
            other => panic!("Expected pointer type, got {:?}", other),
        }
    }

    #[test]
    fn test_unified_comparison_type() {
        // Same types return themselves
        assert_eq!(unified_comparison_type(&Type::I32, &Type::I32), Some(Type::I32));
        assert_eq!(unified_comparison_type(&Type::U64, &Type::U64), Some(Type::U64));

        // Signed integer promotion
        assert_eq!(unified_comparison_type(&Type::I8, &Type::I32), Some(Type::I32));
        assert_eq!(unified_comparison_type(&Type::I16, &Type::I64), Some(Type::I64));
        assert_eq!(unified_comparison_type(&Type::I32, &Type::I64), Some(Type::I64));

        // Unsigned integer promotion
        assert_eq!(unified_comparison_type(&Type::U8, &Type::U32), Some(Type::U32));
        assert_eq!(unified_comparison_type(&Type::U16, &Type::U64), Some(Type::U64));
        assert_eq!(unified_comparison_type(&Type::U32, &Type::U64), Some(Type::U64));

        // Float promotion
        assert_eq!(unified_comparison_type(&Type::F32, &Type::F64), Some(Type::F64));

        // Mixed signed/unsigned: no promotion
        assert_eq!(unified_comparison_type(&Type::I32, &Type::U32), None);

        // Incompatible types
        assert_eq!(unified_comparison_type(&Type::I32, &Type::F64), None);
        assert_eq!(unified_comparison_type(&Type::Bool, &Type::I32), None);
    }
}
