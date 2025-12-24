//! BMB Type System
//!
//! Type checking and inference for BMB programs.
//!
//! "Omission is guessing, and guessing is error."
//! - All types must be explicit and verifiable.

use std::collections::HashMap;

use crate::ast::*;
use crate::exhaustiveness::{check_exhaustiveness, format_missing_patterns};
use crate::{BmbError, Result};

/// Registry for user-defined types (structs, enums, and refined types)
#[derive(Debug, Clone, Default)]
pub struct TypeRegistry {
    /// Struct definitions by name
    pub structs: HashMap<String, StructDef>,
    /// Enum definitions by name
    pub enums: HashMap<String, EnumDef>,
    /// Refined type definitions by name
    pub refined_types: HashMap<String, TypeDef>,
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

    /// Check if a struct with this name is registered
    pub fn has_struct(&self, name: &str) -> bool {
        self.structs.contains_key(name)
    }

    /// Get an enum definition by name
    pub fn get_enum(&self, name: &str) -> Option<&EnumDef> {
        self.enums.get(name)
    }

    /// Check if an enum with this name is registered
    pub fn has_enum(&self, name: &str) -> bool {
        self.enums.contains_key(name)
    }

    /// Check if a type name is defined (struct, enum, or refined type)
    pub fn is_defined(&self, name: &str) -> bool {
        self.structs.contains_key(name)
            || self.enums.contains_key(name)
            || self.refined_types.contains_key(name)
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

    /// Register a refined type definition
    pub fn add_refined_type(&mut self, def: TypeDef) {
        self.refined_types.insert(def.name.name.clone(), def);
    }

    /// Get a refined type definition by name
    pub fn get_refined_type(&self, name: &str) -> Option<&TypeDef> {
        self.refined_types.get(name)
    }

    /// Check if a refined type with this name is registered
    pub fn has_refined_type(&self, name: &str) -> bool {
        self.refined_types.contains_key(name)
    }

    /// Resolve a refined type to its base type
    /// Returns the base type if the name refers to a refined type, None otherwise
    pub fn resolve_to_base_type(&self, name: &str) -> Option<&Type> {
        self.refined_types.get(name).map(|def| &def.base_type)
    }

    /// Get the constraint expression for a refined type
    /// Returns the constraint expression if the name refers to a refined type, None otherwise
    pub fn get_refined_constraint(&self, name: &str) -> Option<&Expr> {
        self.refined_types.get(name).map(|def| &def.constraint)
    }

    /// Resolve a type to its canonical form
    /// - For refined types (like nz_i32), returns the base type (i32)
    /// - For Type::Struct that names a refined type, returns the base type
    /// - For Type::Struct that names an enum, returns Type::Enum
    /// - For all other types, returns the type as-is
    pub fn resolve_type_to_base(&self, ty: &Type) -> Type {
        match ty {
            Type::Struct(name) => {
                // Check if this is a refined type name
                if let Some(base) = self.resolve_to_base_type(name) {
                    base.clone()
                } else if self.enums.contains_key(name) {
                    // This is actually an enum, not a struct
                    // Parser uses Type::Struct for all user-defined types
                    Type::Enum(name.clone())
                } else {
                    ty.clone()
                }
            }
            Type::Refined { name, .. } => {
                // Look up the refined type definition and return its base type
                if let Some(base) = self.resolve_to_base_type(name) {
                    base.clone()
                } else {
                    ty.clone()
                }
            }
            // All other types pass through unchanged
            _ => ty.clone(),
        }
    }

    /// Check if two types are compatible (same base type after resolving refined types)
    pub fn types_compatible(&self, a: &Type, b: &Type) -> bool {
        let base_a = self.resolve_type_to_base(a);
        let base_b = self.resolve_type_to_base(b);
        base_a == base_b
    }
}

/// Type-checked AST (extends AST with type annotations)
#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub imports: Vec<Import>,
    /// External function declarations (v0.12+)
    pub extern_defs: Vec<ExternDef>,
    pub structs: Vec<StructDef>,
    pub enums: Vec<EnumDef>,
    /// Refined type definitions
    pub type_defs: Vec<TypeDef>,
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
    /// Linear type usage tracking (v0.10+): @consume params must be used exactly once
    linear_params: HashMap<String, usize>,
    /// Device params tracking (v0.10+): @device params for MMIO
    device_params: std::collections::HashSet<String>,
}

/// Function signature for type checking calls
#[derive(Debug, Clone)]
pub struct FunctionSig {
    pub params: Vec<Type>,
    pub returns: Type,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            params: HashMap::new(),
            registers: HashMap::new(),
            functions: HashMap::new(),
            return_type: None,
            linear_params: HashMap::new(),
            device_params: std::collections::HashSet::new(),
        }
    }

    pub fn add_param(&mut self, name: &str, ty: Type) {
        self.params.insert(name.to_string(), ty);
    }

    /// Add a linear parameter (v0.10+): must be used exactly once
    pub fn add_linear_param(&mut self, name: &str, ty: Type) {
        self.params.insert(name.to_string(), ty);
        self.linear_params.insert(name.to_string(), 0);
    }

    /// Add a device parameter (v0.10+): MMIO pointer with volatile semantics
    pub fn add_device_param(&mut self, name: &str, ty: Type) {
        self.params.insert(name.to_string(), ty);
        self.device_params.insert(name.to_string());
    }

    /// Record usage of a parameter (for linear type checking)
    pub fn use_param(&mut self, name: &str) {
        if let Some(count) = self.linear_params.get_mut(name) {
            *count += 1;
        }
    }

    /// Verify all linear params were used exactly once
    /// Returns Some((param_name, use_count)) if a param wasn't used exactly once
    pub fn verify_linear_usage(&self) -> Option<(String, usize)> {
        for (name, count) in &self.linear_params {
            if *count != 1 {
                return Some((name.clone(), *count));
            }
        }
        None
    }

    /// Check if a param is a device parameter
    #[allow(dead_code)]
    pub fn is_device_param(&self, name: &str) -> bool {
        self.device_params.contains(name)
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

    // Phase 0b: Register refined type definitions
    for type_def in &program.type_defs {
        if registry.is_defined(&type_def.name.name) {
            return Err(BmbError::TypeError {
                message: format!("Duplicate type definition: {}", type_def.name.name),
            });
        }
        registry.add_refined_type(type_def.clone());
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

    // Phase 2b: Validate refined type base types exist and constraints are valid
    for type_def in &program.type_defs {
        validate_type(&type_def.base_type, &registry)?;
        // Validate the constraint expression is well-formed
        // Note: The constraint can reference 'self' which refers to the value being constrained
        validate_refined_constraint(&type_def.constraint, &type_def.base_type)?;
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

    // Phase 3b: Collect extern function signatures (v0.12+)
    // Extern functions have explicit calling conventions and full type information
    for extern_def in &program.extern_defs {
        // Validate parameter types
        for param in &extern_def.params {
            validate_type(&param.ty, &registry)?;
        }
        // Validate return type
        validate_type(&extern_def.returns, &registry)?;

        let sig = FunctionSig {
            params: extern_def.params.iter().map(|p| p.ty.clone()).collect(),
            returns: extern_def.returns.clone(),
        };
        global_env.add_function(&extern_def.name.name, sig);
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
        extern_defs: program.extern_defs.clone(),
        structs: program.structs.clone(),
        enums: program.enums.clone(),
        type_defs: program.type_defs.clone(),
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

    // Phase 0: Build type registry from struct, enum, and refined type definitions
    for struct_def in &merged.main.structs {
        registry.add_struct(struct_def.clone());
    }
    for enum_def in &merged.main.enums {
        registry.add_enum(enum_def.clone());
    }
    for type_def in &merged.main.type_defs {
        registry.add_refined_type(type_def.clone());
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

    // Phase 1b: Register extern function signatures (v0.12+)
    for extern_def in &merged.main.extern_defs {
        // Validate parameter types
        for param in &extern_def.params {
            validate_type(&param.ty, &registry)?;
        }
        // Validate return type
        validate_type(&extern_def.returns, &registry)?;

        let sig = FunctionSig {
            params: extern_def.params.iter().map(|p| p.ty.clone()).collect(),
            returns: extern_def.returns.clone(),
        };
        global_env.add_function(&extern_def.name.name, sig);
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
        extern_defs: merged.main.extern_defs.clone(),
        structs: merged.main.structs.clone(),
        enums: merged.main.enums.clone(),
        type_defs: merged.main.type_defs.clone(),
        contracts: merged.main.contracts.clone(),
        nodes: typed_nodes,
        registry,
    })
}

/// Perform full type checking on a merged program, including all module nodes
///
/// Unlike `typecheck_merged`, this includes typed nodes from all modules
/// with qualified names (module::function), producing a single TypedProgram
/// suitable for multi-file WASM compilation.
pub fn typecheck_merged_full(merged: &crate::modules::MergedProgram) -> Result<TypedProgram> {
    let mut typed_nodes = Vec::new();
    let mut global_env = TypeEnv::new();
    let mut registry = TypeRegistry::new();

    // Collect all imports and extern defs
    let all_imports = merged.main.imports.clone();
    let mut all_extern_defs = merged.main.extern_defs.clone();
    let mut all_structs = merged.main.structs.clone();
    let mut all_enums = merged.main.enums.clone();
    let mut all_type_defs = merged.main.type_defs.clone();
    let all_contracts = merged.main.contracts.clone();

    // Phase 0a: Build type registry from main program definitions
    for struct_def in &merged.main.structs {
        registry.add_struct(struct_def.clone());
    }
    for enum_def in &merged.main.enums {
        registry.add_enum(enum_def.clone());
    }
    for type_def in &merged.main.type_defs {
        registry.add_refined_type(type_def.clone());
    }

    // Phase 0b: Build type registry from module definitions
    for (_module_name, resolved) in &merged.modules {
        for struct_def in &resolved.program.structs {
            if !registry.has_struct(&struct_def.name.name) {
                registry.add_struct(struct_def.clone());
                all_structs.push(struct_def.clone());
            }
        }
        for enum_def in &resolved.program.enums {
            if !registry.has_enum(&enum_def.name.name) {
                registry.add_enum(enum_def.clone());
                all_enums.push(enum_def.clone());
            }
        }
        for type_def in &resolved.program.type_defs {
            if !registry.has_refined_type(&type_def.name.name) {
                registry.add_refined_type(type_def.clone());
                all_type_defs.push(type_def.clone());
            }
        }
        // Collect extern defs from modules
        for extern_def in &resolved.program.extern_defs {
            all_extern_defs.push(extern_def.clone());
        }
    }

    // Phase 1a: Register module functions with qualified names
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

    // Phase 1b: Register extern function signatures
    for extern_def in &all_extern_defs {
        for param in &extern_def.params {
            validate_type(&param.ty, &registry)?;
        }
        validate_type(&extern_def.returns, &registry)?;

        let sig = FunctionSig {
            params: extern_def.params.iter().map(|p| p.ty.clone()).collect(),
            returns: extern_def.returns.clone(),
        };
        global_env.add_function(&extern_def.name.name, sig);
    }

    // Phase 2: Register main program functions
    for node in &merged.main.nodes {
        let sig = FunctionSig {
            params: node.params.iter().map(|p| p.ty.clone()).collect(),
            returns: node.returns.clone(),
        };
        global_env.add_function(&node.name.name, sig);
    }

    // Phase 3a: Type check module nodes (with qualified names)
    for (module_name, resolved) in &merged.modules {
        for node in &resolved.program.nodes {
            // Create a copy of the node with qualified name
            let mut qualified_node = node.clone();
            qualified_node.name = crate::ast::Identifier {
                name: format!("{}::{}", module_name, node.name.name),
                span: node.name.span,
            };

            let typed_node = typecheck_node(&qualified_node, &global_env, &registry)?;
            typed_nodes.push(typed_node);
        }
    }

    // Phase 3b: Type check main program nodes
    for node in &merged.main.nodes {
        let typed_node = typecheck_node(node, &global_env, &registry)?;
        typed_nodes.push(typed_node);
    }

    Ok(TypedProgram {
        imports: all_imports,
        extern_defs: all_extern_defs,
        structs: all_structs,
        enums: all_enums,
        type_defs: all_type_defs,
        contracts: all_contracts,
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
        | Type::Void
        // String types (v0.9+) - UTF-8 validity guaranteed at type level
        | Type::BmbString
        | Type::BmbStr => Ok(()),
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
            } else if registry.get_refined_type(name).is_some() {
                // User wrote a refined type name (e.g., nz_i32) - valid
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
            // Validate refined type exists in registry
            if name.is_empty() {
                Err(BmbError::TypeError {
                    message: "Refined type name cannot be empty".to_string(),
                })
            } else if registry.get_refined_type(name).is_some() {
                Ok(())
            } else {
                // It might be a parameterized refined type usage - check if base name exists
                // For now, just accept it since parsing validated the syntax
                Ok(())
            }
        }
        // Generic built-in types
        Type::Option(inner) => validate_type(inner, registry),
        Type::Result { ok, err } => {
            validate_type(ok, registry)?;
            validate_type(err, registry)
        }
        Type::Vector(inner) | Type::Slice(inner) => validate_type(inner, registry),
        // Box<T> for heap-allocated recursive types
        Type::BmbBox(inner) => validate_type(inner, registry),
    }
}

/// Validate that a refined type constraint expression is well-formed
///
/// The constraint can use 'self' to refer to the value being constrained,
/// as well as literals and basic operators.
fn validate_refined_constraint(constraint: &Expr, _base_type: &Type) -> Result<()> {
    // For now, perform basic validation that the constraint is a valid boolean expression
    // In the future, we could verify that 'self' is used appropriately for the base type
    validate_constraint_expr(constraint)
}

/// Recursively validate a constraint expression
fn validate_constraint_expr(expr: &Expr) -> Result<()> {
    match expr {
        Expr::IntLit(_) | Expr::FloatLit(_) | Expr::BoolLit(_) | Expr::SelfRef => Ok(()),
        Expr::Var(_) => {
            // Variables in constraints should only be 'self' (Expr::SelfRef)
            // but we allow parameter names in parameterized refined types
            Ok(())
        }
        Expr::Ret => Err(BmbError::TypeError {
            message: "'ret' cannot be used in refined type constraints".to_string(),
        }),
        Expr::Old(_) => Err(BmbError::TypeError {
            message: "'old()' cannot be used in refined type constraints".to_string(),
        }),
        Expr::Binary { left, right, .. } => {
            validate_constraint_expr(left)?;
            validate_constraint_expr(right)
        }
        Expr::Unary { operand, .. } => validate_constraint_expr(operand),
    }
}

fn typecheck_node(node: &Node, global_env: &TypeEnv, registry: &TypeRegistry) -> Result<TypedNode> {
    let mut env = TypeEnv::new();

    // Copy function signatures
    for (name, sig) in &global_env.functions {
        env.add_function(name, sig.clone());
    }

    // Add parameters to environment based on their annotation (v0.10+)
    for param in &node.params {
        match param.annotation {
            ParamAnnotation::Consume => {
                // Linear type: must be used exactly once
                env.add_linear_param(&param.name.name, param.ty.clone());
            }
            ParamAnnotation::Device => {
                // Device pointer: MMIO semantics
                env.add_device_param(&param.name.name, param.ty.clone());
            }
            ParamAnnotation::None => {
                // Regular parameter
                env.add_param(&param.name.name, param.ty.clone());
            }
        }
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
            Instruction::Match(match_stmt) => {
                // Get scrutinee type
                let scrutinee_type = env.get_type(&match_stmt.scrutinee)
                    .ok_or_else(|| BmbError::TypeError {
                        message: format!("Unknown register in @match: %{}", match_stmt.scrutinee),
                    })?
                    .clone();

                // Type check each arm
                for arm in &match_stmt.arms {
                    // Validate pattern against scrutinee type
                    typecheck_pattern(&arm.pattern, &scrutinee_type, &mut env, registry)?;

                    // Type check arm body
                    for instr in &arm.body {
                        if let Instruction::Statement(stmt) = instr {
                            typecheck_statement(stmt, &mut env, &node.returns, registry)?;
                        }
                    }

                    // Note: We keep bindings in register_types rather than removing them
                    // because codegen needs locals allocated for all bindings.
                    // Scoping is enforced by the pattern structure, not by removal.
                }

                // Type check default arm if present
                if let Some(default) = &match_stmt.default {
                    for instr in &default.body {
                        if let Instruction::Statement(stmt) = instr {
                            typecheck_statement(stmt, &mut env, &node.returns, registry)?;
                        }
                    }
                }

                // Exhaustiveness check (v0.15+)
                // "Omission is guessing, and guessing is error."
                let exhaustiveness_result =
                    check_exhaustiveness(match_stmt, &scrutinee_type, registry)?;

                if !exhaustiveness_result.is_exhaustive {
                    return Err(BmbError::TypeError {
                        message: format!(
                            "Non-exhaustive pattern match on %{}: {}",
                            match_stmt.scrutinee,
                            format_missing_patterns(&exhaustiveness_result.missing_patterns)
                        ),
                    });
                }

                // Warn about unreachable patterns (currently as error for strictness)
                if !exhaustiveness_result.unreachable_patterns.is_empty() {
                    // For now, unreachable patterns are warnings, not errors
                    // In the future, this could be configurable
                    // eprintln!("Warning: {}", format_unreachable_patterns(&exhaustiveness_result.unreachable_patterns));
                }
            }
        }
    }

    // Verify linear type usage (v0.10+): @consume params must be used exactly once
    if let Some((param_name, use_count)) = env.verify_linear_usage() {
        return Err(BmbError::TypeError {
            message: if use_count == 0 {
                format!(
                    "Linear type error: @consume parameter '{}' was never used (must be used exactly once)",
                    param_name
                )
            } else {
                format!(
                    "Linear type error: @consume parameter '{}' was used {} times (must be used exactly once)",
                    param_name, use_count
                )
            },
        });
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

/// Track usage of operands for linear type checking (v0.10+)
/// This must be called for each operand that accesses a parameter
fn track_operand_usage(operand: &Operand, env: &mut TypeEnv) {
    match operand {
        Operand::Register(r) => {
            // Registers starting with % that match parameter names
            env.use_param(&r.name);
        }
        Operand::Identifier(id) => {
            env.use_param(&id.name);
        }
        _ => {}
    }
}

/// Track usage of all operands in a statement for linear type checking
fn track_statement_usage(stmt: &Statement, env: &mut TypeEnv) {
    for operand in &stmt.operands {
        track_operand_usage(operand, env);
    }
}

/// Type check a pattern in a match arm
fn typecheck_pattern(
    pattern: &Pattern,
    scrutinee_type: &Type,
    env: &mut TypeEnv,
    registry: &TypeRegistry,
) -> Result<()> {
    match pattern {
        Pattern::Variant {
            enum_name,
            variant_name,
            binding,
            ..
        } => {
            // Verify scrutinee is an enum type
            let enum_type_name = match scrutinee_type {
                Type::Enum(name) | Type::Struct(name) => name,
                _ => {
                    return Err(BmbError::TypeError {
                        message: format!(
                            "Cannot match variant pattern against non-enum type {}",
                            scrutinee_type
                        ),
                    });
                }
            };

            // Verify enum name matches
            if enum_type_name != &enum_name.name {
                return Err(BmbError::TypeError {
                    message: format!(
                        "Pattern enum {} doesn't match scrutinee type {}",
                        enum_name.name, enum_type_name
                    ),
                });
            }

            // Look up the enum definition
            if let Some(enum_def) = registry.get_enum(&enum_name.name) {
                // Find the variant
                let variant = enum_def.variants.iter().find(|v| v.name.name == variant_name.name);
                if let Some(v) = variant {
                    // If there's a binding, add it to the environment with the variant's payload type
                    if let Some(bind_name) = binding {
                        if let Some(ref payload_type) = v.payload {
                            env.add_register(bind_name, payload_type.clone());
                        } else {
                            return Err(BmbError::TypeError {
                                message: format!(
                                    "Variant {}::{} has no payload but binding was provided",
                                    enum_name.name, variant_name.name
                                ),
                            });
                        }
                    }
                } else {
                    return Err(BmbError::TypeError {
                        message: format!(
                            "Unknown variant {}::{}",
                            enum_name.name, variant_name.name
                        ),
                    });
                }
            } else {
                return Err(BmbError::TypeError {
                    message: format!("Unknown enum type: {}", enum_name.name),
                });
            }
        }
        Pattern::Literal { value, .. } => {
            // Verify literal type matches scrutinee type
            let literal_type = match value {
                LiteralValue::Int(_) => {
                    // Integer literals can match i32, i64, u32, etc.
                    // For now, accept if scrutinee is any integer type
                    if !matches!(
                        scrutinee_type,
                        Type::I8
                            | Type::I16
                            | Type::I32
                            | Type::I64
                            | Type::U8
                            | Type::U16
                            | Type::U32
                            | Type::U64
                    ) {
                        return Err(BmbError::TypeError {
                            message: format!(
                                "Integer pattern cannot match type {}",
                                scrutinee_type
                            ),
                        });
                    }
                    scrutinee_type.clone()
                }
                LiteralValue::Bool(_) => {
                    if *scrutinee_type != Type::Bool {
                        return Err(BmbError::TypeError {
                            message: format!(
                                "Bool pattern cannot match type {}",
                                scrutinee_type
                            ),
                        });
                    }
                    Type::Bool
                }
                LiteralValue::Char(_) => {
                    if *scrutinee_type != Type::Char {
                        return Err(BmbError::TypeError {
                            message: format!(
                                "Char pattern cannot match type {}",
                                scrutinee_type
                            ),
                        });
                    }
                    Type::Char
                }
            };
            // Pattern type matches - no action needed
            let _ = literal_type;
        }
    }
    Ok(())
}

fn typecheck_statement(
    stmt: &Statement,
    env: &mut TypeEnv,
    return_type: &Type,
    registry: &TypeRegistry,
) -> Result<()> {
    // Track linear type usage (v0.10+): @consume params
    track_statement_usage(stmt, env);

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

            // Resolve refined types to base types for comparison
            if !registry.types_compatible(&type_a, &type_b) {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} operands must have same type: {} vs {}",
                        stmt.opcode, type_a, type_b
                    ),
                });
            }

            // Set result register type (use resolved base type)
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, registry.resolve_type_to_base(&type_a));
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

            // Resolve refined types to base types for comparison
            if !registry.types_compatible(&type_a, &type_b) {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} operands must have same type: {} vs {}",
                        stmt.opcode, type_a, type_b
                    ),
                });
            }

            // Bitwise operations only work on integer types (use resolved base type)
            let base_type = registry.resolve_type_to_base(&type_a);
            if !base_type.is_integer() && base_type != Type::Bool {
                return Err(BmbError::TypeError {
                    message: format!(
                        "{} requires integer operands, got {}",
                        stmt.opcode, type_a
                    ),
                });
            }

            // Set result register type (use resolved base type)
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, base_type);
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

            if !registry.types_compatible(&type_a, &type_b) {
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
            if !registry.types_compatible(&ret_type, return_type) {
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
            // External call: supports both void and non-void returns
            // Syntax 1 (void): xcall func_name %args...
            // Syntax 2 (non-void): xcall %dest func_name %args...
            if stmt.operands.is_empty() {
                return Err(BmbError::TypeError {
                    message: "xcall requires at least 1 operand (function name)".to_string(),
                });
            }

            // Check if first operand is register (non-void) or identifier (void)
            match &stmt.operands[0] {
                Operand::Register(ref dest_reg) => {
                    // Non-void xcall: xcall %dest func_name %args...
                    if stmt.operands.len() < 2 {
                        return Err(BmbError::TypeError {
                            message: "xcall with destination requires function name".to_string(),
                        });
                    }
                    let func_name = match &stmt.operands[1] {
                        Operand::Identifier(func) => func.name.clone(),
                        Operand::QualifiedIdent { module, name } => {
                            format!("{}::{}", module.name, name.name)
                        }
                        _ => {
                            return Err(BmbError::TypeError {
                                message: "xcall requires function name as second operand".to_string(),
                            });
                        }
                    };
                    if let Some(sig) = env.get_function(&func_name) {
                        env.add_register(&dest_reg.name, sig.returns.clone());
                    } else {
                        return Err(BmbError::TypeError {
                            message: format!("Unknown function: {}", func_name),
                        });
                    }
                }
                Operand::Identifier(ref func) => {
                    // Void xcall: xcall func_name %args...
                    if env.get_function(&func.name).is_none() {
                        return Err(BmbError::TypeError {
                            message: format!("Unknown function: {}", func.name),
                        });
                    }
                }
                _ => {
                    return Err(BmbError::TypeError {
                        message: "xcall first operand must be register or function name".to_string(),
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

            let src_type = get_operand_type(&stmt.operands[1], env, registry)?;
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, src_type);
            }
        }

        Opcode::Load => {
            // load %dest %ptr - Load value from memory address in ptr
            // Philosophy: "Omission is guessing" - explicit memory access
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!("load requires 2 operands, got {}", stmt.operands.len()),
                });
            }

            // Get ptr type to determine loaded value type
            let ptr_type = get_operand_type(&stmt.operands[1], env, registry)?;

            // Determine the type being loaded based on pointer type
            let loaded_type = match &ptr_type {
                Type::Ptr(inner) | Type::Ref(inner) => (**inner).clone(),
                Type::BmbBox(inner) => (**inner).clone(),
                // If pointer is i32 (raw address), default to i32 load
                Type::I32 | Type::U32 => Type::I32,
                _ => {
                    return Err(BmbError::TypeError {
                        message: format!(
                            "load requires pointer operand, got {:?}",
                            ptr_type
                        ),
                    });
                }
            };

            // Register the destination with the loaded type
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, loaded_type);
            }
        }

        Opcode::Store => {
            // store %ptr %value - Store value at memory address in ptr
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!("store requires 2 operands, got {}", stmt.operands.len()),
                });
            }

            // Verify ptr operand is a pointer type
            let ptr_type = get_operand_type(&stmt.operands[0], env, registry)?;
            match &ptr_type {
                Type::Ptr(_) | Type::Ref(_) | Type::BmbBox(_) | Type::I32 | Type::U32 => {}
                _ => {
                    return Err(BmbError::TypeError {
                        message: format!(
                            "store requires pointer as first operand, got {:?}",
                            ptr_type
                        ),
                    });
                }
            }

            // Verify value operand exists
            let _ = get_operand_type(&stmt.operands[1], env, registry)?;
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

        Opcode::Box => {
            // box %dest %src - Allocate heap memory for value, store pointer
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!("box requires 2 operands (dest, src), got {}", stmt.operands.len()),
                });
            }

            // Get source type
            let src_type = get_operand_type(&stmt.operands[1], env, registry)?;

            // Destination register gets Box<T> type
            if let Operand::Register(ref r) = stmt.operands[0] {
                env.add_register(&r.name, Type::BmbBox(Box::new(src_type)));
            }
        }

        Opcode::Unbox => {
            // unbox %dest %src - Dereference Box pointer, read value
            if stmt.operands.len() != 2 {
                return Err(BmbError::TypeError {
                    message: format!("unbox requires 2 operands (dest, src), got {}", stmt.operands.len()),
                });
            }

            // Get source type (must be Box<T>)
            let src_type = get_operand_type(&stmt.operands[1], env, registry)?;

            match &src_type {
                Type::BmbBox(inner) => {
                    // Destination register gets the inner type
                    if let Operand::Register(ref r) = stmt.operands[0] {
                        env.add_register(&r.name, (**inner).clone());
                    }
                }
                _ => {
                    return Err(BmbError::TypeError {
                        message: format!("unbox requires Box<T> source, got {}", src_type),
                    });
                }
            }
        }

        Opcode::Drop => {
            // drop %src - Mark Box as freed (type checking only)
            if stmt.operands.len() != 1 {
                return Err(BmbError::TypeError {
                    message: format!("drop requires 1 operand, got {}", stmt.operands.len()),
                });
            }

            // Get source type (must be Box<T>)
            let src_type = get_operand_type(&stmt.operands[0], env, registry)?;

            if !matches!(src_type, Type::BmbBox(_)) {
                return Err(BmbError::TypeError {
                    message: format!("drop requires Box<T> operand, got {}", src_type),
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
        Operand::VariantConstructor {
            enum_name,
            variant_name: _,
            payload: _,
        } => {
            // Variant constructor creates an enum value
            // The semantic type is the enum type, though runtime representation
            // may be i64 for enums with payload (packed: discriminant << 32 | payload)
            // or i32 for simple enums (just discriminant)
            if registry.get_enum(&enum_name.name).is_some() {
                // Preserve enum type for type checking (enables pattern matching)
                Ok(Type::Enum(enum_name.name.clone()))
            } else {
                Err(BmbError::TypeError {
                    message: format!("Unknown enum: {}", enum_name.name),
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
            is_volatile: false,
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

    #[test]
    fn test_typecheck_refined_type_definition() {
        let source = r#"
@type nz_i32 i32 where self != 0

@node divide
@params a:i32 b:i32
@returns i32
  div %r a b
  ret %r
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Refined type definition failed: {:?}", result.err());

        let typed = result.unwrap();
        // Check that the refined type is registered
        assert!(typed.registry.get_refined_type("nz_i32").is_some());

        // Check that type_defs is populated
        assert_eq!(typed.type_defs.len(), 1);
        assert_eq!(typed.type_defs[0].name.name, "nz_i32");
    }

    #[test]
    fn test_typecheck_refined_type_base_resolution() {
        let mut registry = TypeRegistry::new();
        registry.add_refined_type(TypeDef {
            name: Identifier {
                name: "positive_i32".to_string(),
                span: Span::default(),
            },
            params: vec![],
            base_type: Type::I32,
            constraint: Expr::Binary {
                op: BinaryOp::Gt,
                left: Box::new(Expr::SelfRef),
                right: Box::new(Expr::IntLit(0)),
            },
            span: Span::default(),
        });

        // Check that we can resolve to base type
        assert_eq!(registry.resolve_to_base_type("positive_i32"), Some(&Type::I32));
        assert!(registry.is_defined("positive_i32"));
    }

    #[test]
    fn test_typecheck_refined_type_with_function_using_it() {
        let source = r#"
@type nz_i32 i32 where self != 0

@node safe_divide
@params a:i32 b:nz_i32
@returns i32
  div %r a b
  ret %r
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Function using refined type failed: {:?}", result.err());

        let typed = result.unwrap();
        // The function should typecheck successfully
        assert_eq!(typed.nodes.len(), 1);
    }

    #[test]
    fn test_refined_type_duplicate_error() {
        let source = r#"
@type nz_i32 i32 where self != 0
@type nz_i32 i32 where self > 0

@node test
@params
@returns i32
  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_err(), "Duplicate refined type should fail");
        let err = result.err().unwrap();
        assert!(err.to_string().contains("Duplicate type definition"));
    }

    #[test]
    fn test_refined_constraint_invalid_ret() {
        // Test that 'ret' in constraint is rejected
        let constraint = Expr::Binary {
            op: BinaryOp::Eq,
            left: Box::new(Expr::Ret),
            right: Box::new(Expr::IntLit(0)),
        };
        let result = validate_constraint_expr(&constraint);
        assert!(result.is_err());
        assert!(result.err().unwrap().to_string().contains("'ret' cannot be used"));
    }

    #[test]
    fn test_refined_constraint_invalid_old() {
        // Test that 'old()' in constraint is rejected
        let constraint = Expr::Old(Box::new(Expr::SelfRef));
        let result = validate_constraint_expr(&constraint);
        assert!(result.is_err());
        assert!(result.err().unwrap().to_string().contains("'old()' cannot be used"));
    }

    #[test]
    fn test_typecheck_option_param() {
        // Test Option<T> type as parameter - type is valid
        let source = r#"
@node maybe_value
@params x:Option<i32>
@returns i32

  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Option parameter type should typecheck: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_result_param() {
        // Test Result<T, E> type as parameter - type is valid
        let source = r#"
@node handle_result
@params r:Result<i32, bool>
@returns i32

  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Result parameter type should typecheck: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_vector_param() {
        // Test Vector<T> type as parameter - type is valid
        let source = r#"
@node sum_vector
@params v:Vector<f64>
@returns f64

  ret 0.0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Vector parameter type should typecheck: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_slice_param() {
        // Test Slice<T> type as parameter - type is valid
        let source = r#"
@node process_slice
@params s:Slice<i32>
@returns i32

  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Slice parameter type should typecheck: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_nested_generic_param() {
        // Test nested generic types: Option<Result<i32, bool>> as parameter
        let source = r#"
@node complex
@params x:Option<Result<i32, bool>>
@returns i32

  ret 0
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Nested generic parameter type should typecheck: {:?}", result.err());
    }

    #[test]
    fn test_validate_generic_types() {
        // Test that all generic types are validated correctly
        let registry = TypeRegistry::default();

        // Option<i32> is valid
        let opt_type = Type::Option(Box::new(Type::I32));
        assert!(validate_type(&opt_type, &registry).is_ok());

        // Result<i32, bool> is valid
        let result_type = Type::Result {
            ok: Box::new(Type::I32),
            err: Box::new(Type::Bool),
        };
        assert!(validate_type(&result_type, &registry).is_ok());

        // Vector<f64> is valid
        let vec_type = Type::Vector(Box::new(Type::F64));
        assert!(validate_type(&vec_type, &registry).is_ok());

        // Slice<i32> is valid
        let slice_type = Type::Slice(Box::new(Type::I32));
        assert!(validate_type(&slice_type, &registry).is_ok());

        // Nested: Option<Vector<i32>> is valid
        let nested_type = Type::Option(Box::new(Type::Vector(Box::new(Type::I32))));
        assert!(validate_type(&nested_type, &registry).is_ok());
    }

    // ===== v0.10.0 Tests: Linear Type Checking =====

    #[test]
    fn test_linear_type_used_once() {
        // @consume param used exactly once: should pass
        let node = Node {
            is_public: false,
            name: Identifier::new("free_buffer", Span::default()),
            tags: vec![],
            params: vec![Parameter {
                name: Identifier::new("buf", Span::default()),
                ty: Type::Ptr(Box::new(Type::U8)),
                annotation: ParamAnnotation::Consume,
                span: Span::default(),
            }],
            returns: Type::Void,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body: vec![
                Instruction::Statement(Statement {
                    opcode: Opcode::Mov,
                    operands: vec![
                        Operand::Register(Identifier::new("0", Span::default())),
                        Operand::Identifier(Identifier::new("buf", Span::default())),
                    ],
                    span: Span::default(),
                }),
            ],
            span: Span::default(),
        };

        let env = TypeEnv::new();
        let registry = TypeRegistry::new();
        let result = typecheck_node(&node, &env, &registry);
        assert!(result.is_ok(), "Linear param used once should pass: {:?}", result.err());
    }

    #[test]
    fn test_linear_type_never_used() {
        // @consume param never used: should fail
        let node = Node {
            is_public: false,
            name: Identifier::new("unused_buffer", Span::default()),
            tags: vec![],
            params: vec![Parameter {
                name: Identifier::new("buf", Span::default()),
                ty: Type::Ptr(Box::new(Type::U8)),
                annotation: ParamAnnotation::Consume,
                span: Span::default(),
            }, Parameter {
                name: Identifier::new("x", Span::default()),
                ty: Type::I32,
                annotation: ParamAnnotation::None,
                span: Span::default(),
            }],
            returns: Type::I32,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body: vec![
                // Use x (non-linear) but not buf (linear)
                Instruction::Statement(Statement {
                    opcode: Opcode::Ret,
                    operands: vec![
                        Operand::Identifier(Identifier::new("x", Span::default())),
                    ],
                    span: Span::default(),
                }),
            ],
            span: Span::default(),
        };

        let env = TypeEnv::new();
        let registry = TypeRegistry::new();
        let result = typecheck_node(&node, &env, &registry);
        assert!(result.is_err(), "Linear param never used should fail");

        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(err_msg.contains("never used"), "Error should mention 'never used': {}", err_msg);
    }

    #[test]
    fn test_linear_type_used_twice() {
        // @consume param used twice: should fail
        let node = Node {
            is_public: false,
            name: Identifier::new("double_use", Span::default()),
            tags: vec![],
            params: vec![Parameter {
                name: Identifier::new("buf", Span::default()),
                ty: Type::Ptr(Box::new(Type::U8)),
                annotation: ParamAnnotation::Consume,
                span: Span::default(),
            }],
            returns: Type::Void,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body: vec![
                Instruction::Statement(Statement {
                    opcode: Opcode::Mov,
                    operands: vec![
                        Operand::Register(Identifier::new("0", Span::default())),
                        Operand::Identifier(Identifier::new("buf", Span::default())),
                    ],
                    span: Span::default(),
                }),
                Instruction::Statement(Statement {
                    opcode: Opcode::Mov,
                    operands: vec![
                        Operand::Register(Identifier::new("1", Span::default())),
                        Operand::Identifier(Identifier::new("buf", Span::default())),
                    ],
                    span: Span::default(),
                }),
            ],
            span: Span::default(),
        };

        let env = TypeEnv::new();
        let registry = TypeRegistry::new();
        let result = typecheck_node(&node, &env, &registry);
        assert!(result.is_err(), "Linear param used twice should fail");

        let err_msg = format!("{:?}", result.err().unwrap());
        assert!(err_msg.contains("2 times"), "Error should mention '2 times': {}", err_msg);
    }

    #[test]
    fn test_regular_param_no_linear_check() {
        // Regular param (no annotation) can be used any number of times
        let node = Node {
            is_public: false,
            name: Identifier::new("normal_func", Span::default()),
            tags: vec![],
            params: vec![Parameter {
                name: Identifier::new("x", Span::default()),
                ty: Type::I32,
                annotation: ParamAnnotation::None,
                span: Span::default(),
            }],
            returns: Type::I32,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body: vec![
                Instruction::Statement(Statement {
                    opcode: Opcode::Add,
                    operands: vec![
                        Operand::Register(Identifier::new("0", Span::default())),
                        Operand::Identifier(Identifier::new("x", Span::default())),
                        Operand::Identifier(Identifier::new("x", Span::default())),
                    ],
                    span: Span::default(),
                }),
                Instruction::Statement(Statement {
                    opcode: Opcode::Ret,
                    operands: vec![Operand::Register(Identifier::new("0", Span::default()))],
                    span: Span::default(),
                }),
            ],
            span: Span::default(),
        };

        let env = TypeEnv::new();
        let registry = TypeRegistry::new();
        let result = typecheck_node(&node, &env, &registry);
        assert!(result.is_ok(), "Regular param can be used multiple times: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_match_literal_patterns() {
        let source = r#"
@node classify
@params n:i32
@returns i32

  mov %x n
  @match %x
  @case 0:
    mov %result 0
    ret %result
  @case 1:
    mov %result 1
    ret %result
  @default:
    mov %result 2
    ret %result
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Match type check failed: {:?}", result.err());
    }

    #[test]
    fn test_typecheck_match_wrong_pattern_type() {
        let source = r#"
@node classify
@params n:i32
@returns i32

  mov %x n
  @match %x
  @case true:
    mov %result 0
    ret %result
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_err(), "Should fail: bool pattern on i32 scrutinee");
        let err_msg = format!("{:?}", result.err());
        assert!(err_msg.contains("Bool pattern cannot match"), "Error message: {}", err_msg);
    }

    #[test]
    fn test_typecheck_match_enum_variants() {
        let source = r#"
@enum Status
  Ok:i32
  Err:i32

@node handle
@params r:Status
@returns i32

  mov %x r
  @match %x
  @case Status::Ok(%val):
    ret %val
  @case Status::Err(%code):
    ret %code
"#;
        let program = parser::parse(source).unwrap();
        let result = typecheck(&program);
        assert!(result.is_ok(), "Enum match type check failed: {:?}", result.err());
    }
}
