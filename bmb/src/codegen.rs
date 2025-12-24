//! BMB Code Generator
//!
//! Generates WebAssembly from type-checked BMB AST.
//!
//! "Omission is guessing, and guessing is error."
//! - Every type decision is explicit based on TypedNode analysis

use std::collections::HashMap;

use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, ExportKind, ExportSection, Function, FunctionSection,
    GlobalSection, GlobalType, ImportSection, Instruction, MemorySection, MemoryType, Module,
    TypeSection, ValType,
};

use crate::ast::{self, Invariant, Node, Opcode, Operand, Statement, Type};
use crate::contracts::{ContractCodeGenerator, VerifiedProgram};
use crate::types::{TypedNode, TypeRegistry};
use crate::{BmbError, Result};

/// Memory layout information for a struct
#[derive(Debug, Clone)]
pub struct StructLayout {
    /// Total size in bytes
    pub size: u32,
    /// Alignment in bytes
    pub alignment: u32,
    /// Field offsets by name
    pub fields: HashMap<String, FieldLayout>,
}

/// Layout for a single field
#[derive(Debug, Clone)]
pub struct FieldLayout {
    pub offset: u32,
    pub size: u32,
    pub ty: Type,
}

impl StructLayout {
    /// Calculate layout for a struct given its fields
    pub fn calculate(fields: &[(String, Type)]) -> Self {
        let mut offset = 0u32;
        let mut max_align = 1u32;
        let mut field_layouts = HashMap::new();

        for (name, ty) in fields {
            let (size, align) = type_size_align(ty);
            max_align = max_align.max(align);

            // Align offset
            offset = (offset + align - 1) & !(align - 1);

            field_layouts.insert(
                name.clone(),
                FieldLayout {
                    offset,
                    size,
                    ty: ty.clone(),
                },
            );

            offset += size;
        }

        // Align total size to struct alignment
        let size = (offset + max_align - 1) & !(max_align - 1);

        StructLayout {
            size,
            alignment: max_align,
            fields: field_layouts,
        }
    }
}

/// Get size and alignment for a type
fn type_size_align(ty: &Type) -> (u32, u32) {
    match ty {
        // 8-bit types (native size for memory layout)
        Type::I8 | Type::U8 => (1, 1),
        // 16-bit types
        Type::I16 | Type::U16 => (2, 2),
        // 32-bit types (Bool is i32 in WASM for efficiency)
        Type::I32 | Type::U32 | Type::F32 | Type::Char | Type::Bool => (4, 4),
        // 64-bit types
        Type::I64 | Type::U64 | Type::F64 => (8, 8),
        Type::Void => (0, 1),
        Type::Array { element, size } => {
            let (elem_size, elem_align) = type_size_align(element);
            (elem_size * (*size as u32), elem_align)
        }
        // Pointers are 32-bit in WASM32
        Type::Ref(_) | Type::Ptr(_) => (4, 4),
        // Struct and Enum are handled via layout calculation
        Type::Struct(_) | Type::Enum(_) => (4, 4), // Placeholder - actual size from registry
        // Refined types use their base type's size (resolved at type check time)
        Type::Refined { .. } => (4, 4), // Placeholder - actual size from type registry
        // Generic built-in types (v0.8+)
        Type::Option(inner) => {
            // Option<T> = tag (i32) + value (T), aligned to max alignment
            let (inner_size, inner_align) = type_size_align(inner);
            let align = inner_align.max(4);
            let size = 4 + inner_size; // tag + value
            (size, align)
        }
        Type::Result { ok, err } => {
            // Result<T,E> = tag (i32) + max(T, E), aligned to max alignment
            let (ok_size, ok_align) = type_size_align(ok);
            let (err_size, err_align) = type_size_align(err);
            let inner_size = ok_size.max(err_size);
            let align = ok_align.max(err_align).max(4);
            (4 + inner_size, align) // tag + max(ok, err)
        }
        // Vector and Slice are represented as pointers in WASM32
        Type::Vector(_) => (4, 4), // Pointer to heap allocation
        Type::Slice(_) => (8, 4),
        // String types (v0.9+) - UTF-8 strings are fat pointers
        Type::BmbString => (12, 4), // ptr(4) + len(4) + cap(4) on WASM32
        Type::BmbStr => (8, 4),     // ptr(4) + len(4) - borrowed slice  // Pointer + length (fat pointer)
        // Box type (v0.13+) - heap-allocated pointer
        Type::BmbBox(_) => (4, 4),  // Just a pointer on WASM32
    }
}

/// Generate WebAssembly binary from a verified program
///
/// # Arguments
///
/// * `program` - The verified AST to generate code from
///
/// # Returns
///
/// The WebAssembly binary or a code generation error
pub fn generate(program: &VerifiedProgram) -> Result<Vec<u8>> {
    let mut generator = CodeGenerator::new();
    generator.generate_program(&program.program)?;
    Ok(generator.finish())
}

struct CodeGenerator {
    module: Module,
    types: TypeSection,
    imports: ImportSection,
    functions: FunctionSection,
    memory: MemorySection,
    globals: GlobalSection,
    exports: ExportSection,
    code: CodeSection,
    function_indices: HashMap<String, u32>,
    struct_layouts: HashMap<String, StructLayout>,
    /// Enum definitions for pattern matching codegen
    enums: HashMap<String, crate::ast::EnumDef>,
    next_func_idx: u32,
    next_type_idx: u32,
    /// Flag to track if memory is needed
    needs_memory: bool,
    /// Flag to track if heap allocation is needed (for Box<T>)
    needs_heap: bool,
    /// Global index for heap pointer (bump allocator)
    heap_ptr_global_idx: u32,
}

impl CodeGenerator {
    fn new() -> Self {
        Self {
            module: Module::new(),
            types: TypeSection::new(),
            imports: ImportSection::new(),
            functions: FunctionSection::new(),
            memory: MemorySection::new(),
            globals: GlobalSection::new(),
            exports: ExportSection::new(),
            code: CodeSection::new(),
            function_indices: HashMap::new(),
            struct_layouts: HashMap::new(),
            enums: HashMap::new(),
            next_func_idx: 0,
            next_type_idx: 0,
            needs_memory: false,
            needs_heap: false,
            heap_ptr_global_idx: 0,
        }
    }

    /// Calculate and store layouts for all structs
    fn calculate_struct_layouts(&mut self, registry: &TypeRegistry) {
        for (name, struct_def) in &registry.structs {
            let fields: Vec<(String, Type)> = struct_def
                .fields
                .iter()
                .map(|f| (f.name.name.clone(), f.ty.clone()))
                .collect();
            let layout = StructLayout::calculate(&fields);
            self.struct_layouts.insert(name.clone(), layout);
            self.needs_memory = true;
        }
    }

    /// Get layout for a struct by name (for future struct field access)
    #[allow(dead_code)]
    fn get_struct_layout(&self, name: &str) -> Option<&StructLayout> {
        self.struct_layouts.get(name)
    }

    fn generate_program(&mut self, program: &crate::types::TypedProgram) -> Result<()> {
        // Phase 0: Calculate struct layouts from registry
        self.calculate_struct_layouts(&program.registry);

        // Store enum definitions for pattern matching codegen
        for (name, enum_def) in &program.registry.enums {
            self.enums.insert(name.clone(), enum_def.clone());
        }

        // First pass: register imported functions
        // Imported functions take function indices before local functions
        for import in &program.imports {
            let type_idx = self.register_import_type(import)?;
            self.function_indices
                .insert(import.name.name.clone(), self.next_func_idx);
            self.imports.import(
                "env",
                &import.name.name,
                wasm_encoder::EntityType::Function(type_idx),
            );
            self.next_func_idx += 1;
        }

        // First pass (continued): register extern functions with explicit module names (v0.12+)
        // Extern functions use two-level namespace: module/function
        for extern_def in &program.extern_defs {
            let type_idx = self.register_extern_type(extern_def)?;
            self.function_indices
                .insert(extern_def.name.name.clone(), self.next_func_idx);
            // Use source_module if specified, otherwise default to "env"
            let module_name = extern_def
                .source_module
                .as_deref()
                .unwrap_or("env");
            self.imports.import(
                module_name,
                &extern_def.name.name,
                wasm_encoder::EntityType::Function(type_idx),
            );
            self.next_func_idx += 1;
        }

        // Second pass: register local function types
        // Check if any function has @pub annotation for backwards compatibility (v0.12+)
        // If no functions have @pub, export all (legacy behavior)
        // If any function has @pub, only export @pub functions
        let has_any_public = program.nodes.iter().any(|n| n.node.is_public);

        for typed_node in &program.nodes {
            let node = &typed_node.node;
            let type_idx = self.register_function_type(node)?;
            self.function_indices
                .insert(node.name.name.clone(), self.next_func_idx);
            self.functions.function(type_idx);

            // Export based on visibility: if no @pub exists, export all; otherwise only @pub
            if !has_any_public || node.is_public {
                self.exports
                    .export(&node.name.name, ExportKind::Func, self.next_func_idx);
            }
            self.next_func_idx += 1;
        }

        // Detection pass: check if heap allocation is needed (Box<T> usage)
        for typed_node in &program.nodes {
            if self.uses_heap_allocation(&typed_node.node) {
                self.needs_heap = true;
                break;
            }
        }

        // Third pass: generate function bodies
        for typed_node in &program.nodes {
            self.generate_function(typed_node, &program.contracts)?;
        }

        Ok(())
    }

    /// Check if a node uses heap allocation (box/unbox/drop opcodes)
    fn uses_heap_allocation(&self, node: &Node) -> bool {
        for instr in &node.body {
            match instr {
                ast::Instruction::Statement(stmt) => {
                    if matches!(stmt.opcode, Opcode::Box | Opcode::Unbox | Opcode::Drop) {
                        return true;
                    }
                }
                ast::Instruction::Match(match_stmt) => {
                    // Check match arms for heap ops
                    for arm in &match_stmt.arms {
                        for instr in &arm.body {
                            if let ast::Instruction::Statement(stmt) = instr {
                                if matches!(stmt.opcode, Opcode::Box | Opcode::Unbox | Opcode::Drop)
                                {
                                    return true;
                                }
                            }
                        }
                    }
                    if let Some(default) = &match_stmt.default {
                        for instr in &default.body {
                            if let ast::Instruction::Statement(stmt) = instr {
                                if matches!(stmt.opcode, Opcode::Box | Opcode::Unbox | Opcode::Drop)
                                {
                                    return true;
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn register_import_type(&mut self, import: &crate::ast::Import) -> Result<u32> {
        let params: Vec<ValType> = import
            .param_types
            .iter()
            .map(|t| type_to_valtype(t))
            .collect();
        // Imported functions (like print_i32) don't return values
        let results: Vec<ValType> = vec![];

        let type_idx = self.next_type_idx;
        self.types.ty().function(params, results);
        self.next_type_idx += 1;
        Ok(type_idx)
    }

    /// Register type for @extern function declaration (v0.12+)
    /// Unlike legacy imports, extern functions have explicit return types
    fn register_extern_type(&mut self, extern_def: &crate::ast::ExternDef) -> Result<u32> {
        let params: Vec<ValType> = extern_def
            .params
            .iter()
            .map(|p| type_to_valtype(&p.ty))
            .collect();
        // Extern functions have explicit return types (unlike legacy imports)
        let results: Vec<ValType> = match &extern_def.returns {
            crate::ast::Type::Void => vec![],
            ty => vec![type_to_valtype(ty)],
        };

        let type_idx = self.next_type_idx;
        self.types.ty().function(params, results);
        self.next_type_idx += 1;
        Ok(type_idx)
    }

    fn register_function_type(&mut self, node: &Node) -> Result<u32> {
        let params: Vec<ValType> = node.params.iter().map(|p| type_to_valtype(&p.ty)).collect();
        let results = vec![type_to_valtype(&node.returns)];

        let type_idx = self.next_type_idx;
        self.types.ty().function(params, results);
        self.next_type_idx += 1;
        Ok(type_idx)
    }

    fn generate_function(
        &mut self,
        typed_node: &TypedNode,
        contracts: &[crate::ast::ContractDef],
    ) -> Result<()> {
        let node = &typed_node.node;

        // Build locals map: parameters first, then registers
        let mut locals: HashMap<String, u32> = HashMap::new();
        let mut local_types: Vec<(u32, ValType)> = Vec::new();

        // Map parameters (they are already locals 0..n-1)
        for (idx, param) in node.params.iter().enumerate() {
            locals.insert(param.name.name.clone(), idx as u32);
        }

        let param_count = node.params.len() as u32;

        // Map registers - collect unique registers with their types
        let mut register_list: Vec<(&String, &Type)> = typed_node.register_types.iter().collect();
        // Sort for deterministic ordering
        register_list.sort_by_key(|(name, _)| *name);

        for (reg_name, reg_type) in register_list {
            if !locals.contains_key(reg_name) {
                let local_idx = param_count + local_types.len() as u32;
                locals.insert(reg_name.clone(), local_idx);
                local_types.push((1, type_to_valtype(reg_type)));
            }
        }

        // Expand @requires directives into constituent contracts
        let expanded = crate::contracts::expand_requires(node, contracts)?;

        // Add a result local for postcondition checking if needed
        // Also needed for expanded postconditions from @requires
        let result_local = if !node.postconditions.is_empty() || !expanded.postconditions.is_empty()
        {
            let idx = param_count + local_types.len() as u32;
            local_types.push((1, type_to_valtype(&node.returns)));
            Some(idx)
        } else {
            None
        };

        // Create function with locals
        let mut func = Function::new(local_types);

        // Build type map for contract generator (params + registers)
        let mut all_types: HashMap<String, Type> = node
            .params
            .iter()
            .map(|p| (p.name.name.clone(), p.ty.clone()))
            .collect();
        for (name, ty) in &typed_node.register_types {
            all_types.insert(name.clone(), ty.clone());
        }

        // Generate precondition checks at function entry (multiple allowed)
        for pre in &node.preconditions {
            let contract_gen =
                ContractCodeGenerator::new(&locals, &all_types, node.returns.clone());
            contract_gen.generate_precondition(pre, &mut func);
        }

        // Generate expanded preconditions from @requires
        for pre in &expanded.preconditions {
            let contract_gen =
                ContractCodeGenerator::new(&locals, &all_types, node.returns.clone());
            contract_gen.generate_precondition(pre, &mut func);
        }

        // Generate assertion checks after preconditions (multiple allowed)
        for assertion in &node.assertions {
            let contract_gen =
                ContractCodeGenerator::new(&locals, &all_types, node.returns.clone());
            contract_gen.generate_assertion(&assertion.condition, &mut func);
        }

        // Combine postconditions from node and expanded @requires
        let mut all_postconditions = node.postconditions.clone();
        all_postconditions.extend(expanded.postconditions);

        // Create function context for code generation
        let ctx = FunctionContext {
            locals: &locals,
            register_types: &typed_node.register_types,
            param_types: node
                .params
                .iter()
                .map(|p| (p.name.name.clone(), p.ty.clone()))
                .collect(),
            return_type: node.returns.clone(),
            function_indices: &self.function_indices,
            postconditions: all_postconditions,
            all_types: all_types.clone(),
            result_local,
            invariants: &node.invariants,
        };

        // Analyze control flow for labels
        let cf = analyze_control_flow(&node.body);

        // Generate instructions
        self.generate_body(&node.body, &mut func, &ctx, &cf)?;

        // Ensure function ends properly
        func.instruction(&Instruction::End);

        self.code.function(&func);
        Ok(())
    }

    fn generate_body(
        &self,
        body: &[ast::Instruction],
        func: &mut Function,
        ctx: &FunctionContext,
        cf: &ControlFlowAnalysis,
    ) -> Result<()> {
        // Track which loops and blocks need to be closed
        let mut open_loops: Vec<String> = Vec::new();
        let mut open_blocks: Vec<String> = Vec::new();

        for (pos, instruction) in body.iter().enumerate() {
            // Check if any blocks start at this position (before processing the instruction)
            let blocks_starting: Vec<String> = cf
                .labels
                .iter()
                .filter(|(_, info)| info.block_start_position == Some(pos))
                .map(|(name, _)| name.clone())
                .collect();

            for block_name in blocks_starting {
                // Start a block for forward jumps
                func.instruction(&Instruction::Block(BlockType::Empty));
                open_blocks.push(block_name);
            }

            match instruction {
                ast::Instruction::Label(id) => {
                    // Labels in BMB are targets for jumps
                    // In Wasm, we use block/loop structure
                    if let Some(info) = cf.labels.get(&id.name) {
                        // Close block if this label is a block target
                        if info.is_block_target {
                            if let Some(idx) = open_blocks.iter().rposition(|b| b == &id.name) {
                                func.instruction(&Instruction::End);
                                open_blocks.remove(idx);
                            }
                        }
                        // Start loop if this label is a loop target
                        if info.is_loop_target {
                            func.instruction(&Instruction::Loop(BlockType::Empty));
                            open_loops.push(id.name.clone());

                            // Generate invariant check at the start of each loop iteration
                            // @invariant _label condition
                            if let Some(inv) = ctx
                                .invariants
                                .iter()
                                .find(|inv| inv.label.name == id.name)
                            {
                                let contract_gen = ContractCodeGenerator::new(
                                    ctx.locals,
                                    &ctx.all_types,
                                    ctx.return_type.clone(),
                                );
                                contract_gen.generate_assertion(&inv.condition, func);
                            }
                        }
                    }
                }
                ast::Instruction::Statement(stmt) => {
                    self.generate_statement(stmt, func, ctx, cf, pos)?;

                    // Check if any loops end at this position
                    // Close loops in reverse order (innermost first)
                    let loops_to_close: Vec<String> = cf
                        .labels
                        .iter()
                        .filter(|(_, info)| info.loop_end_position == Some(pos))
                        .map(|(name, _)| name.clone())
                        .collect();

                    for loop_name in loops_to_close {
                        if let Some(idx) = open_loops.iter().rposition(|l| l == &loop_name) {
                            // Close this loop
                            func.instruction(&Instruction::End);
                            open_loops.remove(idx);
                        }
                    }
                }
                ast::Instruction::Match(match_stmt) => {
                    self.generate_match(match_stmt, func, ctx)?;
                }
            }
        }

        // Close any remaining open structures (shouldn't happen in well-formed code)
        for _ in open_blocks.iter() {
            func.instruction(&Instruction::End);
        }
        for _ in open_loops.iter() {
            func.instruction(&Instruction::End);
        }

        Ok(())
    }

    fn generate_statement(
        &self,
        stmt: &Statement,
        func: &mut Function,
        ctx: &FunctionContext,
        cf: &ControlFlowAnalysis,
        current_pos: usize,
    ) -> Result<()> {
        match stmt.opcode {
            Opcode::Add => self.generate_binary_op(stmt, func, ctx, BinaryOp::Add)?,
            Opcode::Sub => self.generate_binary_op(stmt, func, ctx, BinaryOp::Sub)?,
            Opcode::Mul => self.generate_binary_op(stmt, func, ctx, BinaryOp::Mul)?,
            Opcode::Div => self.generate_binary_op(stmt, func, ctx, BinaryOp::Div)?,
            Opcode::Mod => self.generate_binary_op(stmt, func, ctx, BinaryOp::Mod)?,
            Opcode::And => self.generate_binary_op(stmt, func, ctx, BinaryOp::And)?,
            Opcode::Or => self.generate_binary_op(stmt, func, ctx, BinaryOp::Or)?,
            Opcode::Xor => self.generate_binary_op(stmt, func, ctx, BinaryOp::Xor)?,
            Opcode::Shl => self.generate_binary_op(stmt, func, ctx, BinaryOp::Shl)?,
            Opcode::Shr => self.generate_binary_op(stmt, func, ctx, BinaryOp::Shr)?,
            Opcode::Not => self.generate_unary_not(stmt, func, ctx)?,
            Opcode::Eq => self.generate_binary_op(stmt, func, ctx, BinaryOp::Eq)?,
            Opcode::Ne => self.generate_binary_op(stmt, func, ctx, BinaryOp::Ne)?,
            Opcode::Lt => self.generate_binary_op(stmt, func, ctx, BinaryOp::Lt)?,
            Opcode::Le => self.generate_binary_op(stmt, func, ctx, BinaryOp::Le)?,
            Opcode::Gt => self.generate_binary_op(stmt, func, ctx, BinaryOp::Gt)?,
            Opcode::Ge => self.generate_binary_op(stmt, func, ctx, BinaryOp::Ge)?,

            Opcode::Ret => {
                // Load return value
                self.generate_operand(&stmt.operands[0], func, ctx)?;

                // If there are postconditions, check them before returning
                if !ctx.postconditions.is_empty() {
                    if let Some(result_local) = ctx.result_local {
                        // Store result to check postconditions
                        func.instruction(&Instruction::LocalSet(result_local));

                        // Generate postcondition checks (all must pass)
                        for post in &ctx.postconditions {
                            let mut contract_gen = ContractCodeGenerator::new(
                                ctx.locals,
                                &ctx.all_types,
                                ctx.return_type.clone(),
                            );
                            contract_gen.set_result_local(result_local);
                            contract_gen.generate_postcondition(post, func);
                        }

                        // Load result for return
                        func.instruction(&Instruction::LocalGet(result_local));
                    }
                }

                func.instruction(&Instruction::Return);
            }

            Opcode::Jmp => {
                // Unconditional jump to label
                if let Operand::Label(label_id) = &stmt.operands[0] {
                    if let Some(_info) = cf.labels.get(&label_id.name) {
                        // Calculate branch depth based on active loops at current position
                        let depth = self.calculate_branch_depth(&label_id.name, current_pos, cf);
                        func.instruction(&Instruction::Br(depth));
                    }
                }
            }

            Opcode::Jif => {
                // Conditional jump: jif condition label
                // Jump to label if condition is true (non-zero)
                self.generate_operand(&stmt.operands[0], func, ctx)?;

                if let Operand::Label(label_id) = &stmt.operands[1] {
                    if let Some(_info) = cf.labels.get(&label_id.name) {
                        // Calculate branch depth based on active loops at current position
                        let depth = self.calculate_branch_depth(&label_id.name, current_pos, cf);
                        func.instruction(&Instruction::BrIf(depth));
                    }
                }
            }

            Opcode::Call => {
                // call result_reg function_name args...
                // First operand is result register, second is function name or qualified ident
                let func_name = match &stmt.operands[1] {
                    Operand::Identifier(id) => id.name.clone(),
                    Operand::QualifiedIdent { module, name } => {
                        // Qualified identifier: module::function
                        format!("{}::{}", module.name, name.name)
                    }
                    _ => {
                        return Err(BmbError::CodegenError {
                            message: "Call requires function name".to_string(),
                        })
                    }
                };

                // Push arguments (operands 2..)
                for operand in stmt.operands.iter().skip(2) {
                    self.generate_operand(operand, func, ctx)?;
                }

                // Call function
                if let Some(&func_idx) = ctx.function_indices.get(&func_name) {
                    func.instruction(&Instruction::Call(func_idx));
                } else {
                    return Err(BmbError::CodegenError {
                        message: format!("Unknown function: {}", func_name),
                    });
                }

                // Store result
                if let Operand::Register(r) = &stmt.operands[0] {
                    if let Some(&idx) = ctx.locals.get(&r.name) {
                        func.instruction(&Instruction::LocalSet(idx));
                    }
                }
            }

            Opcode::Xcall => {
                // xcall function_name args...
                // External call to void function (no return value)
                // First operand is function name, rest are arguments
                let func_name = match &stmt.operands[0] {
                    Operand::Identifier(id) => &id.name,
                    _ => {
                        return Err(BmbError::CodegenError {
                            message: "Xcall requires function name".to_string(),
                        })
                    }
                };

                // Push arguments (operands 1..)
                for operand in stmt.operands.iter().skip(1) {
                    self.generate_operand(operand, func, ctx)?;
                }

                // Call function (no return value to store)
                if let Some(&func_idx) = ctx.function_indices.get(func_name) {
                    func.instruction(&Instruction::Call(func_idx));
                } else {
                    return Err(BmbError::CodegenError {
                        message: format!("Unknown function: {}", func_name),
                    });
                }
            }

            Opcode::Mov => {
                // mov dest src
                self.generate_operand(&stmt.operands[1], func, ctx)?;
                if let Operand::Register(r) = &stmt.operands[0] {
                    if let Some(&idx) = ctx.locals.get(&r.name) {
                        func.instruction(&Instruction::LocalSet(idx));
                    }
                }
            }

            Opcode::Load => {
                // load %dest %ptr - Load value from memory at address in %ptr
                // Philosophy: "Omission is guessing" - explicit memory access
                //
                // Operands: [dest_register, ptr_register]
                // 1. Get address from ptr register
                // 2. Load value from memory[address]
                // 3. Store result in dest register

                // Determine the type to load based on destination register or pointer type
                let load_type = if let Operand::Register(r) = &stmt.operands[0] {
                    ctx.register_types
                        .get(&r.name)
                        .cloned()
                        .unwrap_or(Type::I32)
                } else if let Operand::Register(r) = &stmt.operands[1] {
                    // Try to get inner type from pointer type
                    if let Some(Type::Ptr(inner)) = ctx.register_types.get(&r.name) {
                        (**inner).clone()
                    } else {
                        Type::I32
                    }
                } else {
                    Type::I32
                };

                // Get destination register index
                let dest_idx = if let Operand::Register(r) = &stmt.operands[0] {
                    *ctx.locals.get(&r.name).unwrap_or(&0)
                } else {
                    return Err(BmbError::CodegenError {
                        message: "load: destination must be a register".to_string(),
                    });
                };

                // Load the address from ptr register
                self.generate_operand(&stmt.operands[1], func, ctx)?;

                // Generate appropriate load instruction based on type
                match load_type {
                    Type::I8 => {
                        func.instruction(&Instruction::I32Load8S(wasm_encoder::MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }));
                    }
                    Type::U8 | Type::Bool => {
                        func.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }));
                    }
                    Type::I16 => {
                        func.instruction(&Instruction::I32Load16S(wasm_encoder::MemArg {
                            offset: 0,
                            align: 1,
                            memory_index: 0,
                        }));
                    }
                    Type::U16 => {
                        func.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                            offset: 0,
                            align: 1,
                            memory_index: 0,
                        }));
                    }
                    Type::I32 | Type::U32 | Type::Char | Type::Enum(_) | Type::Ptr(_) | Type::Ref(_) => {
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::I64 | Type::U64 => {
                        func.instruction(&Instruction::I64Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    Type::F32 => {
                        func.instruction(&Instruction::F32Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::F64 => {
                        func.instruction(&Instruction::F64Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    _ => {
                        // Default to i32 load for unknown types
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                }

                // Store result in destination register
                func.instruction(&Instruction::LocalSet(dest_idx));
            }

            Opcode::Store => {
                // store %ptr %value - Store value at memory address in %ptr
                // Philosophy: "Omission is guessing" - explicit memory writes
                //
                // Operands: [ptr_register, value_operand]
                // 1. Get address from ptr register
                // 2. Get value to store
                // 3. Store value at memory[address]

                // Determine the type to store based on value operand
                let store_type = if let Operand::Register(r) = &stmt.operands[1] {
                    ctx.register_types
                        .get(&r.name)
                        .cloned()
                        .unwrap_or(Type::I32)
                } else if let Operand::Register(r) = &stmt.operands[0] {
                    // Try to get inner type from pointer type
                    if let Some(Type::Ptr(inner)) = ctx.register_types.get(&r.name) {
                        (**inner).clone()
                    } else {
                        Type::I32
                    }
                } else {
                    Type::I32 // Default for literals
                };

                // Load address onto stack first
                self.generate_operand(&stmt.operands[0], func, ctx)?;

                // Load value onto stack
                self.generate_operand(&stmt.operands[1], func, ctx)?;

                // Generate appropriate store instruction based on type
                match store_type {
                    Type::I8 | Type::U8 | Type::Bool => {
                        func.instruction(&Instruction::I32Store8(wasm_encoder::MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }));
                    }
                    Type::I16 | Type::U16 => {
                        func.instruction(&Instruction::I32Store16(wasm_encoder::MemArg {
                            offset: 0,
                            align: 1,
                            memory_index: 0,
                        }));
                    }
                    Type::I32 | Type::U32 | Type::Char | Type::Enum(_) | Type::Ptr(_) | Type::Ref(_) => {
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::I64 | Type::U64 => {
                        func.instruction(&Instruction::I64Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    Type::F32 => {
                        func.instruction(&Instruction::F32Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::F64 => {
                        func.instruction(&Instruction::F64Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    _ => {
                        // Default to i32 store for unknown types
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                }
            }

            Opcode::Print => {
                // Print is not directly supported in WASM
                // For x64 native compilation, use compile_to_x64() instead
                return Err(BmbError::CodegenError {
                    message: "print opcode is not supported in WASM. Use --emit elf for native x64 compilation.".to_string(),
                });
            }

            Opcode::Box => {
                // box %dest %src - Allocate heap memory for value, store pointer
                // Bump allocator implementation:
                // 1. Get current heap pointer
                // 2. Store value at heap pointer
                // 3. Store heap pointer in %dest (this is the Box pointer)
                // 4. Increment heap pointer by value size

                // Get source value type to determine size
                let src_type = if let Operand::Register(r) = &stmt.operands[1] {
                    ctx.register_types
                        .get(&r.name)
                        .cloned()
                        .unwrap_or(Type::I32)
                } else {
                    Type::I32 // Default for literals
                };
                let (size, _align) = type_size_align(&src_type);

                // Get destination register index
                let dest_idx = if let Operand::Register(r) = &stmt.operands[0] {
                    *ctx.locals.get(&r.name).unwrap_or(&0)
                } else {
                    0
                };

                // Step 1: Get current heap pointer and save it for the Box pointer
                func.instruction(&Instruction::GlobalGet(self.heap_ptr_global_idx));

                // Step 2: Store value at heap pointer address
                // First, duplicate the heap pointer for the store operation
                func.instruction(&Instruction::GlobalGet(self.heap_ptr_global_idx));
                // Load source value onto stack
                self.generate_operand(&stmt.operands[1], func, ctx)?;
                // Store value at [heap_ptr]
                match src_type {
                    Type::I8 | Type::U8 | Type::Bool => {
                        func.instruction(&Instruction::I32Store8(wasm_encoder::MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }));
                    }
                    Type::I16 | Type::U16 => {
                        func.instruction(&Instruction::I32Store16(wasm_encoder::MemArg {
                            offset: 0,
                            align: 1,
                            memory_index: 0,
                        }));
                    }
                    Type::I32 | Type::U32 | Type::Char | Type::Enum(_) | Type::BmbBox(_) => {
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::I64 | Type::U64 => {
                        func.instruction(&Instruction::I64Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    Type::F32 => {
                        func.instruction(&Instruction::F32Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::F64 => {
                        func.instruction(&Instruction::F64Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    _ => {
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                }

                // Step 3: The heap pointer on stack becomes the Box pointer
                // (Already on stack from Step 1)
                func.instruction(&Instruction::LocalSet(dest_idx));

                // Step 4: Increment heap pointer by size
                func.instruction(&Instruction::GlobalGet(self.heap_ptr_global_idx));
                func.instruction(&Instruction::I32Const(size as i32));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::GlobalSet(self.heap_ptr_global_idx));
            }

            Opcode::Unbox => {
                // unbox %dest %src - Dereference Box pointer, read value
                // 1. Get Box pointer from %src
                // 2. Load value from that address
                // 3. Store in %dest

                // Get inner type from Box<T>
                let inner_type = if let Operand::Register(r) = &stmt.operands[1] {
                    if let Some(Type::BmbBox(inner)) = ctx.register_types.get(&r.name) {
                        (**inner).clone()
                    } else {
                        Type::I32 // Fallback
                    }
                } else {
                    Type::I32
                };

                // Get destination register index
                let dest_idx = if let Operand::Register(r) = &stmt.operands[0] {
                    *ctx.locals.get(&r.name).unwrap_or(&0)
                } else {
                    0
                };

                // Load the Box pointer
                self.generate_operand(&stmt.operands[1], func, ctx)?;

                // Load value from [box_ptr]
                match inner_type {
                    Type::I8 => {
                        func.instruction(&Instruction::I32Load8S(wasm_encoder::MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }));
                    }
                    Type::U8 | Type::Bool => {
                        func.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }));
                    }
                    Type::I16 => {
                        func.instruction(&Instruction::I32Load16S(wasm_encoder::MemArg {
                            offset: 0,
                            align: 1,
                            memory_index: 0,
                        }));
                    }
                    Type::U16 => {
                        func.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                            offset: 0,
                            align: 1,
                            memory_index: 0,
                        }));
                    }
                    Type::I32 | Type::U32 | Type::Char | Type::Enum(_) | Type::BmbBox(_) => {
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::I64 | Type::U64 => {
                        func.instruction(&Instruction::I64Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    Type::F32 => {
                        func.instruction(&Instruction::F32Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    Type::F64 => {
                        func.instruction(&Instruction::F64Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    _ => {
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                }

                // Store result in destination
                func.instruction(&Instruction::LocalSet(dest_idx));
            }

            Opcode::Drop => {
                // drop %src - Mark Box as freed
                // With bump allocator, this is a no-op (memory is not actually freed)
                // Future: integrate with GC or region-based memory management
            }
        }

        Ok(())
    }

    /// Calculate the branch depth for a jump to a label
    /// In WASM, br depth 0 means the innermost block/loop
    fn calculate_branch_depth(
        &self,
        target_label: &str,
        current_pos: usize,
        cf: &ControlFlowAnalysis,
    ) -> u32 {
        // Get the list of active loops and blocks at the current position
        let active_loops = cf
            .active_loops_at
            .get(current_pos)
            .cloned()
            .unwrap_or_default();
        let active_blocks = cf
            .active_blocks_at
            .get(current_pos)
            .cloned()
            .unwrap_or_default();

        // Check if this is a forward jump (to a block)
        if let Some(info) = cf.labels.get(target_label) {
            if info.is_block_target && info.position > current_pos {
                // Forward jump: find the block in active_blocks
                // Note: blocks are added to active_blocks at their start position,
                // which is the same as the jump position, so we need to count
                // the block we're about to create

                // Count all enclosing structures from innermost
                // For forward jumps, we need to count from the newly started block
                // The block for this label should be at the top of the stack

                // Since we're at the jump instruction and block is just starting,
                // we need depth 0 to exit the block we just entered
                if let Some(pos) = active_blocks.iter().rposition(|b| b == target_label) {
                    // Found in active blocks, calculate depth from innermost
                    let blocks_after = active_blocks.len() - pos - 1;
                    // Also count any active loops that are nested inside this block
                    return (blocks_after + active_loops.len()) as u32;
                }
                // Block is being created at this position, so depth is 0
                // plus any nested loops
                return active_loops.len() as u32;
            }
        }

        // Backward jump (to a loop): existing logic
        if let Some(pos) = active_loops.iter().position(|l| l == target_label) {
            // The target loop is at position `pos` in the stack
            // Depth is counted from innermost (top of stack), so:
            // depth = (total active loops) - (target position) - 1
            // Plus any active blocks that are nested inside the loop
            let loops_after = active_loops.len() - pos - 1;
            (loops_after + active_blocks.len()) as u32
        } else {
            // Target is not in active loops - check if we're inside any loop
            // and the target is this loop itself (just started)
            if let Some(info) = cf.labels.get(target_label) {
                if info.is_loop_target && info.position <= current_pos {
                    // We're branching to a loop we're currently in
                    active_blocks.len() as u32
                } else {
                    0
                }
            } else {
                0
            }
        }
    }

    fn generate_binary_op(
        &self,
        stmt: &Statement,
        func: &mut Function,
        ctx: &FunctionContext,
        op: BinaryOp,
    ) -> Result<()> {
        // Determine type from destination register (for arithmetic operations)
        let dest_type = if let Operand::Register(r) = &stmt.operands[0] {
            ctx.register_types
                .get(&r.name)
                .cloned()
                .unwrap_or(Type::I32)
        } else {
            Type::I32
        };

        // For comparison operations, we need the operand type (not dest_type which is Bool)
        // Get type from first operand (operands[1])
        let operand_type = match &stmt.operands[1] {
            Operand::Register(r) => ctx
                .register_types
                .get(&r.name)
                .cloned()
                .unwrap_or(Type::I32),
            Operand::IntLiteral(_) => Type::I32,
            Operand::FloatLiteral(_) => Type::F64,
            Operand::Identifier(id) => {
                // Check if it's a parameter
                ctx.register_types
                    .get(&id.name)
                    .cloned()
                    .unwrap_or(Type::I32)
            }
            _ => Type::I32,
        };

        // Load operands
        self.generate_operand(&stmt.operands[1], func, ctx)?;
        self.generate_operand(&stmt.operands[2], func, ctx)?;

        // Apply operation with correct type
        // Note: 8/16/32-bit types all use i32 operations in WASM
        // 64-bit types (i64, u64) use i64 operations
        // For comparisons, use operand_type instead of dest_type (which is Bool)
        let instr = match op {
            BinaryOp::Add => match dest_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Add,
                Type::I64 | Type::U64 => Instruction::I64Add,
                Type::F32 => Instruction::F32Add,
                Type::F64 => Instruction::F64Add,
                _ => Instruction::I32Add, // Compound types use i32 pointer arithmetic
            },
            BinaryOp::Sub => match dest_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Sub,
                Type::I64 | Type::U64 => Instruction::I64Sub,
                Type::F32 => Instruction::F32Sub,
                Type::F64 => Instruction::F64Sub,
                _ => Instruction::I32Sub,
            },
            BinaryOp::Mul => match dest_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Mul,
                Type::I64 | Type::U64 => Instruction::I64Mul,
                Type::F32 => Instruction::F32Mul,
                Type::F64 => Instruction::F64Mul,
                _ => Instruction::I32Mul,
            },
            BinaryOp::Div => match dest_type {
                // Signed division for signed types
                Type::I8 | Type::I16 | Type::I32 => Instruction::I32DivS,
                Type::I64 => Instruction::I64DivS,
                // Unsigned division for unsigned types
                Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32DivU,
                Type::U64 => Instruction::I64DivU,
                Type::F32 => Instruction::F32Div,
                Type::F64 => Instruction::F64Div,
                _ => Instruction::I32DivS,
            },
            BinaryOp::Mod => match dest_type {
                // Signed remainder for signed types
                Type::I8 | Type::I16 | Type::I32 => Instruction::I32RemS,
                Type::I64 => Instruction::I64RemS,
                // Unsigned remainder for unsigned types
                Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32RemU,
                Type::U64 => Instruction::I64RemU,
                // Float mod: a % b = a - (b * floor(a / b))
                // For simplicity, we don't support float mod directly
                Type::F32 | Type::F64 => {
                    return Err(BmbError::CodegenError {
                        message: "Modulo not supported for floating point types".to_string(),
                    })
                }
                _ => Instruction::I32RemS,
            },
            // Bitwise operations (integer only)
            BinaryOp::And => match dest_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32And,
                Type::I64 | Type::U64 => Instruction::I64And,
                Type::F32 | Type::F64 => {
                    return Err(BmbError::CodegenError {
                        message: "Bitwise AND not supported for floating point types".to_string(),
                    })
                }
                _ => Instruction::I32And,
            },
            BinaryOp::Or => match dest_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Or,
                Type::I64 | Type::U64 => Instruction::I64Or,
                Type::F32 | Type::F64 => {
                    return Err(BmbError::CodegenError {
                        message: "Bitwise OR not supported for floating point types".to_string(),
                    })
                }
                _ => Instruction::I32Or,
            },
            BinaryOp::Xor => match dest_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Xor,
                Type::I64 | Type::U64 => Instruction::I64Xor,
                Type::F32 | Type::F64 => {
                    return Err(BmbError::CodegenError {
                        message: "Bitwise XOR not supported for floating point types".to_string(),
                    })
                }
                _ => Instruction::I32Xor,
            },
            BinaryOp::Shl => match dest_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Shl,
                Type::I64 | Type::U64 => Instruction::I64Shl,
                Type::F32 | Type::F64 => {
                    return Err(BmbError::CodegenError {
                        message: "Shift left not supported for floating point types".to_string(),
                    })
                }
                _ => Instruction::I32Shl,
            },
            BinaryOp::Shr => match dest_type {
                // Signed shift for signed types
                Type::I8 | Type::I16 | Type::I32 => Instruction::I32ShrS,
                Type::I64 => Instruction::I64ShrS,
                // Unsigned shift for unsigned types
                Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32ShrU,
                Type::U64 => Instruction::I64ShrU,
                Type::F32 | Type::F64 => {
                    return Err(BmbError::CodegenError {
                        message: "Shift right not supported for floating point types".to_string(),
                    })
                }
                _ => Instruction::I32ShrS,
            },
            // Comparisons return i32 (bool) but instruction selection uses operand_type
            // Note: Eq/Ne are signedness-agnostic, Lt/Le/Gt/Ge need signed/unsigned variants
            BinaryOp::Eq => match operand_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Eq,
                Type::I64 | Type::U64 => Instruction::I64Eq,
                Type::F32 => Instruction::F32Eq,
                Type::F64 => Instruction::F64Eq,
                _ => Instruction::I32Eq,
            },
            BinaryOp::Ne => match operand_type {
                Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32Ne,
                Type::I64 | Type::U64 => Instruction::I64Ne,
                Type::F32 => Instruction::F32Ne,
                Type::F64 => Instruction::F64Ne,
                _ => Instruction::I32Ne,
            },
            BinaryOp::Lt => match operand_type {
                // Signed comparisons for signed types
                Type::I8 | Type::I16 | Type::I32 => Instruction::I32LtS,
                Type::I64 => Instruction::I64LtS,
                // Unsigned comparisons for unsigned types
                Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32LtU,
                Type::U64 => Instruction::I64LtU,
                Type::F32 => Instruction::F32Lt,
                Type::F64 => Instruction::F64Lt,
                _ => Instruction::I32LtS,
            },
            BinaryOp::Le => match operand_type {
                Type::I8 | Type::I16 | Type::I32 => Instruction::I32LeS,
                Type::I64 => Instruction::I64LeS,
                Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32LeU,
                Type::U64 => Instruction::I64LeU,
                Type::F32 => Instruction::F32Le,
                Type::F64 => Instruction::F64Le,
                _ => Instruction::I32LeS,
            },
            BinaryOp::Gt => match operand_type {
                Type::I8 | Type::I16 | Type::I32 => Instruction::I32GtS,
                Type::I64 => Instruction::I64GtS,
                Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32GtU,
                Type::U64 => Instruction::I64GtU,
                Type::F32 => Instruction::F32Gt,
                Type::F64 => Instruction::F64Gt,
                _ => Instruction::I32GtS,
            },
            BinaryOp::Ge => match operand_type {
                Type::I8 | Type::I16 | Type::I32 => Instruction::I32GeS,
                Type::I64 => Instruction::I64GeS,
                Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => Instruction::I32GeU,
                Type::U64 => Instruction::I64GeU,
                Type::F32 => Instruction::F32Ge,
                Type::F64 => Instruction::F64Ge,
                _ => Instruction::I32GeS,
            },
        };

        func.instruction(&instr);

        // Store result
        if let Operand::Register(r) = &stmt.operands[0] {
            if let Some(&idx) = ctx.locals.get(&r.name) {
                func.instruction(&Instruction::LocalSet(idx));
            }
        }

        Ok(())
    }

    /// Generate unary NOT operation: not %r a → ~a
    /// Implemented as XOR with -1 (all bits set)
    fn generate_unary_not(
        &self,
        stmt: &Statement,
        func: &mut Function,
        ctx: &FunctionContext,
    ) -> Result<()> {
        // Determine type from destination register
        let dest_type = if let Operand::Register(r) = &stmt.operands[0] {
            ctx.register_types
                .get(&r.name)
                .cloned()
                .unwrap_or(Type::I32)
        } else {
            Type::I32
        };

        // Load operand
        self.generate_operand(&stmt.operands[1], func, ctx)?;

        // Apply NOT using XOR with -1 (all bits set)
        // 8/16/32-bit types use i32, 64-bit types use i64
        match dest_type {
            Type::I8 | Type::I16 | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool | Type::Char => {
                func.instruction(&Instruction::I32Const(-1));
                func.instruction(&Instruction::I32Xor);
            }
            Type::I64 | Type::U64 => {
                func.instruction(&Instruction::I64Const(-1));
                func.instruction(&Instruction::I64Xor);
            }
            Type::F32 | Type::F64 => {
                return Err(BmbError::CodegenError {
                    message: "Bitwise NOT not supported for floating point types".to_string(),
                });
            }
            _ => {
                func.instruction(&Instruction::I32Const(-1));
                func.instruction(&Instruction::I32Xor);
            }
        }

        // Store result
        if let Operand::Register(r) = &stmt.operands[0] {
            if let Some(&idx) = ctx.locals.get(&r.name) {
                func.instruction(&Instruction::LocalSet(idx));
            }
        }

        Ok(())
    }

    /// Generate WASM code for pattern matching (@match)
    /// Uses a block with if-else chain for arm selection
    fn generate_match(
        &self,
        match_stmt: &crate::ast::MatchStmt,
        func: &mut Function,
        ctx: &FunctionContext,
    ) -> Result<()> {
        // Get scrutinee local index
        let scrutinee_idx = ctx
            .locals
            .get(&match_stmt.scrutinee)
            .ok_or_else(|| BmbError::CodegenError {
                message: format!("Unknown register in match: %{}", match_stmt.scrutinee),
            })?;

        // Create outer block for match (to break out after arm execution)
        func.instruction(&Instruction::Block(BlockType::Empty));

        // Generate each arm
        for arm in &match_stmt.arms {
            // Load scrutinee
            func.instruction(&Instruction::LocalGet(*scrutinee_idx));

            // Generate pattern comparison
            self.generate_pattern_comparison(&arm.pattern, func, ctx)?;

            // If pattern matches, execute body and break
            func.instruction(&Instruction::If(BlockType::Empty));

            // Generate arm body (simplified - just statements, no nested match)
            for instruction in &arm.body {
                match instruction {
                    crate::ast::Instruction::Statement(stmt) => {
                        // Generate statement without control flow analysis
                        // This is simplified - complex control flow in match arms
                        // would need full analysis
                        self.generate_statement_simple(stmt, func, ctx)?;
                    }
                    crate::ast::Instruction::Label(_) => {
                        // Labels in match arms - future support
                    }
                    crate::ast::Instruction::Match(nested) => {
                        // Nested match - recursive call
                        self.generate_match(nested, func, ctx)?;
                    }
                }
            }

            // Break out of match block
            func.instruction(&Instruction::Br(1)); // depth 1 = outer block
            func.instruction(&Instruction::End); // end if
        }

        // Generate default arm if present
        if let Some(default) = &match_stmt.default {
            for instruction in &default.body {
                match instruction {
                    crate::ast::Instruction::Statement(stmt) => {
                        self.generate_statement_simple(stmt, func, ctx)?;
                    }
                    crate::ast::Instruction::Label(_) => {}
                    crate::ast::Instruction::Match(nested) => {
                        self.generate_match(nested, func, ctx)?;
                    }
                }
            }
        }

        // End outer block
        func.instruction(&Instruction::End);

        // Add unreachable after match if all arms return (WASM needs this for type checking)
        // This instruction is polymorphic and satisfies any stack type requirement
        func.instruction(&Instruction::Unreachable);

        Ok(())
    }

    /// Generate pattern comparison code
    /// Leaves 1 on stack if pattern matches, 0 otherwise
    fn generate_pattern_comparison(
        &self,
        pattern: &crate::ast::Pattern,
        func: &mut Function,
        _ctx: &FunctionContext,
    ) -> Result<()> {
        match pattern {
            crate::ast::Pattern::Literal { value, .. } => {
                // Compare scrutinee (already on stack) with literal
                match value {
                    crate::ast::LiteralValue::Int(n) => {
                        func.instruction(&Instruction::I32Const(*n as i32));
                        func.instruction(&Instruction::I32Eq);
                    }
                    crate::ast::LiteralValue::Bool(b) => {
                        func.instruction(&Instruction::I32Const(if *b { 1 } else { 0 }));
                        func.instruction(&Instruction::I32Eq);
                    }
                    crate::ast::LiteralValue::Char(c) => {
                        func.instruction(&Instruction::I32Const(*c as i32));
                        func.instruction(&Instruction::I32Eq);
                    }
                }
            }
            crate::ast::Pattern::Variant {
                enum_name,
                variant_name,
                ..
            } => {
                // For enums, compare discriminant (first word) with variant index
                // Enum representation: discriminant is stored as i32
                // Get variant index from enum definition
                let variant_idx = self
                    .enums
                    .get(&enum_name.name)
                    .and_then(|e| {
                        e.variants
                            .iter()
                            .position(|v| v.name.name == variant_name.name)
                    })
                    .ok_or_else(|| BmbError::CodegenError {
                        message: format!(
                            "Unknown enum variant: {}::{}",
                            enum_name.name, variant_name.name
                        ),
                    })?;

                // For simple enums (no payload), scrutinee IS the discriminant
                // Compare with variant index
                func.instruction(&Instruction::I32Const(variant_idx as i32));
                func.instruction(&Instruction::I32Eq);
            }
        }

        Ok(())
    }

    /// Simplified statement generation for match arm bodies
    /// Doesn't handle complex control flow (jmp/jif with labels)
    fn generate_statement_simple(
        &self,
        stmt: &Statement,
        func: &mut Function,
        ctx: &FunctionContext,
    ) -> Result<()> {
        match stmt.opcode {
            Opcode::Add => self.generate_binary_op(stmt, func, ctx, BinaryOp::Add)?,
            Opcode::Sub => self.generate_binary_op(stmt, func, ctx, BinaryOp::Sub)?,
            Opcode::Mul => self.generate_binary_op(stmt, func, ctx, BinaryOp::Mul)?,
            Opcode::Div => self.generate_binary_op(stmt, func, ctx, BinaryOp::Div)?,
            Opcode::Mod => self.generate_binary_op(stmt, func, ctx, BinaryOp::Mod)?,
            Opcode::And => self.generate_binary_op(stmt, func, ctx, BinaryOp::And)?,
            Opcode::Or => self.generate_binary_op(stmt, func, ctx, BinaryOp::Or)?,
            Opcode::Xor => self.generate_binary_op(stmt, func, ctx, BinaryOp::Xor)?,
            Opcode::Shl => self.generate_binary_op(stmt, func, ctx, BinaryOp::Shl)?,
            Opcode::Shr => self.generate_binary_op(stmt, func, ctx, BinaryOp::Shr)?,
            Opcode::Not => self.generate_unary_not(stmt, func, ctx)?,
            Opcode::Eq => self.generate_binary_op(stmt, func, ctx, BinaryOp::Eq)?,
            Opcode::Ne => self.generate_binary_op(stmt, func, ctx, BinaryOp::Ne)?,
            Opcode::Lt => self.generate_binary_op(stmt, func, ctx, BinaryOp::Lt)?,
            Opcode::Le => self.generate_binary_op(stmt, func, ctx, BinaryOp::Le)?,
            Opcode::Gt => self.generate_binary_op(stmt, func, ctx, BinaryOp::Gt)?,
            Opcode::Ge => self.generate_binary_op(stmt, func, ctx, BinaryOp::Ge)?,
            Opcode::Ret => {
                self.generate_operand(&stmt.operands[0], func, ctx)?;
                func.instruction(&Instruction::Return);
            }
            Opcode::Mov => {
                self.generate_operand(&stmt.operands[1], func, ctx)?;
                if let Operand::Register(r) = &stmt.operands[0] {
                    if let Some(&idx) = ctx.locals.get(&r.name) {
                        func.instruction(&Instruction::LocalSet(idx));
                    }
                }
            }
            Opcode::Call => {
                let func_name = match &stmt.operands[1] {
                    Operand::Identifier(id) => id.name.clone(),
                    Operand::QualifiedIdent { module, name } => {
                        format!("{}::{}", module.name, name.name)
                    }
                    _ => {
                        return Err(BmbError::CodegenError {
                            message: "Call requires function name".to_string(),
                        })
                    }
                };

                for operand in stmt.operands.iter().skip(2) {
                    self.generate_operand(operand, func, ctx)?;
                }

                if let Some(&func_idx) = ctx.function_indices.get(&func_name) {
                    func.instruction(&Instruction::Call(func_idx));
                } else {
                    return Err(BmbError::CodegenError {
                        message: format!("Unknown function: {}", func_name),
                    });
                }

                if let Operand::Register(r) = &stmt.operands[0] {
                    if let Some(&idx) = ctx.locals.get(&r.name) {
                        func.instruction(&Instruction::LocalSet(idx));
                    }
                }
            }
            Opcode::Xcall => {
                let func_name = match &stmt.operands[0] {
                    Operand::Identifier(id) => &id.name,
                    _ => {
                        return Err(BmbError::CodegenError {
                            message: "Xcall requires function name".to_string(),
                        })
                    }
                };

                for operand in stmt.operands.iter().skip(1) {
                    self.generate_operand(operand, func, ctx)?;
                }

                if let Some(&func_idx) = ctx.function_indices.get(func_name) {
                    func.instruction(&Instruction::Call(func_idx));
                } else {
                    return Err(BmbError::CodegenError {
                        message: format!("Unknown function: {}", func_name),
                    });
                }
            }
            Opcode::Jmp | Opcode::Jif => {
                return Err(BmbError::CodegenError {
                    message: "Jump instructions not supported in match arms".to_string(),
                });
            }
            Opcode::Load => {
                // load %dest %ptr - Load value from memory at address in %ptr
                // Simplified version for match arms (no full type inference)
                let dest_idx = if let Operand::Register(r) = &stmt.operands[0] {
                    *ctx.locals.get(&r.name).unwrap_or(&0)
                } else {
                    return Err(BmbError::CodegenError {
                        message: "load: destination must be a register".to_string(),
                    });
                };

                // Load address from ptr register
                self.generate_operand(&stmt.operands[1], func, ctx)?;

                // Default to i32 load in match arms (type inference limited)
                func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: 0,
                    align: 2,
                    memory_index: 0,
                }));

                func.instruction(&Instruction::LocalSet(dest_idx));
            }
            Opcode::Store => {
                // store %ptr %value - Store value at memory address in %ptr
                // Simplified version for match arms

                // Load address
                self.generate_operand(&stmt.operands[0], func, ctx)?;

                // Load value
                self.generate_operand(&stmt.operands[1], func, ctx)?;

                // Default to i32 store in match arms
                func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                    offset: 0,
                    align: 2,
                    memory_index: 0,
                }));
            }
            Opcode::Print => {
                return Err(BmbError::CodegenError {
                    message: "print opcode is not supported in WASM".to_string(),
                });
            }
            Opcode::Box | Opcode::Unbox | Opcode::Drop => {
                // For now, Box operations in match arms are not supported
                // This requires access to heap pointer which is complex in this context
                return Err(BmbError::CodegenError {
                    message: "Box/Unbox/Drop operations not supported in match arms yet".to_string(),
                });
            }
        }

        Ok(())
    }

    fn generate_operand(
        &self,
        operand: &Operand,
        func: &mut Function,
        ctx: &FunctionContext,
    ) -> Result<()> {
        match operand {
            Operand::Register(r) | Operand::Identifier(r) => {
                if let Some(&idx) = ctx.locals.get(&r.name) {
                    func.instruction(&Instruction::LocalGet(idx));
                } else {
                    return Err(BmbError::CodegenError {
                        message: format!("Unknown local: {}", r.name),
                    });
                }
            }
            Operand::IntLiteral(v) => {
                // Determine type from context if needed
                func.instruction(&Instruction::I32Const(*v as i32));
            }
            Operand::FloatLiteral(v) => {
                func.instruction(&Instruction::F64Const(*v));
            }
            Operand::Label(_) => {
                // Labels are not values, they're control flow targets
            }
            Operand::StringLiteral(_) => {
                // String literals are only used with print opcode
                // which is not supported in WASM
            }
            Operand::FieldAccess { base, field } => {
                // Field access requires memory support (future)
                return Err(BmbError::CodegenError {
                    message: format!(
                        "Field access {}.{} requires memory support (Phase A.2)",
                        base.name, field.name
                    ),
                });
            }
            Operand::ArrayAccess { base, index: _ } => {
                // Array access requires memory support (future)
                return Err(BmbError::CodegenError {
                    message: format!(
                        "Array access {}[...] requires memory support (Phase A.1)",
                        base.name
                    ),
                });
            }
            Operand::QualifiedIdent { module, name } => {
                // Qualified identifier: module::function
                // Only valid in call position, not as a value operand
                return Err(BmbError::CodegenError {
                    message: format!(
                        "Qualified identifier {}::{} can only be used in call position",
                        module.name, name.name
                    ),
                });
            }
        }

        Ok(())
    }

    fn finish(mut self) -> Vec<u8> {
        self.module.section(&self.types);
        // Import section must come before function section
        if self.imports.len() > 0 {
            self.module.section(&self.imports);
        }
        self.module.section(&self.functions);

        // Memory section (if needed for structs/arrays/heap)
        if self.needs_memory || self.needs_heap {
            // One page of memory (64KB) - can grow as needed
            self.memory.memory(MemoryType {
                minimum: 1,
                maximum: Some(256), // Max 16MB
                memory64: false,
                shared: false,
                page_size_log2: None,
            });
            self.module.section(&self.memory);
            // Export memory for host access
            self.exports.export("memory", ExportKind::Memory, 0);
        }

        // Global section (if heap allocation is needed)
        if self.needs_heap {
            // Add heap pointer global: mutable i32, initialized to 1024
            // (leave first 1KB for struct static data)
            self.globals.global(
                GlobalType {
                    val_type: ValType::I32,
                    mutable: true,
                    shared: false,
                },
                &ConstExpr::i32_const(1024), // Start heap at 1KB offset
            );
            self.module.section(&self.globals);
        }

        self.module.section(&self.exports);
        self.module.section(&self.code);
        self.module.finish()
    }
}

/// Function context for code generation
#[allow(dead_code)]
struct FunctionContext<'a> {
    locals: &'a HashMap<String, u32>,
    register_types: &'a HashMap<String, Type>,
    param_types: HashMap<String, Type>,
    return_type: Type,
    function_indices: &'a HashMap<String, u32>,
    /// Postcondition expressions to check before return (multiple allowed)
    postconditions: Vec<crate::ast::Expr>,
    /// Combined type map for contract checking
    all_types: HashMap<String, Type>,
    /// Local index for storing result during postcondition check
    result_local: Option<u32>,
    /// Loop invariants indexed by label name
    invariants: &'a [Invariant],
}

impl<'a> FunctionContext<'a> {
    /// Get type of a variable (parameter or register)
    #[allow(dead_code)]
    fn get_type(&self, name: &str) -> Option<&Type> {
        self.param_types
            .get(name)
            .or_else(|| self.register_types.get(name))
    }
}

/// Binary operation types
#[derive(Clone, Copy)]
enum BinaryOp {
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

/// Label information for control flow
struct LabelInfo {
    /// Position of the label in the instruction list
    position: usize,
    /// Whether this label is a loop target (has backward jumps to it)
    is_loop_target: bool,
    /// Position of the last backward jump to this label (where loop ends)
    loop_end_position: Option<usize>,
    /// Whether this label is a block target (has forward jumps to it)
    is_block_target: bool,
    /// Position of the first forward jump to this label (where block starts)
    block_start_position: Option<usize>,
    /// Nesting depth (for calculating br depth)
    depth: u32,
}

/// Analyzed control flow structure
struct ControlFlowAnalysis {
    labels: HashMap<String, LabelInfo>,
    /// Active loop stack at each position (for depth calculation)
    active_loops_at: Vec<Vec<String>>,
    /// Active block stack at each position (for forward jump depth calculation)
    active_blocks_at: Vec<Vec<String>>,
}

/// Analyze control flow to determine label block structure
fn analyze_control_flow(body: &[ast::Instruction]) -> ControlFlowAnalysis {
    let mut label_positions: HashMap<String, usize> = HashMap::new();
    let mut jump_targets: Vec<(usize, String, bool)> = Vec::new(); // (pos, label, is_jmp_not_jif)

    // First pass: collect labels and jumps
    for (pos, instr) in body.iter().enumerate() {
        match instr {
            ast::Instruction::Label(id) => {
                label_positions.insert(id.name.clone(), pos);
            }
            ast::Instruction::Statement(stmt) => {
                if matches!(stmt.opcode, Opcode::Jmp | Opcode::Jif) {
                    if let Some(Operand::Label(label_id)) = stmt.operands.last() {
                        let is_jmp = matches!(stmt.opcode, Opcode::Jmp);
                        jump_targets.push((pos, label_id.name.clone(), is_jmp));
                    }
                }
            }
            ast::Instruction::Match(_) => {
                // Pattern matching doesn't affect control flow analysis for now
            }
        }
    }

    // Second pass: determine loop/block targets and their boundaries
    let mut labels: HashMap<String, LabelInfo> = HashMap::new();

    for (label_name, label_pos) in &label_positions {
        // Find all backward jumps to this label (for loops)
        let backward_jumps: Vec<_> = jump_targets
            .iter()
            .filter(|(jump_pos, target, _)| target == label_name && *jump_pos > *label_pos)
            .collect();

        // Find all forward jumps to this label (for blocks)
        let forward_jumps: Vec<_> = jump_targets
            .iter()
            .filter(|(jump_pos, target, _)| target == label_name && *jump_pos < *label_pos)
            .collect();

        let is_loop = !backward_jumps.is_empty();
        let loop_end = backward_jumps.iter().map(|(pos, _, _)| *pos).max();

        let is_block = !forward_jumps.is_empty();
        let block_start = forward_jumps.iter().map(|(pos, _, _)| *pos).min();

        labels.insert(
            label_name.clone(),
            LabelInfo {
                position: *label_pos,
                is_loop_target: is_loop,
                loop_end_position: loop_end,
                is_block_target: is_block,
                block_start_position: block_start,
                depth: 0, // Will be calculated in third pass
            },
        );
    }

    // Third pass: calculate nesting depth at each position
    // Track which loops and blocks are active at each instruction position
    let mut active_loops_at: Vec<Vec<String>> = vec![Vec::new(); body.len()];
    let mut active_blocks_at: Vec<Vec<String>> = vec![Vec::new(); body.len()];
    let mut current_loops: Vec<String> = Vec::new();
    let mut current_blocks: Vec<String> = Vec::new();

    for (pos, instr) in body.iter().enumerate() {
        // Check if any loops end at this position
        let loops_ending: Vec<String> = labels
            .iter()
            .filter(|(_, info)| info.loop_end_position == Some(pos))
            .map(|(name, _)| name.clone())
            .collect();

        // Check if any blocks start at this position (forward jump origin)
        let blocks_starting: Vec<String> = labels
            .iter()
            .filter(|(_, info)| info.block_start_position == Some(pos))
            .map(|(name, _)| name.clone())
            .collect();

        // First, record active loops/blocks at this position (before any changes)
        active_loops_at[pos] = current_loops.clone();
        active_blocks_at[pos] = current_blocks.clone();

        // Handle block starts (at the forward jump instruction)
        for block_name in blocks_starting {
            current_blocks.push(block_name);
        }

        // Handle loop starts
        if let ast::Instruction::Label(id) = instr {
            if let Some(info) = labels.get(&id.name) {
                if info.is_loop_target {
                    current_loops.push(id.name.clone());
                }
                // Block ends at the label (the target)
                if info.is_block_target {
                    if let Some(idx) = current_blocks.iter().position(|b| b == &id.name) {
                        current_blocks.remove(idx);
                    }
                }
            }
        }

        // Handle loop ends (remove from stack after the ending instruction)
        for ended in loops_ending {
            if let Some(idx) = current_loops.iter().position(|l| l == &ended) {
                current_loops.remove(idx);
            }
        }
    }

    // Fourth pass: set depth for each label based on nesting
    for (_label_name, info) in labels.iter_mut() {
        if info.is_loop_target {
            if let Some(active) = active_loops_at.get(info.position) {
                info.depth = active.len() as u32;
            }
        }
    }

    ControlFlowAnalysis {
        labels,
        active_loops_at,
        active_blocks_at,
    }
}

fn type_to_valtype(ty: &Type) -> ValType {
    match ty {
        // 8-bit, 16-bit, and 32-bit integers map to WASM i32
        Type::I8 | Type::I16 | Type::I32 => ValType::I32,
        Type::U8 | Type::U16 | Type::U32 => ValType::I32,
        Type::Bool | Type::Char => ValType::I32,
        // 64-bit integers map to WASM i64
        Type::I64 | Type::U64 => ValType::I64,
        // Floats
        Type::F32 => ValType::F32,
        Type::F64 => ValType::F64,
        // Compound types - map to i32 (pointer/index) for now
        Type::Void => ValType::I32,
        Type::Array { .. } => ValType::I32, // Array base pointer
        Type::Struct(_) => ValType::I32,    // Struct base pointer
        Type::Enum(_) => ValType::I32,      // Enum discriminant
        Type::Ref(_) => ValType::I32,       // Reference pointer
        Type::Ptr(_) => ValType::I32,       // Raw pointer
        Type::Refined { .. } => ValType::I32, // Refined type (resolved to base type at check time)
        // Generic built-in types - represented as i32 pointers in WASM32
        Type::Option(_) => ValType::I32,    // Option tag+value (stack allocated for small types)
        Type::Result { .. } => ValType::I32, // Result tag+value (stack allocated for small types)
        Type::Vector(_) => ValType::I32,    // Vector pointer to heap
        Type::Slice(_) => ValType::I32,
        // String types (v0.9+) - represented as i32 pointers in WASM
        Type::BmbString | Type::BmbStr => ValType::I32,     // Slice pointer (fat pointer, but simplified for now)
        // Box type (v0.13+) - heap-allocated pointer
        Type::BmbBox(_) => ValType::I32,    // Box pointer to heap
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        Identifier, Instruction as AstInstruction, Node, Opcode, Operand, ParamAnnotation,
        Parameter, Span, Statement, Type,
    };
    use crate::contracts::VerifiedProgram;
    use crate::types::{TypedNode, TypedProgram};

    fn make_typed_node(
        name: &str,
        params: Vec<Parameter>,
        returns: Type,
        body: Vec<AstInstruction>,
        register_types: HashMap<String, Type>,
    ) -> TypedNode {
        TypedNode {
            node: Node {
                is_public: false,
                name: Identifier::new(name, Span::default()),
                tags: vec![],
                params,
                returns,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body,
                span: Span::default(),
            },
            register_types,
        }
    }

    fn make_param(name: &str, ty: Type) -> Parameter {
        Parameter {
            name: Identifier::new(name, Span::default()),
            ty,
            annotation: ParamAnnotation::None,
            span: Span::default(),
        }
    }

    #[test]
    fn test_type_to_valtype() {
        // Signed integers: 8/16/32-bit → i32, 64-bit → i64
        assert_eq!(type_to_valtype(&Type::I8), ValType::I32);
        assert_eq!(type_to_valtype(&Type::I16), ValType::I32);
        assert_eq!(type_to_valtype(&Type::I32), ValType::I32);
        assert_eq!(type_to_valtype(&Type::I64), ValType::I64);

        // Unsigned integers: 8/16/32-bit → i32, 64-bit → i64
        assert_eq!(type_to_valtype(&Type::U8), ValType::I32);
        assert_eq!(type_to_valtype(&Type::U16), ValType::I32);
        assert_eq!(type_to_valtype(&Type::U32), ValType::I32);
        assert_eq!(type_to_valtype(&Type::U64), ValType::I64);

        // Other primitives → i32
        assert_eq!(type_to_valtype(&Type::Bool), ValType::I32);
        assert_eq!(type_to_valtype(&Type::Char), ValType::I32);

        // Floats
        assert_eq!(type_to_valtype(&Type::F32), ValType::F32);
        assert_eq!(type_to_valtype(&Type::F64), ValType::F64);

        // Pointers → i32 (WASM32)
        assert_eq!(type_to_valtype(&Type::Ptr(Box::new(Type::I32))), ValType::I32);
        assert_eq!(type_to_valtype(&Type::Ref(Box::new(Type::I32))), ValType::I32);
    }

    #[test]
    fn test_generate_simple_add() {
        // @node sum
        // @params a:i32 b:i32
        // @returns i32
        //   add %r a b
        //   ret %r

        let mut register_types = HashMap::new();
        register_types.insert("r".to_string(), Type::I32);

        let node = make_typed_node(
            "sum",
            vec![make_param("a", Type::I32), make_param("b", Type::I32)],
            Type::I32,
            vec![
                AstInstruction::Statement(Statement {
                    opcode: Opcode::Add,
                    operands: vec![
                        Operand::Register(Identifier::new("r", Span::default())),
                        Operand::Identifier(Identifier::new("a", Span::default())),
                        Operand::Identifier(Identifier::new("b", Span::default())),
                    ],
                    span: Span::default(),
                }),
                AstInstruction::Statement(Statement {
                    opcode: Opcode::Ret,
                    operands: vec![Operand::Register(Identifier::new("r", Span::default()))],
                    span: Span::default(),
                }),
            ],
            register_types,
        );

        let program = TypedProgram {
            imports: vec![],
            extern_defs: vec![],
            structs: vec![],
            enums: vec![],
            type_defs: vec![],
            contracts: vec![],
            nodes: vec![node],
            registry: crate::types::TypeRegistry::new(),
        };
        let verified = VerifiedProgram { program };

        let wasm = generate(&verified).expect("codegen should succeed");

        // Verify it's valid WebAssembly (starts with magic bytes)
        assert_eq!(&wasm[0..4], b"\0asm");
        assert_eq!(&wasm[4..8], &[1, 0, 0, 0]); // version 1
    }

    #[test]
    fn test_generate_f64_division() {
        // @node divide
        // @params a:f64 b:f64
        // @returns f64
        //   div %r a b
        //   ret %r

        let mut register_types = HashMap::new();
        register_types.insert("r".to_string(), Type::F64);

        let node = make_typed_node(
            "divide",
            vec![make_param("a", Type::F64), make_param("b", Type::F64)],
            Type::F64,
            vec![
                AstInstruction::Statement(Statement {
                    opcode: Opcode::Div,
                    operands: vec![
                        Operand::Register(Identifier::new("r", Span::default())),
                        Operand::Identifier(Identifier::new("a", Span::default())),
                        Operand::Identifier(Identifier::new("b", Span::default())),
                    ],
                    span: Span::default(),
                }),
                AstInstruction::Statement(Statement {
                    opcode: Opcode::Ret,
                    operands: vec![Operand::Register(Identifier::new("r", Span::default()))],
                    span: Span::default(),
                }),
            ],
            register_types,
        );

        let program = TypedProgram {
            imports: vec![],
            extern_defs: vec![],
            structs: vec![],
            enums: vec![],
            type_defs: vec![],
            contracts: vec![],
            nodes: vec![node],
            registry: crate::types::TypeRegistry::new(),
        };
        let verified = VerifiedProgram { program };

        let wasm = generate(&verified).expect("codegen should succeed");
        assert_eq!(&wasm[0..4], b"\0asm");
    }

    #[test]
    fn test_generate_mov() {
        // @node identity
        // @params x:i32
        // @returns i32
        //   mov %r x
        //   ret %r

        let mut register_types = HashMap::new();
        register_types.insert("r".to_string(), Type::I32);

        let node = make_typed_node(
            "identity",
            vec![make_param("x", Type::I32)],
            Type::I32,
            vec![
                AstInstruction::Statement(Statement {
                    opcode: Opcode::Mov,
                    operands: vec![
                        Operand::Register(Identifier::new("r", Span::default())),
                        Operand::Identifier(Identifier::new("x", Span::default())),
                    ],
                    span: Span::default(),
                }),
                AstInstruction::Statement(Statement {
                    opcode: Opcode::Ret,
                    operands: vec![Operand::Register(Identifier::new("r", Span::default()))],
                    span: Span::default(),
                }),
            ],
            register_types,
        );

        let program = TypedProgram {
            imports: vec![],
            extern_defs: vec![],
            structs: vec![],
            enums: vec![],
            type_defs: vec![],
            contracts: vec![],
            nodes: vec![node],
            registry: crate::types::TypeRegistry::new(),
        };
        let verified = VerifiedProgram { program };

        let wasm = generate(&verified).expect("codegen should succeed");
        assert_eq!(&wasm[0..4], b"\0asm");
    }

    #[test]
    fn test_analyze_control_flow() {
        // _loop:
        //   ...
        //   jmp _loop   <- backward jump, so _loop is a loop target

        let body = vec![
            AstInstruction::Label(Identifier::new("_loop", Span::default())),
            AstInstruction::Statement(Statement {
                opcode: Opcode::Jmp,
                operands: vec![Operand::Label(Identifier::new("_loop", Span::default()))],
                span: Span::default(),
            }),
        ];

        let cf = analyze_control_flow(&body);
        assert!(cf
            .labels
            .get("_loop")
            .map(|l| l.is_loop_target)
            .unwrap_or(false));
        // Loop should end at position 1 (the jmp instruction)
        assert_eq!(
            cf.labels.get("_loop").map(|l| l.loop_end_position),
            Some(Some(1))
        );
    }

    #[test]
    fn test_struct_layout_simple() {
        // Struct with two i32 fields
        let fields = vec![
            ("x".to_string(), Type::I32),
            ("y".to_string(), Type::I32),
        ];
        let layout = StructLayout::calculate(&fields);

        assert_eq!(layout.size, 8); // 4 + 4 = 8 bytes
        assert_eq!(layout.alignment, 4);
        assert_eq!(layout.fields.get("x").map(|f| f.offset), Some(0));
        assert_eq!(layout.fields.get("y").map(|f| f.offset), Some(4));
    }

    #[test]
    fn test_struct_layout_mixed_types() {
        // Struct with mixed types: i32, i64, i32
        // Should align i64 on 8-byte boundary
        let fields = vec![
            ("a".to_string(), Type::I32), // 0..4
            ("b".to_string(), Type::I64), // 8..16 (aligned to 8)
            ("c".to_string(), Type::I32), // 16..20
        ];
        let layout = StructLayout::calculate(&fields);

        assert_eq!(layout.alignment, 8); // Alignment from i64
        assert_eq!(layout.fields.get("a").map(|f| f.offset), Some(0));
        assert_eq!(layout.fields.get("b").map(|f| f.offset), Some(8));
        assert_eq!(layout.fields.get("c").map(|f| f.offset), Some(16));
        assert_eq!(layout.size, 24); // Padded to 8-byte alignment
    }

    #[test]
    fn test_struct_layout_with_array() {
        // Struct with array field
        let fields = vec![
            ("count".to_string(), Type::I32),
            (
                "data".to_string(),
                Type::Array {
                    element: Box::new(Type::I32),
                    size: 4,
                },
            ),
        ];
        let layout = StructLayout::calculate(&fields);

        assert_eq!(layout.fields.get("count").map(|f| f.offset), Some(0));
        assert_eq!(layout.fields.get("data").map(|f| f.offset), Some(4));
        assert_eq!(layout.fields.get("data").map(|f| f.size), Some(16)); // 4 * 4 = 16
        assert_eq!(layout.size, 20); // 4 + 16 = 20
    }

    #[test]
    fn test_type_size_align() {
        // 8-bit types
        assert_eq!(type_size_align(&Type::I8), (1, 1));
        assert_eq!(type_size_align(&Type::U8), (1, 1));

        // 16-bit types
        assert_eq!(type_size_align(&Type::I16), (2, 2));
        assert_eq!(type_size_align(&Type::U16), (2, 2));

        // 32-bit types
        assert_eq!(type_size_align(&Type::I32), (4, 4));
        assert_eq!(type_size_align(&Type::U32), (4, 4));
        assert_eq!(type_size_align(&Type::F32), (4, 4));
        assert_eq!(type_size_align(&Type::Char), (4, 4));
        assert_eq!(type_size_align(&Type::Bool), (4, 4)); // Bool is i32 in WASM

        // 64-bit types
        assert_eq!(type_size_align(&Type::I64), (8, 8));
        assert_eq!(type_size_align(&Type::U64), (8, 8));
        assert_eq!(type_size_align(&Type::F64), (8, 8));

        // Void
        assert_eq!(type_size_align(&Type::Void), (0, 1));

        // Array
        let array_type = Type::Array {
            element: Box::new(Type::I32),
            size: 10,
        };
        assert_eq!(type_size_align(&array_type), (40, 4)); // 10 * 4 = 40 bytes

        // Pointers (32-bit in WASM32)
        assert_eq!(type_size_align(&Type::Ref(Box::new(Type::I32))), (4, 4));
        assert_eq!(type_size_align(&Type::Ptr(Box::new(Type::I64))), (4, 4));
    }
}
