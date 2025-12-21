//! BMB Code Generator
//!
//! Generates WebAssembly from type-checked BMB AST.
//!
//! "Omission is guessing, and guessing is error."
//! - Every type decision is explicit based on TypedNode analysis

use std::collections::HashMap;

use wasm_encoder::{
    BlockType, CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction,
    Module, TypeSection, ValType,
};

use crate::ast::{self, Node, Opcode, Operand, Statement, Type};
use crate::contracts::{ContractCodeGenerator, VerifiedProgram};
use crate::types::TypedNode;
use crate::{BmbError, Result};

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
    functions: FunctionSection,
    exports: ExportSection,
    code: CodeSection,
    function_indices: HashMap<String, u32>,
    next_func_idx: u32,
}

impl CodeGenerator {
    fn new() -> Self {
        Self {
            module: Module::new(),
            types: TypeSection::new(),
            functions: FunctionSection::new(),
            exports: ExportSection::new(),
            code: CodeSection::new(),
            function_indices: HashMap::new(),
            next_func_idx: 0,
        }
    }

    fn generate_program(&mut self, program: &crate::types::TypedProgram) -> Result<()> {
        // First pass: register all function types
        for typed_node in &program.nodes {
            let node = &typed_node.node;
            let type_idx = self.register_function_type(node)?;
            self.function_indices
                .insert(node.name.name.clone(), self.next_func_idx);
            self.functions.function(type_idx);
            self.exports
                .export(&node.name.name, ExportKind::Func, self.next_func_idx);
            self.next_func_idx += 1;
        }

        // Second pass: generate function bodies
        for typed_node in &program.nodes {
            self.generate_function(typed_node)?;
        }

        Ok(())
    }

    fn register_function_type(&mut self, node: &Node) -> Result<u32> {
        let params: Vec<ValType> = node.params.iter().map(|p| type_to_valtype(&p.ty)).collect();
        let results = vec![type_to_valtype(&node.returns)];

        let type_idx = self.types.len();
        self.types.ty().function(params, results);
        Ok(type_idx)
    }

    fn generate_function(&mut self, typed_node: &TypedNode) -> Result<()> {
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

        // Add a result local for postcondition checking if needed
        let result_local = if node.postcondition.is_some() {
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

        // Generate precondition check at function entry
        if let Some(ref pre) = node.precondition {
            let contract_gen =
                ContractCodeGenerator::new(&locals, &all_types, node.returns.clone());
            contract_gen.generate_precondition(pre, &mut func);
        }

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
            postcondition: node.postcondition.clone(),
            all_types: all_types.clone(),
            result_local,
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
        // Track which loops need to be closed
        let mut open_loops: Vec<String> = Vec::new();

        for (pos, instruction) in body.iter().enumerate() {
            match instruction {
                ast::Instruction::Label(id) => {
                    // Labels in BMB are targets for jumps
                    // In Wasm, we use block/loop structure
                    if let Some(info) = cf.labels.get(&id.name) {
                        if info.is_loop_target {
                            // Start of a loop
                            func.instruction(&Instruction::Loop(BlockType::Empty));
                            open_loops.push(id.name.clone());
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
            }
        }

        // Close any remaining open loops (shouldn't happen in well-formed code)
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
            Opcode::Eq => self.generate_binary_op(stmt, func, ctx, BinaryOp::Eq)?,
            Opcode::Ne => self.generate_binary_op(stmt, func, ctx, BinaryOp::Ne)?,
            Opcode::Lt => self.generate_binary_op(stmt, func, ctx, BinaryOp::Lt)?,
            Opcode::Le => self.generate_binary_op(stmt, func, ctx, BinaryOp::Le)?,
            Opcode::Gt => self.generate_binary_op(stmt, func, ctx, BinaryOp::Gt)?,
            Opcode::Ge => self.generate_binary_op(stmt, func, ctx, BinaryOp::Ge)?,

            Opcode::Ret => {
                // Load return value
                self.generate_operand(&stmt.operands[0], func, ctx)?;

                // If there's a postcondition, check it before returning
                if let (Some(ref post), Some(result_local)) = (&ctx.postcondition, ctx.result_local)
                {
                    // Store result to check postcondition
                    func.instruction(&Instruction::LocalSet(result_local));

                    // Generate postcondition check
                    let mut contract_gen = ContractCodeGenerator::new(
                        ctx.locals,
                        &ctx.all_types,
                        ctx.return_type.clone(),
                    );
                    contract_gen.set_result_local(result_local);
                    contract_gen.generate_postcondition(post, func);

                    // Load result for return
                    func.instruction(&Instruction::LocalGet(result_local));
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
                // First operand is result register, second is function name
                let func_name = match &stmt.operands[1] {
                    Operand::Identifier(id) => &id.name,
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
                if let Some(&func_idx) = ctx.function_indices.get(func_name) {
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

            Opcode::Mov => {
                // mov dest src
                self.generate_operand(&stmt.operands[1], func, ctx)?;
                if let Operand::Register(r) = &stmt.operands[0] {
                    if let Some(&idx) = ctx.locals.get(&r.name) {
                        func.instruction(&Instruction::LocalSet(idx));
                    }
                }
            }

            Opcode::Load | Opcode::Store => {
                // Memory operations - future expansion for linear memory
                // For now, treat as no-op (BMB uses registers, not heap memory)
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
        // Get the list of active loops at the current position
        let active_loops = cf
            .active_loops_at
            .get(current_pos)
            .cloned()
            .unwrap_or_default();

        // If the target is in the active loops, find its position in the stack
        // The depth is how many loops are nested inside it (from innermost)
        if let Some(pos) = active_loops.iter().position(|l| l == target_label) {
            // The target loop is at position `pos` in the stack
            // Depth is counted from innermost (top of stack), so:
            // depth = (total active loops) - (target position) - 1
            (active_loops.len() - pos - 1) as u32
        } else {
            // Target is not in active loops - check if we're inside any loop
            // and the target is this loop itself (just started)
            if let Some(info) = cf.labels.get(target_label) {
                if info.is_loop_target && info.position <= current_pos {
                    // We're branching to a loop we're currently in
                    // Find how deep we are
                    0 // Default: innermost
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
        // Determine type from destination register
        let dest_type = if let Operand::Register(r) = &stmt.operands[0] {
            ctx.register_types
                .get(&r.name)
                .cloned()
                .unwrap_or(Type::I32)
        } else {
            Type::I32
        };

        // Load operands
        self.generate_operand(&stmt.operands[1], func, ctx)?;
        self.generate_operand(&stmt.operands[2], func, ctx)?;

        // Apply operation with correct type
        let instr = match op {
            BinaryOp::Add => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32Add,
                Type::I64 => Instruction::I64Add,
                Type::F32 => Instruction::F32Add,
                Type::F64 => Instruction::F64Add,
            },
            BinaryOp::Sub => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32Sub,
                Type::I64 => Instruction::I64Sub,
                Type::F32 => Instruction::F32Sub,
                Type::F64 => Instruction::F64Sub,
            },
            BinaryOp::Mul => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32Mul,
                Type::I64 => Instruction::I64Mul,
                Type::F32 => Instruction::F32Mul,
                Type::F64 => Instruction::F64Mul,
            },
            BinaryOp::Div => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32DivS,
                Type::I64 => Instruction::I64DivS,
                Type::F32 => Instruction::F32Div,
                Type::F64 => Instruction::F64Div,
            },
            BinaryOp::Mod => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32RemS,
                Type::I64 => Instruction::I64RemS,
                // Float mod: a % b = a - (b * floor(a / b))
                // For simplicity, we don't support float mod directly
                Type::F32 | Type::F64 => {
                    return Err(BmbError::CodegenError {
                        message: "Modulo not supported for floating point types".to_string(),
                    })
                }
            },
            // Comparisons return i32 (bool)
            BinaryOp::Eq => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32Eq,
                Type::I64 => Instruction::I64Eq,
                Type::F32 => Instruction::F32Eq,
                Type::F64 => Instruction::F64Eq,
            },
            BinaryOp::Ne => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32Ne,
                Type::I64 => Instruction::I64Ne,
                Type::F32 => Instruction::F32Ne,
                Type::F64 => Instruction::F64Ne,
            },
            BinaryOp::Lt => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32LtS,
                Type::I64 => Instruction::I64LtS,
                Type::F32 => Instruction::F32Lt,
                Type::F64 => Instruction::F64Lt,
            },
            BinaryOp::Le => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32LeS,
                Type::I64 => Instruction::I64LeS,
                Type::F32 => Instruction::F32Le,
                Type::F64 => Instruction::F64Le,
            },
            BinaryOp::Gt => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32GtS,
                Type::I64 => Instruction::I64GtS,
                Type::F32 => Instruction::F32Gt,
                Type::F64 => Instruction::F64Gt,
            },
            BinaryOp::Ge => match dest_type {
                Type::I32 | Type::Bool => Instruction::I32GeS,
                Type::I64 => Instruction::I64GeS,
                Type::F32 => Instruction::F32Ge,
                Type::F64 => Instruction::F64Ge,
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
        }

        Ok(())
    }

    fn finish(mut self) -> Vec<u8> {
        self.module.section(&self.types);
        self.module.section(&self.functions);
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
    /// Postcondition expression to check before return
    postcondition: Option<crate::ast::Expr>,
    /// Combined type map for contract checking
    all_types: HashMap<String, Type>,
    /// Local index for storing result during postcondition check
    result_local: Option<u32>,
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
    /// Nesting depth (for calculating br depth)
    depth: u32,
}

/// Analyzed control flow structure
struct ControlFlowAnalysis {
    labels: HashMap<String, LabelInfo>,
    /// Active loop stack at each position (for depth calculation)
    active_loops_at: Vec<Vec<String>>,
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
        }
    }

    // Second pass: determine loop targets and their boundaries
    let mut labels: HashMap<String, LabelInfo> = HashMap::new();

    for (label_name, label_pos) in &label_positions {
        // Find all backward jumps to this label
        let backward_jumps: Vec<_> = jump_targets
            .iter()
            .filter(|(jump_pos, target, _)| target == label_name && *jump_pos > *label_pos)
            .collect();

        let is_loop = !backward_jumps.is_empty();
        let loop_end = backward_jumps.iter().map(|(pos, _, _)| *pos).max();

        labels.insert(
            label_name.clone(),
            LabelInfo {
                position: *label_pos,
                is_loop_target: is_loop,
                loop_end_position: loop_end,
                depth: 0, // Will be calculated in third pass
            },
        );
    }

    // Third pass: calculate nesting depth at each position
    // Track which loops are active at each instruction position
    let mut active_loops_at: Vec<Vec<String>> = vec![Vec::new(); body.len()];
    let mut current_loops: Vec<String> = Vec::new();

    for (pos, instr) in body.iter().enumerate() {
        // Check if any loops end at this position
        let loops_ending: Vec<String> = labels
            .iter()
            .filter(|(_, info)| info.loop_end_position == Some(pos))
            .map(|(name, _)| name.clone())
            .collect();

        // First, record active loops at this position (before any changes)
        active_loops_at[pos] = current_loops.clone();

        // Handle loop starts
        if let ast::Instruction::Label(id) = instr {
            if let Some(info) = labels.get(&id.name) {
                if info.is_loop_target {
                    current_loops.push(id.name.clone());
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
            // Depth when inside the loop is the number of enclosing loops
            // For br inside a loop, depth 0 = the innermost loop
            if let Some(active) = active_loops_at.get(info.position) {
                // Count loops that are active when this loop starts
                info.depth = active.len() as u32;
            }
        }
    }

    ControlFlowAnalysis {
        labels,
        active_loops_at,
    }
}

fn type_to_valtype(ty: &Type) -> ValType {
    match ty {
        Type::I32 | Type::Bool => ValType::I32,
        Type::I64 => ValType::I64,
        Type::F32 => ValType::F32,
        Type::F64 => ValType::F64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        Identifier, Instruction as AstInstruction, Node, Opcode, Operand, Parameter, Span,
        Statement, Type,
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
                name: Identifier::new(name, Span::default()),
                params,
                returns,
                precondition: None,
                postcondition: None,
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
            span: Span::default(),
        }
    }

    #[test]
    fn test_type_to_valtype() {
        assert_eq!(type_to_valtype(&Type::I32), ValType::I32);
        assert_eq!(type_to_valtype(&Type::Bool), ValType::I32);
        assert_eq!(type_to_valtype(&Type::I64), ValType::I64);
        assert_eq!(type_to_valtype(&Type::F32), ValType::F32);
        assert_eq!(type_to_valtype(&Type::F64), ValType::F64);
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

        let program = TypedProgram { nodes: vec![node] };
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

        let program = TypedProgram { nodes: vec![node] };
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

        let program = TypedProgram { nodes: vec![node] };
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
}
