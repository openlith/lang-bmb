//! ARM64 Code Generation
//!
//! Translates BMB typed AST to ARM64 machine code.

use crate::ast::{Instruction, Node, Opcode, Operand, Statement};
use crate::types::TypedProgram;
use crate::BmbError;
use std::collections::HashMap;

use super::encoding::{self, Condition};
use super::registers::Reg64;

/// ARM64 Code Generator
pub struct Arm64Codegen {
    /// Generated machine code
    code: Vec<u8>,
    /// Register allocation: BMB register name -> ARM64 register
    reg_alloc: HashMap<String, Reg64>,
    /// Next available register for allocation
    next_reg: u8,
    /// Label positions for forward references
    labels: HashMap<String, usize>,
    /// Pending forward jumps: (patch_offset, label_name)
    pending_jumps: Vec<(usize, String)>,
    /// Function entry points
    functions: HashMap<String, usize>,
}

impl Arm64Codegen {
    pub fn new() -> Self {
        Self {
            code: Vec::new(),
            reg_alloc: HashMap::new(),
            next_reg: 9, // Start from X9 (caller-saved, not argument)
            labels: HashMap::new(),
            pending_jumps: Vec::new(),
            functions: HashMap::new(),
        }
    }

    /// Compile a typed program to ARM64 machine code
    pub fn compile(&mut self, program: &TypedProgram) -> Result<Vec<u8>, BmbError> {
        // Generate code for each function
        for typed_node in &program.nodes {
            self.functions
                .insert(typed_node.node.name.name.clone(), self.code.len());
            self.compile_function(&typed_node.node)?;
        }

        // Patch forward jumps
        self.patch_jumps()?;

        Ok(self.code.clone())
    }

    /// Compile a function for a standalone Linux executable
    pub fn compile_executable(&mut self, program: &TypedProgram) -> Result<Vec<u8>, BmbError> {
        // Find main function
        let main_typed_node = program
            .nodes
            .iter()
            .find(|n| n.node.name.name == "main")
            .ok_or_else(|| BmbError::CodegenError {
                message: "No 'main' function found".to_string(),
            })?;

        // For Linux: just compile the main function body
        // The result in X0 will be the exit code
        self.functions.insert("main".to_string(), self.code.len());
        self.compile_function(&main_typed_node.node)?;

        // Epilogue: syscall exit
        // The return value should be in X0 (handled by compile_function)

        // mov x8, #93 (exit syscall number on Linux ARM64)
        encoding::load_imm64(&mut self.code, Reg64::X8, 93);

        // svc #0
        encoding::svc(&mut self.code, 0);

        self.patch_jumps()?;

        Ok(self.code.clone())
    }

    /// Compile a single function
    fn compile_function(&mut self, node: &Node) -> Result<(), BmbError> {
        // Reset register allocation for this function
        self.reg_alloc.clear();
        self.next_reg = 9;
        self.labels.clear();

        // Map parameters to argument registers (X0-X7)
        for (i, param) in node.params.iter().enumerate() {
            if i < 8 {
                let reg = unsafe { std::mem::transmute::<u8, Reg64>(i as u8) };
                self.reg_alloc.insert(param.name.name.clone(), reg);
            } else {
                return Err(BmbError::CodegenError {
                    message: format!("Too many parameters (max 8): {}", node.name.name),
                });
            }
        }

        // Compile function body - iterate over Instructions
        for instr in &node.body {
            match instr {
                Instruction::Label(ident) => {
                    // Record label position
                    let label_name = ident.name.trim_start_matches('_').to_string();
                    self.labels.insert(label_name, self.code.len());
                }
                Instruction::Statement(stmt) => {
                    self.compile_statement(stmt)?;
                }
            }
        }

        Ok(())
    }

    /// Compile a single statement
    fn compile_statement(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        match &stmt.opcode {
            Opcode::Add => self.compile_binop(stmt, BinOp::Add),
            Opcode::Sub => self.compile_binop(stmt, BinOp::Sub),
            Opcode::Mul => self.compile_binop(stmt, BinOp::Mul),
            Opcode::Div => self.compile_binop(stmt, BinOp::Div),
            Opcode::Mod => self.compile_mod(stmt),
            Opcode::Eq => self.compile_comparison(stmt, Condition::EQ),
            Opcode::Ne => self.compile_comparison(stmt, Condition::NE),
            Opcode::Lt => self.compile_comparison(stmt, Condition::LT),
            Opcode::Le => self.compile_comparison(stmt, Condition::LE),
            Opcode::Gt => self.compile_comparison(stmt, Condition::GT),
            Opcode::Ge => self.compile_comparison(stmt, Condition::GE),
            Opcode::Mov => self.compile_mov(stmt),
            Opcode::Ret => self.compile_ret(stmt),
            Opcode::Jmp => self.compile_jmp(stmt),
            Opcode::Jif => self.compile_jif(stmt),
            Opcode::Call => self.compile_call(stmt),
            _ => Err(BmbError::CodegenError {
                message: format!("Unsupported opcode for ARM64: {:?}", stmt.opcode),
            }),
        }
    }

    /// Allocate or get a register for a BMB register
    fn get_or_alloc_reg(&mut self, name: &str) -> Result<Reg64, BmbError> {
        // Strip % prefix if present
        let name = name.trim_start_matches('%');

        if let Some(&reg) = self.reg_alloc.get(name) {
            return Ok(reg);
        }

        // Allocate new register (X9-X15 are caller-saved scratch)
        if self.next_reg > 15 {
            return Err(BmbError::CodegenError {
                message: "Register allocation exhausted".to_string(),
            });
        }

        let reg = unsafe { std::mem::transmute::<u8, Reg64>(self.next_reg) };
        self.reg_alloc.insert(name.to_string(), reg);
        self.next_reg += 1;
        Ok(reg)
    }

    /// Get operand as register, loading immediate if necessary
    fn load_operand(&mut self, operand: &Operand) -> Result<Reg64, BmbError> {
        match operand {
            Operand::Register(id) => self.get_or_alloc_reg(&id.name),
            Operand::Identifier(id) => self.get_or_alloc_reg(&id.name),
            Operand::IntLiteral(val) => {
                // Use X16 as scratch for immediates
                let reg = Reg64::X16;
                encoding::load_imm64(&mut self.code, reg, *val as u64);
                Ok(reg)
            }
            _ => Err(BmbError::CodegenError {
                message: format!("Unsupported operand type: {:?}", operand),
            }),
        }
    }

    /// Compile binary operation
    fn compile_binop(&mut self, stmt: &Statement, op: BinOp) -> Result<(), BmbError> {
        let dest = self.get_dest_reg(stmt)?;
        let src1 = self.load_operand(&stmt.operands[1])?;
        let src2 = self.load_operand(&stmt.operands[2])?;

        match op {
            BinOp::Add => encoding::add_x(&mut self.code, dest, src1, src2),
            BinOp::Sub => encoding::sub_x(&mut self.code, dest, src1, src2),
            BinOp::Mul => encoding::mul_x(&mut self.code, dest, src1, src2),
            BinOp::Div => encoding::sdiv_x(&mut self.code, dest, src1, src2),
        }

        Ok(())
    }

    /// Compile modulo operation
    fn compile_mod(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dest = self.get_dest_reg(stmt)?;
        let src1 = self.load_operand(&stmt.operands[1])?;
        let src2 = self.load_operand(&stmt.operands[2])?;

        // mod = a - (a / b) * b
        // Use X17 as scratch for division result
        encoding::sdiv_x(&mut self.code, Reg64::X17, src1, src2);
        encoding::msub_x(&mut self.code, dest, Reg64::X17, src2, src1);

        Ok(())
    }

    /// Compile comparison operation
    fn compile_comparison(&mut self, stmt: &Statement, cond: Condition) -> Result<(), BmbError> {
        let dest = self.get_dest_reg(stmt)?;
        let src1 = self.load_operand(&stmt.operands[1])?;
        let src2 = self.load_operand(&stmt.operands[2])?;

        // CMP src1, src2
        encoding::cmp_x(&mut self.code, src1, src2);

        // CSET dest, cond
        encoding::cset_x(&mut self.code, dest, cond);

        Ok(())
    }

    /// Compile mov operation
    fn compile_mov(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dest = self.get_dest_reg(stmt)?;

        match &stmt.operands[1] {
            Operand::IntLiteral(val) => {
                encoding::load_imm64(&mut self.code, dest, *val as u64);
            }
            Operand::Register(id) | Operand::Identifier(id) => {
                let src = self.get_or_alloc_reg(&id.name)?;
                if src != dest {
                    encoding::mov_x(&mut self.code, dest, src);
                }
            }
            _ => {
                return Err(BmbError::CodegenError {
                    message: format!("Unsupported mov operand: {:?}", stmt.operands[1]),
                });
            }
        }

        Ok(())
    }

    /// Compile return statement
    fn compile_ret(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        // Move return value to X0
        let src = self.load_operand(&stmt.operands[0])?;
        if src != Reg64::X0 {
            encoding::mov_x(&mut self.code, Reg64::X0, src);
        }

        // RET
        encoding::ret(&mut self.code);

        Ok(())
    }

    /// Compile unconditional jump
    fn compile_jmp(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let label_name = match &stmt.operands[0] {
            Operand::Label(label) => label.name.trim_start_matches('_').to_string(),
            Operand::Identifier(id) => id.name.trim_start_matches('_').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "jmp requires a label operand".to_string(),
                })
            }
        };

        self.pending_jumps.push((self.code.len(), label_name));
        // Placeholder branch instruction (will be patched)
        encoding::b(&mut self.code, 0);
        Ok(())
    }

    /// Compile conditional jump
    fn compile_jif(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let cond_reg = self.load_operand(&stmt.operands[0])?;

        let label_name = match &stmt.operands[1] {
            Operand::Label(label) => label.name.trim_start_matches('_').to_string(),
            Operand::Identifier(id) => id.name.trim_start_matches('_').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "jif requires a label operand".to_string(),
                })
            }
        };

        // CBNZ cond_reg, label (branch if not zero)
        self.pending_jumps.push((self.code.len(), label_name));
        encoding::cbnz_x(&mut self.code, cond_reg, 0);
        Ok(())
    }

    /// Compile function call
    fn compile_call(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dest = self.get_dest_reg(stmt)?;

        // Get function name
        let func_name = match &stmt.operands[1] {
            Operand::Identifier(id) => id.name.clone(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "call requires function name".to_string(),
                });
            }
        };

        // Load arguments into X0-X7
        for (i, arg) in stmt.operands[2..].iter().enumerate() {
            if i >= 8 {
                return Err(BmbError::CodegenError {
                    message: "Too many call arguments (max 8)".to_string(),
                });
            }
            let arg_reg = unsafe { std::mem::transmute::<u8, Reg64>(i as u8) };
            let src = self.load_operand(arg)?;
            if src != arg_reg {
                encoding::mov_x(&mut self.code, arg_reg, src);
            }
        }

        // BL to function (placeholder, will be patched)
        // For now, emit BL with offset 0 and record for patching
        self.pending_jumps
            .push((self.code.len(), format!("fn:{}", func_name)));
        encoding::bl(&mut self.code, 0);

        // Move result from X0 to destination
        if dest != Reg64::X0 {
            encoding::mov_x(&mut self.code, dest, Reg64::X0);
        }

        Ok(())
    }

    /// Get destination register from statement
    fn get_dest_reg(&mut self, stmt: &Statement) -> Result<Reg64, BmbError> {
        match &stmt.operands[0] {
            Operand::Register(id) => self.get_or_alloc_reg(&id.name),
            _ => Err(BmbError::CodegenError {
                message: "First operand must be a register".to_string(),
            }),
        }
    }

    /// Patch forward jump references
    fn patch_jumps(&mut self) -> Result<(), BmbError> {
        for (patch_offset, label) in &self.pending_jumps {
            let target = if label.starts_with("fn:") {
                let func_name = &label[3..];
                *self
                    .functions
                    .get(func_name)
                    .ok_or_else(|| BmbError::CodegenError {
                        message: format!("Unknown function: {}", func_name),
                    })?
            } else {
                *self
                    .labels
                    .get(label)
                    .ok_or_else(|| BmbError::CodegenError {
                        message: format!("Unknown label: {}", label),
                    })?
            };

            let offset = (target as isize - *patch_offset as isize) as i32;

            // Read the original instruction to determine type
            let orig = u32::from_le_bytes([
                self.code[*patch_offset],
                self.code[*patch_offset + 1],
                self.code[*patch_offset + 2],
                self.code[*patch_offset + 3],
            ]);

            let patched = if (orig >> 26) == 0b000101 {
                // B instruction
                let imm26 = ((offset >> 2) as u32) & 0x03FFFFFF;
                0x14000000 | imm26
            } else if (orig >> 26) == 0b100101 {
                // BL instruction
                let imm26 = ((offset >> 2) as u32) & 0x03FFFFFF;
                0x94000000 | imm26
            } else if (orig >> 24) == 0b10110101 {
                // CBNZ instruction
                let rt = orig & 0x1F;
                let imm19 = ((offset >> 2) as u32) & 0x7FFFF;
                0xB5000000 | (imm19 << 5) | rt
            } else {
                return Err(BmbError::CodegenError {
                    message: format!(
                        "Unknown branch instruction to patch at offset {}",
                        patch_offset
                    ),
                });
            };

            let bytes = patched.to_le_bytes();
            self.code[*patch_offset] = bytes[0];
            self.code[*patch_offset + 1] = bytes[1];
            self.code[*patch_offset + 2] = bytes[2];
            self.code[*patch_offset + 3] = bytes[3];
        }

        Ok(())
    }
}

impl Default for Arm64Codegen {
    fn default() -> Self {
        Self::new()
    }
}

/// Binary operation type
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Identifier, Span, Type};
    use crate::types::{TypedNode, TypeRegistry};

    fn make_stmt(opcode: Opcode, operands: Vec<Operand>) -> Instruction {
        Instruction::Statement(Statement {
            opcode,
            operands,
            span: Span::default(),
        })
    }

    fn make_reg(name: &str) -> Operand {
        Operand::Register(Identifier::new(name, Span::default()))
    }

    #[test]
    fn test_simple_add() {
        let mut codegen = Arm64Codegen::new();

        let node = Node {
            name: Identifier::new("main", Span::default()),
            tags: vec![],
            params: vec![],
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
                make_stmt(Opcode::Mov, vec![make_reg("a"), Operand::IntLiteral(10)]),
                make_stmt(Opcode::Mov, vec![make_reg("b"), Operand::IntLiteral(32)]),
                make_stmt(
                    Opcode::Add,
                    vec![make_reg("result"), make_reg("a"), make_reg("b")],
                ),
                make_stmt(Opcode::Ret, vec![make_reg("result")]),
            ],
            span: Span::default(),
        };

        let program = TypedProgram {
            imports: vec![],
            structs: vec![],
            enums: vec![],
            type_defs: vec![],
            contracts: vec![],
            nodes: vec![TypedNode {
                node,
                register_types: HashMap::new(),
            }],
            registry: TypeRegistry::new(),
        };

        let code = codegen
            .compile_executable(&program)
            .expect("Compilation failed");
        assert!(!code.is_empty());
        // Code should be multiple of 4 (ARM64 instructions are 4 bytes)
        assert_eq!(code.len() % 4, 0);
    }

    #[test]
    fn test_mov_immediate() {
        let mut codegen = Arm64Codegen::new();

        let node = Node {
            name: Identifier::new("main", Span::default()),
            tags: vec![],
            params: vec![],
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
                make_stmt(
                    Opcode::Mov,
                    vec![make_reg("result"), Operand::IntLiteral(42)],
                ),
                make_stmt(Opcode::Ret, vec![make_reg("result")]),
            ],
            span: Span::default(),
        };

        let program = TypedProgram {
            imports: vec![],
            structs: vec![],
            enums: vec![],
            type_defs: vec![],
            contracts: vec![],
            nodes: vec![TypedNode {
                node,
                register_types: HashMap::new(),
            }],
            registry: TypeRegistry::new(),
        };

        let code = codegen
            .compile_executable(&program)
            .expect("Compilation failed");
        assert!(!code.is_empty());
    }
}
