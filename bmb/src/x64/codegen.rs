//! BMB to x64 Code Generation
//!
//! Translates BMB TypedProgram to native x64 machine code.

use std::collections::HashMap;

use crate::ast::{CallingConvention, ExternDef, Instruction, Opcode, Operand, Statement};
use crate::types::TypedProgram;
use crate::BmbError;

use super::encoding::CodeBuffer;
use super::registers::{Reg64, SCRATCH_REGS, SYSV_ARG_REGS, WIN64_ARG_REGS, SYSV_RET_REG};

/// Linux x86-64 syscall numbers
pub mod syscall {
    pub const SYS_WRITE: u64 = 1;
    pub const SYS_EXIT: u64 = 60;

    // File descriptors
    pub const STDOUT: u64 = 1;
}

/// Windows API constants
pub mod winapi {
    /// GetStdHandle parameter for stdout
    pub const STD_OUTPUT_HANDLE: i32 = -11;
}

/// Target platform for code generation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetPlatform {
    Linux,
    Windows,
}

/// x64 code generator
pub struct X64Codegen {
    code: CodeBuffer,
    /// Function name -> code offset
    functions: HashMap<String, usize>,
    /// Variable name -> register mapping within current function
    var_regs: HashMap<String, Reg64>,
    /// Next available scratch register index
    next_scratch: usize,
    /// Pending relocations: (patch_offset, target_function)
    relocations: Vec<(usize, String)>,
    /// Label name -> code offset within current function
    labels: HashMap<String, usize>,
    /// Pending label fixups: (patch_offset, label_name)
    label_fixups: Vec<(usize, String)>,
    /// Extern function definitions (v0.12+)
    /// Used to determine calling conventions for xcall
    extern_defs: HashMap<String, ExternDef>,
}

impl X64Codegen {
    pub fn new() -> Self {
        Self {
            code: CodeBuffer::with_capacity(4096),
            functions: HashMap::new(),
            var_regs: HashMap::new(),
            next_scratch: 0,
            relocations: Vec::new(),
            labels: HashMap::new(),
            label_fixups: Vec::new(),
            extern_defs: HashMap::new(),
        }
    }

    /// Compile a typed program to x64 machine code (functions only, no entry point)
    pub fn compile(&mut self, program: &TypedProgram) -> Result<Vec<u8>, BmbError> {
        // Register extern functions for calling convention lookup (v0.12+)
        for extern_def in &program.extern_defs {
            self.extern_defs.insert(extern_def.name.name.clone(), extern_def.clone());
        }

        // Generate code for each function
        for node in &program.nodes {
            self.compile_function(node)?;
        }

        // Apply relocations (function calls)
        self.apply_relocations()?;

        Ok(self.code.code().to_vec())
    }

    /// Compile a typed program to a standalone x64 executable
    /// Generates _start entry point that calls main, prints result, and exits
    pub fn compile_executable(&mut self, program: &TypedProgram) -> Result<Vec<u8>, BmbError> {
        // Register extern functions for calling convention lookup (v0.12+)
        for extern_def in &program.extern_defs {
            self.extern_defs.insert(extern_def.name.name.clone(), extern_def.clone());
        }

        // First, emit _start which will jump over the functions to call main
        let start_offset = self.code.offset();

        // Reserve space for jump to _start code (will patch later)
        // jmp rel32 = 5 bytes
        self.code.emit_bytes(&[0xE9, 0x00, 0x00, 0x00, 0x00]);

        // Generate code for each function
        for node in &program.nodes {
            self.compile_function(node)?;
        }

        // Apply relocations (function calls between BMB functions)
        self.apply_relocations()?;

        // Now emit the actual _start code
        let start_code_offset = self.code.offset();

        // Patch the initial jump to point here
        let jump_rel = (start_code_offset - start_offset - 5) as i32;
        self.code.patch_i32(start_offset + 1, jump_rel);

        // _start: Call main function
        let main_offset = self
            .functions
            .get("main")
            .ok_or_else(|| BmbError::CodegenError {
                message: "No 'main' function found".to_string(),
            })?;
        let main_offset = *main_offset;

        // call main (relative call)
        let call_site = self.code.offset();
        self.code.emit_bytes(&[0xE8, 0x00, 0x00, 0x00, 0x00]); // call rel32
        let call_rel = (main_offset as i64 - call_site as i64 - 5) as i32;
        self.code.patch_i32(call_site + 1, call_rel);

        // Result is in RAX. Convert to string and print.
        // For simplicity, we'll handle numbers 0-999999 (up to 6 digits + newline)
        self.emit_print_i64();

        // syscall: exit(0)
        self.code.mov_r64_imm64(Reg64::RAX, syscall::SYS_EXIT);
        self.code.xor_r64_r64(Reg64::RDI, Reg64::RDI);
        self.code.syscall();

        Ok(self.code.code().to_vec())
    }

    /// Compile a typed program to a Windows x64 executable
    /// Generates entry point that calls main, prints result, and exits via Windows API
    ///
    /// The IAT RVAs must be provided so we can generate correct RIP-relative calls:
    /// - get_std_handle_iat: RVA of GetStdHandle entry in IAT
    /// - write_file_iat: RVA of WriteFile entry in IAT
    /// - exit_process_iat: RVA of ExitProcess entry in IAT
    pub fn compile_executable_windows(
        &mut self,
        program: &TypedProgram,
        iat_rvas: (u32, u32, u32),
    ) -> Result<Vec<u8>, BmbError> {
        let (get_std_handle_iat, write_file_iat, exit_process_iat) = iat_rvas;

        // Text section starts at RVA 0x1000
        let text_rva: u32 = 0x1000;

        // First, emit jump to _start code (will patch later)
        let start_offset = self.code.offset();
        self.code.emit_bytes(&[0xE9, 0x00, 0x00, 0x00, 0x00]); // jmp rel32

        // Generate code for each function
        for node in &program.nodes {
            self.compile_function_windows(node)?;
        }

        // Apply relocations (function calls between BMB functions)
        self.apply_relocations()?;

        // Now emit the actual _start code
        let start_code_offset = self.code.offset();

        // Patch the initial jump to point here
        let jump_rel = (start_code_offset - start_offset - 5) as i32;
        self.code.patch_i32(start_offset + 1, jump_rel);

        // _start: Windows entry point
        // First, allocate shadow space and align stack
        // sub rsp, 40 (32 shadow + 8 for alignment when we have 5 args)
        self.code.sub_r64_imm32(Reg64::RSP, 40);

        // Call main function
        let main_offset = self
            .functions
            .get("main")
            .ok_or_else(|| BmbError::CodegenError {
                message: "No 'main' function found".to_string(),
            })?;
        let main_offset = *main_offset;

        // call main (relative call)
        let call_site = self.code.offset();
        self.code.emit_bytes(&[0xE8, 0x00, 0x00, 0x00, 0x00]); // call rel32
        let call_rel = (main_offset as i64 - call_site as i64 - 5) as i32;
        self.code.patch_i32(call_site + 1, call_rel);

        // Result is in RAX. Convert to string and print.
        self.emit_print_i64_windows(text_rva, get_std_handle_iat, write_file_iat);

        // Call ExitProcess(0)
        // mov rcx, 0 (exit code)
        self.code.xor_r64_r64(Reg64::RCX, Reg64::RCX);
        // call [ExitProcess_IAT]
        self.emit_call_through_iat(text_rva, exit_process_iat);

        // Should never reach here, but add a safety hlt
        self.code.emit(0xF4); // hlt

        Ok(self.code.code().to_vec())
    }

    /// Emit a call through IAT entry (Windows)
    /// Uses FF 15 xx xx xx xx (call [rip+disp32])
    fn emit_call_through_iat(&mut self, text_rva: u32, iat_rva: u32) {
        // FF 15 = call [rip + disp32]
        // After this instruction, RIP points to the next instruction
        // We need: target = RIP + disp32
        // So: disp32 = target - RIP = iat_rva - (text_rva + current_offset + 6)
        let current_offset = self.code.offset() as u32;
        let rip_after_call = text_rva + current_offset + 6;
        let displacement = (iat_rva as i64 - rip_after_call as i64) as i32;

        self.code.emit_bytes(&[0xFF, 0x15]);
        self.code.emit_i32(displacement);
    }

    /// Emit code to print i64 value in RAX using Windows API
    fn emit_print_i64_windows(
        &mut self,
        text_rva: u32,
        get_std_handle_iat: u32,
        write_file_iat: u32,
    ) {
        // Save the value to print
        self.code.push_r64(Reg64::RAX);

        // Allocate buffer on stack (24 bytes for digits + newline + bytesWritten)
        // Also need shadow space for API calls (32 bytes)
        // Total: 64 bytes, but we already have 8 from push, so allocate 56 + 8 = 64 aligned
        self.code.sub_r64_imm32(Reg64::RSP, 64);

        // Get stdout handle: GetStdHandle(STD_OUTPUT_HANDLE)
        // mov ecx, -11 (STD_OUTPUT_HANDLE)
        self.code.emit_bytes(&[0xB9]); // mov ecx, imm32
        self.code.emit_i32(winapi::STD_OUTPUT_HANDLE);

        // call GetStdHandle
        self.emit_call_through_iat(text_rva, get_std_handle_iat);

        // Save handle (returned in RAX) to R12 (callee-saved)
        self.code.push_r64(Reg64::R12);
        self.code.mov_r64_r64(Reg64::R12, Reg64::RAX);

        // Now convert number to string
        // The value to convert is at [RSP + 64 + 8 + 8] = [RSP + 80]
        // (64 we allocated + 8 for pushed RAX + 8 for pushed R12)

        // RSI will point to end of buffer, we build string backwards
        // Buffer is at RSP + 32 (after shadow space)
        self.code.mov_r64_r64(Reg64::RSI, Reg64::RSP);
        self.code.add_r64_imm32(Reg64::RSI, 32 + 23); // Point to end of buffer

        // Store newline at the end
        // mov byte [rsi], 0x0A
        self.code.emit_bytes(&[0xC6, 0x06, 0x0A]);

        // RBX = digit count (starts at 1 for newline), callee-saved so save first
        self.code.push_r64(Reg64::RBX);
        self.code.mov_r64_imm64(Reg64::RBX, 1);

        // RAX = value to convert (from stack: push RAX=8 + sub 64 + push R12=8 + push RBX=8 = 80)
        self.code.emit_bytes(&[0x48, 0x8B, 0x84, 0x24]); // mov rax, [rsp + imm32]
        self.code.emit_i32(80);

        // R8 = 10 (divisor)
        self.code.mov_r64_imm64(Reg64::R8, 10);

        // Loop: divide by 10, store remainder as ASCII digit
        let loop_start = self.code.offset();

        // dec rsi (move buffer pointer back)
        self.code.emit_bytes(&[0x48, 0xFF, 0xCE]);

        // xor rdx, rdx (clear for division)
        self.code.xor_r64_r64(Reg64::RDX, Reg64::RDX);

        // div r8 (rax = rax / 10, rdx = rax % 10)
        self.code.emit_bytes(&[0x49, 0xF7, 0xF0]);

        // add dl, '0' (convert to ASCII)
        self.code.emit_bytes(&[0x80, 0xC2, 0x30]);

        // mov [rsi], dl
        self.code.emit_bytes(&[0x88, 0x16]);

        // inc rbx (digit count)
        self.code.emit_bytes(&[0x48, 0xFF, 0xC3]);

        // test rax, rax (check if more digits)
        self.code.emit_bytes(&[0x48, 0x85, 0xC0]);

        // jnz loop_start
        let jnz_offset = self.code.offset();
        self.code.emit_bytes(&[0x75, 0x00]);
        let rel = (loop_start as i64 - jnz_offset as i64 - 2) as i8;
        self.code.code_mut()[jnz_offset + 1] = rel as u8;

        // Now RSI points to start of string, RBX = length
        // WriteFile(hFile, lpBuffer, nNumberOfBytesToWrite, lpNumberOfBytesWritten, lpOverlapped)
        // RCX = handle (R12)
        // RDX = buffer (RSI)
        // R8 = length (RBX)
        // R9 = &bytesWritten (RSP + 32 + 24 = RSP + 56, but we need to use a location)
        // [RSP + 32] = lpOverlapped (NULL)

        self.code.mov_r64_r64(Reg64::RCX, Reg64::R12); // handle
        self.code.mov_r64_r64(Reg64::RDX, Reg64::RSI); // buffer
        self.code.mov_r64_r64(Reg64::R8, Reg64::RBX); // length

        // R9 = pointer to bytesWritten (use stack space at RSP + 56)
        self.code.mov_r64_r64(Reg64::R9, Reg64::RSP);
        self.code.add_r64_imm32(Reg64::R9, 56);

        // [RSP + 32] = NULL (lpOverlapped)
        self.code
            .emit_bytes(&[0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00]); // mov qword [rsp+32], 0

        // call WriteFile
        self.emit_call_through_iat(text_rva, write_file_iat);

        // Restore RBX
        self.code.pop_r64(Reg64::RBX);

        // Restore R12
        self.code.pop_r64(Reg64::R12);

        // Clean up stack (64 + 8 for original pushed RAX)
        self.code.add_r64_imm32(Reg64::RSP, 72);
    }

    /// Compile a single function for Windows (uses Windows calling convention)
    fn compile_function_windows(&mut self, node: &crate::types::TypedNode) -> Result<(), BmbError> {
        // Record function entry point
        let func_offset = self.code.offset();
        self.functions
            .insert(node.node.name.name.clone(), func_offset);

        // Reset per-function state
        self.var_regs.clear();
        self.labels.clear();
        self.label_fixups.clear();
        self.next_scratch = 0;

        // Function prologue
        self.emit_prologue();

        // Map parameters to registers (Windows x64 ABI: RCX, RDX, R8, R9)
        use super::registers::WIN64_ARG_REGS;
        for (i, param) in node.node.params.iter().enumerate() {
            if i < WIN64_ARG_REGS.len() {
                self.var_regs
                    .insert(param.name.name.clone(), WIN64_ARG_REGS[i]);
            } else {
                return Err(BmbError::CodegenError {
                    message: format!(
                        "Too many parameters: {} (max {})",
                        node.node.params.len(),
                        WIN64_ARG_REGS.len()
                    ),
                });
            }
        }

        // First pass: collect label positions
        let mut temp_offset = self.code.offset();
        for instr in &node.node.body {
            match instr {
                Instruction::Label(ident) => {
                    let label_name = ident.name.trim_start_matches('_').to_string();
                    self.labels.insert(label_name, temp_offset);
                }
                Instruction::Statement(stmt) => {
                    temp_offset += self.estimate_stmt_size(stmt);
                }
                Instruction::Match(_) => {
                    // TODO: Pattern matching codegen - estimate size
                    temp_offset += 64; // Conservative estimate for match statement
                }
            }
        }

        // Second pass: generate code
        for instr in &node.node.body {
            match instr {
                Instruction::Label(ident) => {
                    let label_name = ident.name.trim_start_matches('_').to_string();
                    self.labels.insert(label_name, self.code.offset());
                }
                Instruction::Statement(stmt) => {
                    // For print statements on Windows, we need special handling
                    // But since we don't have IAT info here, print in functions is not yet supported
                    // Only print in _start entry point works
                    if matches!(stmt.opcode, Opcode::Print) {
                        return Err(BmbError::CodegenError {
                            message: "print in functions not yet supported for Windows (only at top level main)".to_string(),
                        });
                    }
                    self.compile_statement(stmt)?;
                }
                Instruction::Match(_) => {
                    return Err(BmbError::CodegenError {
                        message: "Pattern matching not yet supported in Windows PE codegen".to_string(),
                    });
                }
            }
        }

        // Apply label fixups within this function
        self.apply_label_fixups()?;

        Ok(())
    }

    /// Emit code to print the i64 value in RAX followed by newline
    fn emit_print_i64(&mut self) {
        // Save the value
        self.code.push_r64(Reg64::RAX);

        // Allocate buffer on stack (16 bytes for digits + newline)
        self.code.sub_r64_imm32(Reg64::RSP, 24);

        // RSI will point to end of buffer, we build string backwards
        self.code.mov_r64_r64(Reg64::RSI, Reg64::RSP);
        self.code.add_r64_imm32(Reg64::RSI, 23); // Point to end

        // Store newline at the end
        // mov byte [rsi], 0x0A
        self.code.emit_bytes(&[0xC6, 0x06, 0x0A]);

        // RCX = digit count (starts at 1 for newline)
        self.code.mov_r64_imm64(Reg64::RCX, 1);

        // RAX = value to convert
        self.code.mov_r64_r64(Reg64::RAX, Reg64::RSP);
        self.code.add_r64_imm32(Reg64::RAX, 24 + 8); // Point to saved value
                                                     // mov rax, [rax]
        self.code.emit_bytes(&[0x48, 0x8B, 0x00]);

        // Handle negative numbers: if RAX < 0, negate and remember
        // For now, we only handle positive numbers

        // R8 = 10 (divisor)
        self.code.mov_r64_imm64(Reg64::R8, 10);

        // Loop: divide by 10, store remainder as ASCII digit
        let loop_start = self.code.offset();

        // dec rsi (move buffer pointer back)
        self.code.emit_bytes(&[0x48, 0xFF, 0xCE]);

        // xor rdx, rdx (clear for division)
        self.code.xor_r64_r64(Reg64::RDX, Reg64::RDX);

        // div r8 (rax = rax / 10, rdx = rax % 10)
        self.code.emit_bytes(&[0x49, 0xF7, 0xF0]);

        // add dl, '0' (convert to ASCII)
        self.code.emit_bytes(&[0x80, 0xC2, 0x30]);

        // mov [rsi], dl
        self.code.emit_bytes(&[0x88, 0x16]);

        // inc rcx (digit count)
        self.code.emit_bytes(&[0x48, 0xFF, 0xC1]);

        // test rax, rax (check if more digits)
        self.code.emit_bytes(&[0x48, 0x85, 0xC0]);

        // jnz loop_start
        let jnz_offset = self.code.offset();
        self.code.emit_bytes(&[0x75, 0x00]);
        let rel = (loop_start as i64 - jnz_offset as i64 - 2) as i8;
        self.code.code_mut()[jnz_offset + 1] = rel as u8;

        // Now RSI points to start of string, RCX = length
        // syscall: write(1, rsi, rcx)
        self.code.mov_r64_imm64(Reg64::RAX, syscall::SYS_WRITE);
        self.code.mov_r64_imm64(Reg64::RDI, syscall::STDOUT);
        // RSI already points to buffer
        self.code.mov_r64_r64(Reg64::RDX, Reg64::RCX);
        self.code.syscall();

        // Clean up stack
        self.code.add_r64_imm32(Reg64::RSP, 24 + 8);
    }

    /// Compile a single function
    fn compile_function(&mut self, node: &crate::types::TypedNode) -> Result<(), BmbError> {
        // Record function entry point
        let func_offset = self.code.offset();
        self.functions
            .insert(node.node.name.name.clone(), func_offset);

        // Reset per-function state
        self.var_regs.clear();
        self.labels.clear();
        self.label_fixups.clear();
        self.next_scratch = 0;

        // Function prologue
        self.emit_prologue();

        // Map parameters to registers (System V ABI)
        for (i, param) in node.node.params.iter().enumerate() {
            if i < SYSV_ARG_REGS.len() {
                self.var_regs
                    .insert(param.name.name.clone(), SYSV_ARG_REGS[i]);
            } else {
                return Err(BmbError::CodegenError {
                    message: format!(
                        "Too many parameters: {} (max {})",
                        node.node.params.len(),
                        SYSV_ARG_REGS.len()
                    ),
                });
            }
        }

        // First pass: collect label positions
        let mut temp_offset = self.code.offset();
        for instr in &node.node.body {
            match instr {
                Instruction::Label(ident) => {
                    let label_name = ident.name.trim_start_matches('_').to_string();
                    self.labels.insert(label_name, temp_offset);
                }
                Instruction::Statement(stmt) => {
                    // Estimate instruction size (rough approximation)
                    temp_offset += self.estimate_stmt_size(stmt);
                }
                Instruction::Match(_) => {
                    // TODO: Pattern matching codegen - estimate size
                    temp_offset += 64; // Conservative estimate for match statement
                }
            }
        }

        // Second pass: generate code
        for instr in &node.node.body {
            match instr {
                Instruction::Label(ident) => {
                    let label_name = ident.name.trim_start_matches('_').to_string();
                    self.labels.insert(label_name, self.code.offset());
                }
                Instruction::Statement(stmt) => {
                    self.compile_statement(stmt)?;
                }
                Instruction::Match(_) => {
                    return Err(BmbError::CodegenError {
                        message: "Pattern matching not yet supported in ELF64 codegen".to_string(),
                    });
                }
            }
        }

        // Apply label fixups within this function
        self.apply_label_fixups()?;

        Ok(())
    }

    /// Estimate statement size for label offset calculation
    fn estimate_stmt_size(&self, stmt: &Statement) -> usize {
        match stmt.opcode {
            Opcode::Ret => 10,
            Opcode::Jmp | Opcode::Jif => 15,
            Opcode::Call => 20,
            _ => 15,
        }
    }

    /// Emit function prologue
    fn emit_prologue(&mut self) {
        self.code.push_r64(Reg64::RBP);
        self.code.mov_r64_r64(Reg64::RBP, Reg64::RSP);
    }

    /// Emit function epilogue
    fn emit_epilogue(&mut self) {
        self.code.mov_r64_r64(Reg64::RSP, Reg64::RBP);
        self.code.pop_r64(Reg64::RBP);
    }

    /// Allocate a register for a variable
    fn alloc_reg(&mut self, var_name: &str) -> Result<Reg64, BmbError> {
        if let Some(&reg) = self.var_regs.get(var_name) {
            return Ok(reg);
        }

        if self.next_scratch >= SCRATCH_REGS.len() {
            return Err(BmbError::CodegenError {
                message: "Register allocation overflow".to_string(),
            });
        }

        let reg = SCRATCH_REGS[self.next_scratch];
        self.next_scratch += 1;
        self.var_regs.insert(var_name.to_string(), reg);
        Ok(reg)
    }

    /// Get register for an operand, loading immediate if needed
    fn operand_to_reg(
        &mut self,
        operand: &Operand,
        hint: Option<Reg64>,
    ) -> Result<Reg64, BmbError> {
        match operand {
            Operand::Register(var) => {
                let var_name = var.name.trim_start_matches('%');
                self.var_regs
                    .get(var_name)
                    .copied()
                    .ok_or_else(|| BmbError::CodegenError {
                        message: format!("Undefined variable: {}", var_name),
                    })
            }
            Operand::IntLiteral(val) => {
                let reg = hint.unwrap_or_else(|| {
                    let r = SCRATCH_REGS[self.next_scratch.min(SCRATCH_REGS.len() - 1)];
                    self.next_scratch += 1;
                    r
                });
                if *val >= i32::MIN as i64 && *val <= i32::MAX as i64 {
                    self.code.mov_r64_imm32(reg, *val as i32);
                } else {
                    self.code.mov_r64_imm64(reg, *val as u64);
                }
                Ok(reg)
            }
            Operand::Identifier(id) => {
                let var_name = id.name.trim_start_matches('%');
                self.var_regs
                    .get(var_name)
                    .copied()
                    .ok_or_else(|| BmbError::CodegenError {
                        message: format!("Undefined identifier: {}", var_name),
                    })
            }
            _ => Err(BmbError::CodegenError {
                message: format!("Unsupported operand: {:?}", operand),
            }),
        }
    }

    /// Compile a single statement
    fn compile_statement(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        match stmt.opcode {
            Opcode::Mov => self.compile_mov(stmt),
            Opcode::Add => self.compile_binary_op(stmt, BinaryOp::Add),
            Opcode::Sub => self.compile_binary_op(stmt, BinaryOp::Sub),
            Opcode::Mul => self.compile_binary_op(stmt, BinaryOp::Mul),
            Opcode::Div => self.compile_div(stmt),
            Opcode::Mod => self.compile_mod(stmt),
            Opcode::Eq => self.compile_comparison(stmt, Comparison::Eq),
            Opcode::Ne => self.compile_comparison(stmt, Comparison::Ne),
            Opcode::Lt => self.compile_comparison(stmt, Comparison::Lt),
            Opcode::Le => self.compile_comparison(stmt, Comparison::Le),
            Opcode::Gt => self.compile_comparison(stmt, Comparison::Gt),
            Opcode::Ge => self.compile_comparison(stmt, Comparison::Ge),
            Opcode::Ret => self.compile_ret(stmt),
            Opcode::Jmp => self.compile_jmp(stmt),
            Opcode::Jif => self.compile_jif(stmt),
            Opcode::Call => self.compile_call(stmt),
            Opcode::Xcall => self.compile_xcall(stmt),
            Opcode::And => self.compile_binary_op(stmt, BinaryOp::And),
            Opcode::Or => self.compile_binary_op(stmt, BinaryOp::Or),
            Opcode::Xor => self.compile_binary_op(stmt, BinaryOp::Xor),
            Opcode::Shl => self.compile_binary_op(stmt, BinaryOp::Shl),
            Opcode::Shr => self.compile_binary_op(stmt, BinaryOp::Shr),
            Opcode::Not => self.compile_not(stmt),
            Opcode::Load | Opcode::Store => Err(BmbError::CodegenError {
                message: "Memory operations not yet implemented".to_string(),
            }),
            Opcode::Print => self.compile_print(stmt),
            Opcode::Box | Opcode::Unbox | Opcode::Drop => Err(BmbError::CodegenError {
                message: "Heap allocation operations not yet implemented for x64".to_string(),
            }),
        }
    }

    fn compile_mov(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dst_name = match &stmt.operands[0] {
            Operand::Register(v) => v.name.trim_start_matches('%').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "MOV destination must be register".to_string(),
                })
            }
        };

        let dst_reg = self.alloc_reg(&dst_name)?;
        let src_reg = self.operand_to_reg(&stmt.operands[1], Some(dst_reg))?;

        if dst_reg != src_reg {
            self.code.mov_r64_r64(dst_reg, src_reg);
        }
        Ok(())
    }

    fn compile_binary_op(&mut self, stmt: &Statement, op: BinaryOp) -> Result<(), BmbError> {
        let dst_name = match &stmt.operands[0] {
            Operand::Register(v) => v.name.trim_start_matches('%').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "Binary op destination must be register".to_string(),
                })
            }
        };

        let dst_reg = self.alloc_reg(&dst_name)?;

        // Load first operand
        let src1 = self.operand_to_reg(&stmt.operands[1], Some(dst_reg))?;
        if src1 != dst_reg {
            self.code.mov_r64_r64(dst_reg, src1);
        }

        // Load second operand to a temp register
        let src2 = self.operand_to_reg(&stmt.operands[2], None)?;

        match op {
            BinaryOp::Add => self.code.add_r64_r64(dst_reg, src2),
            BinaryOp::Sub => self.code.sub_r64_r64(dst_reg, src2),
            BinaryOp::Mul => self.code.imul_r64_r64(dst_reg, src2),
            BinaryOp::And => self.code.and_r64_r64(dst_reg, src2),
            BinaryOp::Or => self.code.or_r64_r64(dst_reg, src2),
            BinaryOp::Xor => self.code.xor_r64_r64(dst_reg, src2),
            BinaryOp::Shl => {
                // SHL uses CL for shift count - move src2 to RCX
                self.code.mov_r64_r64(Reg64::RCX, src2);
                self.code.shl_r64_cl(dst_reg);
            }
            BinaryOp::Shr => {
                // SAR uses CL for shift count - move src2 to RCX
                self.code.mov_r64_r64(Reg64::RCX, src2);
                self.code.sar_r64_cl(dst_reg);
            }
        }
        Ok(())
    }

    fn compile_div(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dst_name = match &stmt.operands[0] {
            Operand::Register(v) => v.name.trim_start_matches('%').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "DIV destination must be register".to_string(),
                })
            }
        };

        let dst_reg = self.alloc_reg(&dst_name)?;

        // dividend -> RAX
        let dividend = self.operand_to_reg(&stmt.operands[1], Some(Reg64::RAX))?;
        if dividend != Reg64::RAX {
            self.code.mov_r64_r64(Reg64::RAX, dividend);
        }

        // Sign extend RAX into RDX:RAX
        self.code.cqo();

        // divisor
        let divisor = self.operand_to_reg(&stmt.operands[2], Some(Reg64::RCX))?;
        if divisor == Reg64::RAX || divisor == Reg64::RDX {
            self.code.mov_r64_r64(Reg64::RCX, divisor);
            self.code.idiv_r64(Reg64::RCX);
        } else {
            self.code.idiv_r64(divisor);
        }

        // Result (quotient) is in RAX
        if dst_reg != Reg64::RAX {
            self.code.mov_r64_r64(dst_reg, Reg64::RAX);
        }
        Ok(())
    }

    fn compile_mod(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dst_name = match &stmt.operands[0] {
            Operand::Register(v) => v.name.trim_start_matches('%').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "MOD destination must be register".to_string(),
                })
            }
        };

        let dst_reg = self.alloc_reg(&dst_name)?;

        let dividend = self.operand_to_reg(&stmt.operands[1], Some(Reg64::RAX))?;
        if dividend != Reg64::RAX {
            self.code.mov_r64_r64(Reg64::RAX, dividend);
        }
        self.code.cqo();

        let divisor = self.operand_to_reg(&stmt.operands[2], Some(Reg64::RCX))?;
        if divisor == Reg64::RAX || divisor == Reg64::RDX {
            self.code.mov_r64_r64(Reg64::RCX, divisor);
            self.code.idiv_r64(Reg64::RCX);
        } else {
            self.code.idiv_r64(divisor);
        }

        // Remainder is in RDX
        if dst_reg != Reg64::RDX {
            self.code.mov_r64_r64(dst_reg, Reg64::RDX);
        }
        Ok(())
    }

    fn compile_not(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dst_name = match &stmt.operands[0] {
            Operand::Register(v) => v.name.trim_start_matches('%').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "NOT destination must be register".to_string(),
                })
            }
        };

        let dst_reg = self.alloc_reg(&dst_name)?;

        // Load operand
        let src = self.operand_to_reg(&stmt.operands[1], Some(dst_reg))?;
        if src != dst_reg {
            self.code.mov_r64_r64(dst_reg, src);
        }

        // Apply bitwise NOT
        self.code.not_r64(dst_reg);

        Ok(())
    }

    fn compile_comparison(&mut self, stmt: &Statement, cmp: Comparison) -> Result<(), BmbError> {
        let dst_name = match &stmt.operands[0] {
            Operand::Register(v) => v.name.trim_start_matches('%').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "Comparison destination must be register".to_string(),
                })
            }
        };

        let dst_reg = self.alloc_reg(&dst_name)?;

        let left = self.operand_to_reg(&stmt.operands[1], None)?;
        let right = self.operand_to_reg(&stmt.operands[2], None)?;

        self.code.cmp_r64_r64(left, right);

        match cmp {
            Comparison::Eq => self.code.sete(dst_reg),
            Comparison::Ne => self.code.setne(dst_reg),
            Comparison::Lt => self.code.setl(dst_reg),
            Comparison::Le => self.code.setle(dst_reg),
            Comparison::Gt => self.code.setg(dst_reg),
            Comparison::Ge => self.code.setge(dst_reg),
        }

        self.code.movzx_r64_r8(dst_reg, dst_reg);
        Ok(())
    }

    fn compile_ret(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        if !stmt.operands.is_empty() {
            let ret_val = self.operand_to_reg(&stmt.operands[0], Some(SYSV_RET_REG))?;
            if ret_val != SYSV_RET_REG {
                self.code.mov_r64_r64(SYSV_RET_REG, ret_val);
            }
        }
        self.emit_epilogue();
        self.code.ret();
        Ok(())
    }

    fn compile_jmp(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let label = match &stmt.operands[0] {
            Operand::Identifier(id) | Operand::Label(id) => {
                id.name.trim_start_matches('_').to_string()
            }
            _ => {
                return Err(BmbError::CodegenError {
                    message: "JMP target must be label".to_string(),
                })
            }
        };

        let patch_offset = self.code.jmp_rel32();
        self.label_fixups.push((patch_offset, label));
        Ok(())
    }

    fn compile_jif(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let cond = self.operand_to_reg(&stmt.operands[0], None)?;
        let label = match &stmt.operands[1] {
            Operand::Identifier(id) | Operand::Label(id) => {
                id.name.trim_start_matches('_').to_string()
            }
            _ => {
                return Err(BmbError::CodegenError {
                    message: "JIF target must be label".to_string(),
                })
            }
        };

        self.code.cmp_r64_imm32(cond, 0);
        let patch_offset = self.code.jne_rel32();
        self.label_fixups.push((patch_offset, label));
        Ok(())
    }

    fn compile_call(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let dst_name = match &stmt.operands[0] {
            Operand::Register(v) => v.name.trim_start_matches('%').to_string(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "CALL destination must be register".to_string(),
                })
            }
        };

        let func_name = match &stmt.operands[1] {
            Operand::Identifier(id) => id.name.clone(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "CALL target must be function name".to_string(),
                })
            }
        };

        // Setup arguments
        for (i, arg) in stmt.operands.iter().skip(2).enumerate() {
            if i >= SYSV_ARG_REGS.len() {
                return Err(BmbError::CodegenError {
                    message: "Too many arguments".to_string(),
                });
            }
            let arg_reg = self.operand_to_reg(arg, Some(SYSV_ARG_REGS[i]))?;
            if arg_reg != SYSV_ARG_REGS[i] {
                self.code.mov_r64_r64(SYSV_ARG_REGS[i], arg_reg);
            }
        }

        let patch_offset = self.code.call_rel32();
        self.relocations.push((patch_offset, func_name));

        let dst_reg = self.alloc_reg(&dst_name)?;
        if dst_reg != SYSV_RET_REG {
            self.code.mov_r64_r64(dst_reg, SYSV_RET_REG);
        }
        Ok(())
    }

    /// Compile print statement: print "string"
    /// Uses write syscall to output string to stdout
    fn compile_print(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let string_data = match &stmt.operands[0] {
            Operand::StringLiteral(s) => s.clone(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "print requires string literal operand".to_string(),
                })
            }
        };

        let str_len = string_data.len();

        // Strategy: jump over inline string data, then use RIP-relative addressing
        //
        // jmp over_string       ; jump over string data
        // string_data: db "..." ; inline string bytes
        // over_string:
        //   lea rsi, [rip - (str_len + lea_size)]  ; point to string
        //   mov rdx, str_len    ; length
        //   mov rax, 1          ; SYS_WRITE
        //   mov rdi, 1          ; STDOUT
        //   syscall

        // Emit jmp rel8 over string data
        // jmp displacement is calculated from END of jmp instruction
        // jmp (2 bytes) -> string (str_len bytes) -> code
        // displacement = str_len (jump over string bytes)
        if str_len > 127 {
            return Err(BmbError::CodegenError {
                message: "String too long for inline embedding (max 127 bytes)".to_string(),
            });
        }
        self.code.emit_bytes(&[0xEB, str_len as u8]); // jmp rel8

        // Emit string data inline
        let string_start = self.code.offset();
        for byte in string_data.bytes() {
            self.code.emit(byte);
        }

        // Now emit the write syscall code
        // lea rsi, [rip - offset_to_string_start]
        // The LEA instruction is 7 bytes: 48 8D 35 xx xx xx xx
        // After LEA executes, RIP points to the next instruction
        // We need to calculate: string_start - (current_pos + 7)
        let lea_offset_pos = self.code.offset();
        self.code
            .emit_bytes(&[0x48, 0x8D, 0x35, 0x00, 0x00, 0x00, 0x00]); // lea rsi, [rip+rel32]

        // Patch the LEA displacement
        // RIP after LEA = lea_offset_pos + 7
        // Target = string_start
        // Displacement = string_start - (lea_offset_pos + 7)
        let lea_displacement = (string_start as i64) - ((lea_offset_pos + 7) as i64);
        self.code
            .patch_i32(lea_offset_pos + 3, lea_displacement as i32);

        // mov rdx, str_len (string length)
        self.code.mov_r64_imm64(Reg64::RDX, str_len as u64);

        // mov rax, 1 (SYS_WRITE)
        self.code.mov_r64_imm64(Reg64::RAX, syscall::SYS_WRITE);

        // mov rdi, 1 (STDOUT)
        self.code.mov_r64_imm64(Reg64::RDI, syscall::STDOUT);

        // syscall
        self.code.emit_bytes(&[0x0F, 0x05]);

        Ok(())
    }

    fn compile_xcall(&mut self, stmt: &Statement) -> Result<(), BmbError> {
        let func_name = match &stmt.operands[0] {
            Operand::Identifier(id) => id.name.clone(),
            _ => {
                return Err(BmbError::CodegenError {
                    message: "XCALL target must be function name".to_string(),
                })
            }
        };

        // Check if this is an extern function (v0.12+)
        if let Some(extern_def) = self.extern_defs.get(&func_name).cloned() {
            // Set up arguments according to calling convention
            let arg_regs = match extern_def.calling_convention {
                CallingConvention::C | CallingConvention::SysV64 => &SYSV_ARG_REGS[..],
                CallingConvention::Win64 | CallingConvention::System => &WIN64_ARG_REGS[..],
            };

            // Move arguments to calling convention registers
            let args = &stmt.operands[1..]; // Skip function name operand
            for (i, arg) in args.iter().enumerate() {
                if i >= arg_regs.len() {
                    return Err(BmbError::CodegenError {
                        message: format!(
                            "Too many arguments for extern function '{}': {} provided, max {} for calling convention {:?}",
                            func_name,
                            args.len(),
                            arg_regs.len(),
                            extern_def.calling_convention
                        ),
                    });
                }
                let target_reg = arg_regs[i];
                let src_reg = self.operand_to_reg(arg, Some(target_reg))?;
                if src_reg != target_reg {
                    self.code.mov_r64_r64(target_reg, src_reg);
                }
            }

            // NOTE: Actual extern function calls require dynamic linking support
            // which is not yet implemented for native x64 executables.
            // For now, emit a placeholder that documents the extern call setup.
            // Future versions will add PLT/GOT support for Linux and IAT for Windows.
            //
            // The WASM backend fully supports extern function calls via imports.
            return Err(BmbError::CodegenError {
                message: format!(
                    "Extern function call '{}' with {:?} calling convention: \
                     Native x64 extern calls require dynamic linking (future work). \
                     Use WASM target (--emit wasm) for full extern function support.",
                    func_name,
                    extern_def.calling_convention
                ),
            });
        }

        // Handle built-in external functions
        match func_name.as_str() {
            "print_i32" | "print_i64" => {
                let val = self.operand_to_reg(&stmt.operands[1], Some(Reg64::RDI))?;
                if val != Reg64::RDI {
                    self.code.mov_r64_r64(Reg64::RDI, val);
                }
                // Placeholder - proper implementation needs itoa
            }
            "print_newline" => {
                // syscall: write(1, "\n", 1)
                // Would need a data section for the newline character
            }
            _ => {
                return Err(BmbError::CodegenError {
                    message: format!("Unknown external function: {}", func_name),
                });
            }
        }
        Ok(())
    }

    /// Apply relocations after all code is generated
    fn apply_relocations(&mut self) -> Result<(), BmbError> {
        for (patch_offset, func_name) in &self.relocations {
            let target = self
                .functions
                .get(func_name)
                .ok_or_else(|| BmbError::CodegenError {
                    message: format!("Undefined function: {}", func_name),
                })?;

            let rel = (*target as i64) - (*patch_offset as i64 + 4);
            if rel < i32::MIN as i64 || rel > i32::MAX as i64 {
                return Err(BmbError::CodegenError {
                    message: "Call target out of range".to_string(),
                });
            }

            self.code.patch_i32(*patch_offset, rel as i32);
        }
        Ok(())
    }

    /// Apply label fixups within current function
    fn apply_label_fixups(&mut self) -> Result<(), BmbError> {
        for (patch_offset, label_name) in &self.label_fixups {
            let target = self
                .labels
                .get(label_name)
                .ok_or_else(|| BmbError::CodegenError {
                    message: format!("Undefined label: {}", label_name),
                })?;

            let rel = (*target as i64) - (*patch_offset as i64 + 4);
            if rel < i32::MIN as i64 || rel > i32::MAX as i64 {
                return Err(BmbError::CodegenError {
                    message: "Jump target out of range".to_string(),
                });
            }

            self.code.patch_i32(*patch_offset, rel as i32);
        }
        self.label_fixups.clear();
        Ok(())
    }
}

impl Default for X64Codegen {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy)]
enum BinaryOp {
    Add,
    Sub,
    Mul,
    // Bitwise operations
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, Copy)]
enum Comparison {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Generate a minimal "Hello World" program that prints 42 and exits
pub fn generate_hello_world() -> Vec<u8> {
    let mut code = CodeBuffer::new();

    // Convert 42 to ASCII digits: "42\n" = [0x34, 0x32, 0x0A]
    // Store on stack (in reverse for little-endian push)
    code.mov_r64_imm64(Reg64::RAX, 0x0A3234); // "\n24" reversed = "42\n"
    code.push_r64(Reg64::RAX);

    // syscall: write(fd=1, buf=rsp, count=3)
    code.mov_r64_imm64(Reg64::RAX, syscall::SYS_WRITE);
    code.mov_r64_imm64(Reg64::RDI, syscall::STDOUT);
    code.mov_r64_r64(Reg64::RSI, Reg64::RSP);
    code.mov_r64_imm64(Reg64::RDX, 3);
    code.syscall();

    // Clean up stack
    code.add_r64_imm32(Reg64::RSP, 8);

    // syscall: exit(0)
    code.mov_r64_imm64(Reg64::RAX, syscall::SYS_EXIT);
    code.xor_r64_r64(Reg64::RDI, Reg64::RDI);
    code.syscall();

    code.into_code()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x64::elf::Elf64Builder;

    #[test]
    fn test_hello_world_generation() {
        let code = generate_hello_world();
        assert!(!code.is_empty());
        // First instruction should start with REX prefix or mov
        assert!(code[0] == 0x48 || code[0] == 0x50);
    }

    #[test]
    fn test_hello_world_elf() {
        // Generate machine code
        let code = generate_hello_world();
        assert!(!code.is_empty());

        // Build ELF executable
        let elf = Elf64Builder::new().code(code).build();

        // Verify ELF magic
        assert_eq!(&elf[0..4], &[0x7F, b'E', b'L', b'F']);

        // Verify 64-bit
        assert_eq!(elf[4], 2);

        // Verify little endian
        assert_eq!(elf[5], 1);

        // Verify executable type (offset 16-17)
        assert_eq!(elf[16], 2);
        assert_eq!(elf[17], 0);

        // Verify x86-64 (offset 18-19)
        assert_eq!(elf[18], 62);
        assert_eq!(elf[19], 0);

        // Verify entry point is set (offset 24-31)
        let entry = u64::from_le_bytes(elf[24..32].try_into().unwrap());
        assert!(entry > 0x400000);

        // Total size = 64 (ELF header) + 56 (program header) + code
        assert!(elf.len() >= 120);
    }

    #[test]
    fn test_hello_world_syscalls() {
        let code = generate_hello_world();

        // Verify syscall instructions are present (0x0F 0x05)
        let mut syscall_count = 0;
        for i in 0..code.len() - 1 {
            if code[i] == 0x0F && code[i + 1] == 0x05 {
                syscall_count += 1;
            }
        }
        // Should have 2 syscalls: write and exit
        assert_eq!(syscall_count, 2);
    }
}
