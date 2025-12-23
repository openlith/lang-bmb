//! x64 Instruction Encoding
//!
//! Direct machine code generation for x64 instructions.
//! No external assembler dependency.
//!
//! ## Instruction Format
//!
//! ```text
//! [Legacy Prefix] [REX] [Opcode] [ModR/M] [SIB] [Disp] [Imm]
//! ```

use super::registers::{Reg32, Reg64};

/// Machine code buffer for emitting instructions
#[derive(Debug, Default)]
pub struct CodeBuffer {
    code: Vec<u8>,
}

impl CodeBuffer {
    pub fn new() -> Self {
        Self { code: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            code: Vec::with_capacity(capacity),
        }
    }

    /// Get current code offset
    #[inline]
    pub fn offset(&self) -> usize {
        self.code.len()
    }

    /// Emit a single byte
    #[inline]
    pub fn emit(&mut self, byte: u8) {
        self.code.push(byte);
    }

    /// Emit multiple bytes
    #[inline]
    pub fn emit_bytes(&mut self, bytes: &[u8]) {
        self.code.extend_from_slice(bytes);
    }

    /// Emit a 32-bit little-endian value
    #[inline]
    pub fn emit_u32(&mut self, value: u32) {
        self.code.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit a 64-bit little-endian value
    #[inline]
    pub fn emit_u64(&mut self, value: u64) {
        self.code.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit a signed 32-bit little-endian value
    #[inline]
    pub fn emit_i32(&mut self, value: i32) {
        self.code.extend_from_slice(&value.to_le_bytes());
    }

    /// Patch a 32-bit value at the given offset
    pub fn patch_i32(&mut self, offset: usize, value: i32) {
        let bytes = value.to_le_bytes();
        self.code[offset..offset + 4].copy_from_slice(&bytes);
    }

    /// Get the generated code
    pub fn code(&self) -> &[u8] {
        &self.code
    }

    /// Get mutable access to the code buffer for patching
    pub fn code_mut(&mut self) -> &mut [u8] {
        &mut self.code
    }

    /// Take ownership of the generated code
    pub fn into_code(self) -> Vec<u8> {
        self.code
    }
}

/// REX prefix builder
#[derive(Debug, Clone, Copy, Default)]
pub struct Rex {
    w: bool, // 64-bit operand size
    r: bool, // ModR/M reg extension
    x: bool, // SIB index extension
    b: bool, // ModR/M r/m or SIB base extension
}

impl Rex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Set W bit (64-bit operand size)
    pub fn w(mut self) -> Self {
        self.w = true;
        self
    }

    /// Set R bit (reg field extension for r8-r15)
    pub fn r(mut self) -> Self {
        self.r = true;
        self
    }

    /// Set B bit (r/m or base field extension for r8-r15)
    pub fn b(mut self) -> Self {
        self.b = true;
        self
    }

    /// Check if REX prefix is needed
    pub fn is_needed(&self) -> bool {
        self.w || self.r || self.x || self.b
    }

    /// Encode to byte (0x40-0x4F)
    pub fn encode(&self) -> u8 {
        0x40 | ((self.w as u8) << 3)
            | ((self.r as u8) << 2)
            | ((self.x as u8) << 1)
            | (self.b as u8)
    }
}

/// ModR/M byte builder
#[derive(Debug, Clone, Copy)]
pub struct ModRM {
    mod_: u8, // 2 bits: addressing mode
    reg: u8,  // 3 bits: register or opcode extension
    rm: u8,   // 3 bits: register or memory operand
}

impl ModRM {
    /// Create ModR/M for register-to-register (mod=11)
    pub fn reg_reg(reg: u8, rm: u8) -> Self {
        Self {
            mod_: 0b11,
            reg: reg & 0x07,
            rm: rm & 0x07,
        }
    }

    /// Create ModR/M for register with opcode extension (mod=11)
    pub fn reg_opext(opext: u8, rm: u8) -> Self {
        Self {
            mod_: 0b11,
            reg: opext & 0x07,
            rm: rm & 0x07,
        }
    }

    /// Encode to byte
    pub fn encode(&self) -> u8 {
        (self.mod_ << 6) | (self.reg << 3) | self.rm
    }
}

/// x64 instruction emitter
impl CodeBuffer {
    // ==================== Data Movement ====================

    /// MOV r64, imm64 (movabs)
    pub fn mov_r64_imm64(&mut self, dst: Reg64, imm: u64) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0xB8 + dst.encoding()); // B8+rd
        self.emit_u64(imm);
    }

    /// MOV r64, imm32 (sign-extended)
    pub fn mov_r64_imm32(&mut self, dst: Reg64, imm: i32) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0xC7); // C7 /0
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
        self.emit_i32(imm);
    }

    /// MOV r32, imm32
    pub fn mov_r32_imm32(&mut self, dst: Reg32, imm: u32) {
        if dst.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0xB8 + dst.encoding()); // B8+rd
        self.emit_u32(imm);
    }

    /// MOV r64, r64
    pub fn mov_r64_r64(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if src.needs_rex_ext() {
            rex = rex.r();
        }
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x89); // 89 /r
        self.emit(ModRM::reg_reg(src.encoding(), dst.encoding()).encode());
    }

    // ==================== Arithmetic ====================

    /// ADD r64, r64
    pub fn add_r64_r64(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if src.needs_rex_ext() {
            rex = rex.r();
        }
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x01); // 01 /r
        self.emit(ModRM::reg_reg(src.encoding(), dst.encoding()).encode());
    }

    /// ADD r64, imm32 (sign-extended)
    pub fn add_r64_imm32(&mut self, dst: Reg64, imm: i32) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x81); // 81 /0
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
        self.emit_i32(imm);
    }

    /// SUB r64, r64
    pub fn sub_r64_r64(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if src.needs_rex_ext() {
            rex = rex.r();
        }
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x29); // 29 /r
        self.emit(ModRM::reg_reg(src.encoding(), dst.encoding()).encode());
    }

    /// SUB r64, imm32 (sign-extended)
    pub fn sub_r64_imm32(&mut self, dst: Reg64, imm: i32) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x81); // 81 /5
        self.emit(ModRM::reg_opext(5, dst.encoding()).encode());
        self.emit_i32(imm);
    }

    /// IMUL r64, r64
    pub fn imul_r64_r64(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.r();
        }
        if src.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x0F);
        self.emit(0xAF); // 0F AF /r
        self.emit(ModRM::reg_reg(dst.encoding(), src.encoding()).encode());
    }

    /// CQO (sign-extend RAX into RDX:RAX for division)
    pub fn cqo(&mut self) {
        self.emit(Rex::new().w().encode());
        self.emit(0x99);
    }

    /// IDIV r64 (signed divide RDX:RAX by r64, quotient in RAX, remainder in RDX)
    pub fn idiv_r64(&mut self, divisor: Reg64) {
        let mut rex = Rex::new().w();
        if divisor.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0xF7); // F7 /7
        self.emit(ModRM::reg_opext(7, divisor.encoding()).encode());
    }

    // ==================== Comparison ====================

    /// CMP r64, r64
    pub fn cmp_r64_r64(&mut self, left: Reg64, right: Reg64) {
        let mut rex = Rex::new().w();
        if right.needs_rex_ext() {
            rex = rex.r();
        }
        if left.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x39); // 39 /r
        self.emit(ModRM::reg_reg(right.encoding(), left.encoding()).encode());
    }

    /// CMP r64, imm32
    pub fn cmp_r64_imm32(&mut self, left: Reg64, imm: i32) {
        let mut rex = Rex::new().w();
        if left.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x81); // 81 /7
        self.emit(ModRM::reg_opext(7, left.encoding()).encode());
        self.emit_i32(imm);
    }

    /// SETE r8 (set byte if equal)
    pub fn sete(&mut self, dst: Reg64) {
        if dst.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x0F);
        self.emit(0x94); // 0F 94 /0
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
    }

    /// SETNE r8 (set byte if not equal)
    pub fn setne(&mut self, dst: Reg64) {
        if dst.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x0F);
        self.emit(0x95);
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
    }

    /// SETL r8 (set byte if less, signed)
    pub fn setl(&mut self, dst: Reg64) {
        if dst.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x0F);
        self.emit(0x9C);
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
    }

    /// SETLE r8 (set byte if less or equal, signed)
    pub fn setle(&mut self, dst: Reg64) {
        if dst.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x0F);
        self.emit(0x9E);
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
    }

    /// SETG r8 (set byte if greater, signed)
    pub fn setg(&mut self, dst: Reg64) {
        if dst.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x0F);
        self.emit(0x9F);
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
    }

    /// SETGE r8 (set byte if greater or equal, signed)
    pub fn setge(&mut self, dst: Reg64) {
        if dst.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x0F);
        self.emit(0x9D);
        self.emit(ModRM::reg_opext(0, dst.encoding()).encode());
    }

    /// MOVZX r64, r8 (zero-extend byte to 64-bit)
    pub fn movzx_r64_r8(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.r();
        }
        if src.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x0F);
        self.emit(0xB6); // 0F B6 /r
        self.emit(ModRM::reg_reg(dst.encoding(), src.encoding()).encode());
    }

    // ==================== Stack Operations ====================

    /// PUSH r64
    pub fn push_r64(&mut self, reg: Reg64) {
        if reg.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x50 + reg.encoding()); // 50+rd
    }

    /// POP r64
    pub fn pop_r64(&mut self, reg: Reg64) {
        if reg.needs_rex_ext() {
            self.emit(Rex::new().b().encode());
        }
        self.emit(0x58 + reg.encoding()); // 58+rd
    }

    // ==================== Control Flow ====================

    /// RET
    pub fn ret(&mut self) {
        self.emit(0xC3);
    }

    /// JMP rel32 (near jump, returns offset of the displacement for patching)
    pub fn jmp_rel32(&mut self) -> usize {
        self.emit(0xE9); // E9 cd
        let offset = self.offset();
        self.emit_i32(0); // placeholder
        offset
    }

    /// JE rel32 (jump if equal, returns offset of the displacement)
    pub fn je_rel32(&mut self) -> usize {
        self.emit(0x0F);
        self.emit(0x84); // 0F 84 cd
        let offset = self.offset();
        self.emit_i32(0);
        offset
    }

    /// JNE rel32 (jump if not equal)
    pub fn jne_rel32(&mut self) -> usize {
        self.emit(0x0F);
        self.emit(0x85);
        let offset = self.offset();
        self.emit_i32(0);
        offset
    }

    /// CALL rel32 (near call, returns offset of the displacement)
    pub fn call_rel32(&mut self) -> usize {
        self.emit(0xE8); // E8 cd
        let offset = self.offset();
        self.emit_i32(0);
        offset
    }

    // ==================== System ====================

    /// SYSCALL
    pub fn syscall(&mut self) {
        self.emit(0x0F);
        self.emit(0x05);
    }

    // ==================== Bitwise Operations ====================

    /// XOR r64, r64 (often used to zero a register)
    pub fn xor_r64_r64(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if src.needs_rex_ext() {
            rex = rex.r();
        }
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x31); // 31 /r
        self.emit(ModRM::reg_reg(src.encoding(), dst.encoding()).encode());
    }

    /// AND r64, r64
    pub fn and_r64_r64(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if src.needs_rex_ext() {
            rex = rex.r();
        }
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x21); // 21 /r
        self.emit(ModRM::reg_reg(src.encoding(), dst.encoding()).encode());
    }

    /// OR r64, r64
    pub fn or_r64_r64(&mut self, dst: Reg64, src: Reg64) {
        let mut rex = Rex::new().w();
        if src.needs_rex_ext() {
            rex = rex.r();
        }
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0x09); // 09 /r
        self.emit(ModRM::reg_reg(src.encoding(), dst.encoding()).encode());
    }

    /// SHL r64, CL (shift left by value in CL register)
    pub fn shl_r64_cl(&mut self, dst: Reg64) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0xD3); // D3 /4
        self.emit(ModRM::reg_reg(4, dst.encoding()).encode()); // /4 for SHL
    }

    /// SAR r64, CL (arithmetic shift right by value in CL register)
    pub fn sar_r64_cl(&mut self, dst: Reg64) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0xD3); // D3 /7
        self.emit(ModRM::reg_reg(7, dst.encoding()).encode()); // /7 for SAR
    }

    /// NOT r64 (bitwise NOT, one's complement)
    pub fn not_r64(&mut self, dst: Reg64) {
        let mut rex = Rex::new().w();
        if dst.needs_rex_ext() {
            rex = rex.b();
        }
        self.emit(rex.encode());
        self.emit(0xF7); // F7 /2
        self.emit(ModRM::reg_reg(2, dst.encoding()).encode()); // /2 for NOT
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mov_r64_imm64() {
        let mut buf = CodeBuffer::new();
        buf.mov_r64_imm64(Reg64::RAX, 42);
        // REX.W + B8 + imm64
        assert_eq!(&buf.code()[0..2], &[0x48, 0xB8]);
    }

    #[test]
    fn test_mov_r64_r64() {
        let mut buf = CodeBuffer::new();
        buf.mov_r64_r64(Reg64::RBX, Reg64::RAX);
        // REX.W + 89 + ModR/M(11 000 011)
        assert_eq!(buf.code(), &[0x48, 0x89, 0xC3]);
    }

    #[test]
    fn test_add_r64_r64() {
        let mut buf = CodeBuffer::new();
        buf.add_r64_r64(Reg64::RAX, Reg64::RBX);
        // REX.W + 01 + ModR/M(11 011 000)
        assert_eq!(buf.code(), &[0x48, 0x01, 0xD8]);
    }

    #[test]
    fn test_syscall() {
        let mut buf = CodeBuffer::new();
        buf.syscall();
        assert_eq!(buf.code(), &[0x0F, 0x05]);
    }

    #[test]
    fn test_ret() {
        let mut buf = CodeBuffer::new();
        buf.ret();
        assert_eq!(buf.code(), &[0xC3]);
    }

    #[test]
    fn test_push_pop() {
        let mut buf = CodeBuffer::new();
        buf.push_r64(Reg64::RBP);
        buf.pop_r64(Reg64::RBP);
        assert_eq!(buf.code(), &[0x55, 0x5D]);
    }

    #[test]
    fn test_extended_registers() {
        let mut buf = CodeBuffer::new();
        buf.mov_r64_r64(Reg64::R8, Reg64::R15);
        // REX.WRB + 89 + ModR/M
        assert_eq!(buf.code()[0], 0x4D); // REX.W + REX.R + REX.B
    }
}
