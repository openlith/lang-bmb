//! ARM64 (AArch64) Instruction Encoding
//!
//! Encodes ARM64 instructions into 32-bit machine code.
//! All ARM64 instructions are exactly 4 bytes.

use super::registers::{Reg32, Reg64};

/// Encode a 32-bit instruction and append to buffer
fn emit(buf: &mut Vec<u8>, insn: u32) {
    buf.extend_from_slice(&insn.to_le_bytes());
}

// =============================================================================
// Data Processing - Immediate
// =============================================================================

/// MOV (immediate) - Move wide immediate to register (MOVZ)
/// Encodes: MOVZ Xd, #imm16, LSL #shift
pub fn movz_x(buf: &mut Vec<u8>, rd: Reg64, imm16: u16, shift: u8) {
    // MOVZ (64-bit): 1 10 100101 hw imm16 Rd
    let hw = (shift / 16) as u32;
    let insn = 0xD2800000 | (hw << 21) | ((imm16 as u32) << 5) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// MOV (immediate) - Move wide immediate to 32-bit register (MOVZ)
pub fn movz_w(buf: &mut Vec<u8>, rd: Reg32, imm16: u16, shift: u8) {
    // MOVZ (32-bit): 0 10 100101 hw imm16 Rd
    let hw = (shift / 16) as u32;
    let insn = 0x52800000 | (hw << 21) | ((imm16 as u32) << 5) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// MOVK - Move wide with keep (for building larger immediates)
pub fn movk_x(buf: &mut Vec<u8>, rd: Reg64, imm16: u16, shift: u8) {
    // MOVK (64-bit): 1 11 100101 hw imm16 Rd
    let hw = (shift / 16) as u32;
    let insn = 0xF2800000 | (hw << 21) | ((imm16 as u32) << 5) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// ADD (immediate) - Add immediate to register
/// Encodes: ADD Xd, Xn, #imm12
pub fn add_imm_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, imm12: u16) {
    // ADD (64-bit): 1 00 10001 shift imm12 Rn Rd
    let insn =
        0x91000000 | ((imm12 as u32) << 10) | ((rn.encoding() as u32) << 5) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// ADD (immediate) - Add immediate to 32-bit register
pub fn add_imm_w(buf: &mut Vec<u8>, rd: Reg32, rn: Reg32, imm12: u16) {
    // ADD (32-bit): 0 00 10001 shift imm12 Rn Rd
    let insn =
        0x11000000 | ((imm12 as u32) << 10) | ((rn.encoding() as u32) << 5) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// SUB (immediate) - Subtract immediate from register
pub fn sub_imm_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, imm12: u16) {
    // SUB (64-bit): 1 10 10001 shift imm12 Rn Rd
    let insn =
        0xD1000000 | ((imm12 as u32) << 10) | ((rn.encoding() as u32) << 5) | (rd.encoding() as u32);
    emit(buf, insn);
}

// =============================================================================
// Data Processing - Register
// =============================================================================

/// MOV (register) - Move register to register (alias for ORR)
/// Encodes: ORR Xd, XZR, Xm
pub fn mov_x(buf: &mut Vec<u8>, rd: Reg64, rm: Reg64) {
    // ORR Xd, XZR, Xm: 1 01 01010 shift 0 Xm imm6 XZR Xd
    let insn = 0xAA0003E0 | ((rm.encoding() as u32) << 16) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// MOV (register) - Move 32-bit register to register
pub fn mov_w(buf: &mut Vec<u8>, rd: Reg32, rm: Reg32) {
    // ORR Wd, WZR, Wm: 0 01 01010 shift 0 Wm imm6 WZR Wd
    let insn = 0x2A0003E0 | ((rm.encoding() as u32) << 16) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// ADD (register) - Add two registers
/// Encodes: ADD Xd, Xn, Xm
pub fn add_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, rm: Reg64) {
    // ADD (shifted): 1 00 01011 shift 0 Rm imm6 Rn Rd
    let insn = 0x8B000000
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// ADD (register) - Add two 32-bit registers
pub fn add_w(buf: &mut Vec<u8>, rd: Reg32, rn: Reg32, rm: Reg32) {
    // ADD (shifted): 0 00 01011 shift 0 Rm imm6 Rn Rd
    let insn = 0x0B000000
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// SUB (register) - Subtract two registers
pub fn sub_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, rm: Reg64) {
    // SUB (shifted): 1 10 01011 shift 0 Rm imm6 Rn Rd
    let insn = 0xCB000000
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// SUB (register) - Subtract two 32-bit registers
pub fn sub_w(buf: &mut Vec<u8>, rd: Reg32, rn: Reg32, rm: Reg32) {
    // SUB (shifted): 0 10 01011 shift 0 Rm imm6 Rn Rd
    let insn = 0x4B000000
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// MUL (register) - Multiply two registers
/// Encodes: MADD Xd, Xn, Xm, XZR
pub fn mul_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, rm: Reg64) {
    // MADD: 1 00 11011 000 Rm 0 11111 Rn Rd (Ra = XZR = 31)
    let insn = 0x9B007C00
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// MUL (register) - Multiply two 32-bit registers
pub fn mul_w(buf: &mut Vec<u8>, rd: Reg32, rn: Reg32, rm: Reg32) {
    // MADD: 0 00 11011 000 Rm 0 11111 Rn Rd (Ra = WZR = 31)
    let insn = 0x1B007C00
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// SDIV - Signed divide
pub fn sdiv_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, rm: Reg64) {
    // SDIV: 1 00 11010110 Rm 00001 1 Rn Rd
    let insn = 0x9AC00C00
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// SDIV - Signed divide (32-bit)
pub fn sdiv_w(buf: &mut Vec<u8>, rd: Reg32, rn: Reg32, rm: Reg32) {
    // SDIV: 0 00 11010110 Rm 00001 1 Rn Rd
    let insn = 0x1AC00C00
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// UDIV - Unsigned divide
pub fn udiv_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, rm: Reg64) {
    // UDIV: 1 00 11010110 Rm 00001 0 Rn Rd
    let insn = 0x9AC00800
        | ((rm.encoding() as u32) << 16)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

/// MSUB - Multiply-subtract (for modulo: a - (a/b)*b)
pub fn msub_x(buf: &mut Vec<u8>, rd: Reg64, rn: Reg64, rm: Reg64, ra: Reg64) {
    // MSUB: 1 00 11011 000 Rm 1 Ra Rn Rd
    let insn = 0x9B008000
        | ((rm.encoding() as u32) << 16)
        | ((ra.encoding() as u32) << 10)
        | ((rn.encoding() as u32) << 5)
        | (rd.encoding() as u32);
    emit(buf, insn);
}

// =============================================================================
// Comparison and Conditionals
// =============================================================================

/// CMP (register) - Compare two registers (alias for SUBS with Xd = XZR)
pub fn cmp_x(buf: &mut Vec<u8>, rn: Reg64, rm: Reg64) {
    // SUBS XZR, Xn, Xm: 1 11 01011 shift 0 Rm imm6 Rn 11111
    let insn =
        0xEB00001F | ((rm.encoding() as u32) << 16) | ((rn.encoding() as u32) << 5);
    emit(buf, insn);
}

/// CMP (immediate) - Compare register with immediate
pub fn cmp_imm_x(buf: &mut Vec<u8>, rn: Reg64, imm12: u16) {
    // SUBS XZR, Xn, #imm12: 1 11 10001 shift imm12 Rn 11111
    let insn = 0xF100001F | ((imm12 as u32) << 10) | ((rn.encoding() as u32) << 5);
    emit(buf, insn);
}

/// CSET - Conditional set (set 1 if condition, else 0)
/// Encodes: CSINC Xd, XZR, XZR, invert(cond)
pub fn cset_x(buf: &mut Vec<u8>, rd: Reg64, cond: Condition) {
    // CSINC Xd, XZR, XZR, invert(cond)
    let inv_cond = cond.invert();
    let insn = 0x9A9F07E0 | ((inv_cond as u32) << 12) | (rd.encoding() as u32);
    emit(buf, insn);
}

/// ARM64 condition codes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Condition {
    EQ = 0b0000, // Equal
    NE = 0b0001, // Not equal
    CS = 0b0010, // Carry set / unsigned >=
    CC = 0b0011, // Carry clear / unsigned <
    MI = 0b0100, // Minus / negative
    PL = 0b0101, // Plus / positive or zero
    VS = 0b0110, // Overflow
    VC = 0b0111, // No overflow
    HI = 0b1000, // Unsigned >
    LS = 0b1001, // Unsigned <=
    GE = 0b1010, // Signed >=
    LT = 0b1011, // Signed <
    GT = 0b1100, // Signed >
    LE = 0b1101, // Signed <=
    AL = 0b1110, // Always
    NV = 0b1111, // Never (reserved)
}

impl Condition {
    /// Get the inverted condition
    pub fn invert(self) -> Condition {
        // Toggle the least significant bit
        unsafe { std::mem::transmute((self as u8) ^ 1) }
    }
}

// =============================================================================
// Branch Instructions
// =============================================================================

/// B - Unconditional branch (PC-relative)
/// offset is in bytes and must be 4-byte aligned
pub fn b(buf: &mut Vec<u8>, offset: i32) {
    // B: 000101 imm26
    let imm26 = ((offset >> 2) as u32) & 0x03FFFFFF;
    let insn = 0x14000000 | imm26;
    emit(buf, insn);
}

/// B.cond - Conditional branch (PC-relative)
pub fn b_cond(buf: &mut Vec<u8>, cond: Condition, offset: i32) {
    // B.cond: 01010100 imm19 0 cond
    let imm19 = ((offset >> 2) as u32) & 0x7FFFF;
    let insn = 0x54000000 | (imm19 << 5) | (cond as u32);
    emit(buf, insn);
}

/// BL - Branch with link (function call)
pub fn bl(buf: &mut Vec<u8>, offset: i32) {
    // BL: 100101 imm26
    let imm26 = ((offset >> 2) as u32) & 0x03FFFFFF;
    let insn = 0x94000000 | imm26;
    emit(buf, insn);
}

/// BLR - Branch with link to register (indirect call)
pub fn blr(buf: &mut Vec<u8>, rn: Reg64) {
    // BLR: 1101011 0001 11111 000000 Rn 00000
    let insn = 0xD63F0000 | ((rn.encoding() as u32) << 5);
    emit(buf, insn);
}

/// RET - Return from subroutine
/// Default: RET X30 (link register)
pub fn ret(buf: &mut Vec<u8>) {
    ret_rn(buf, Reg64::X30);
}

/// RET - Return from subroutine with specified register
pub fn ret_rn(buf: &mut Vec<u8>, rn: Reg64) {
    // RET: 1101011 0010 11111 000000 Rn 00000
    let insn = 0xD65F0000 | ((rn.encoding() as u32) << 5);
    emit(buf, insn);
}

/// CBZ - Compare and branch if zero
pub fn cbz_x(buf: &mut Vec<u8>, rt: Reg64, offset: i32) {
    // CBZ (64-bit): 1 011010 0 imm19 Rt
    let imm19 = ((offset >> 2) as u32) & 0x7FFFF;
    let insn = 0xB4000000 | (imm19 << 5) | (rt.encoding() as u32);
    emit(buf, insn);
}

/// CBNZ - Compare and branch if not zero
pub fn cbnz_x(buf: &mut Vec<u8>, rt: Reg64, offset: i32) {
    // CBNZ (64-bit): 1 011010 1 imm19 Rt
    let imm19 = ((offset >> 2) as u32) & 0x7FFFF;
    let insn = 0xB5000000 | (imm19 << 5) | (rt.encoding() as u32);
    emit(buf, insn);
}

// =============================================================================
// Load/Store Instructions
// =============================================================================

/// LDR (immediate, unsigned offset) - Load register
/// Encodes: LDR Xt, [Xn, #offset]
pub fn ldr_x_imm(buf: &mut Vec<u8>, rt: Reg64, rn: Reg64, offset: u16) {
    // LDR (64-bit): 11 111 0 01 01 imm12 Rn Rt
    let imm12 = (offset / 8) as u32; // Scale by 8 for 64-bit
    let insn = 0xF9400000 | (imm12 << 10) | ((rn.encoding() as u32) << 5) | (rt.encoding() as u32);
    emit(buf, insn);
}

/// STR (immediate, unsigned offset) - Store register
pub fn str_x_imm(buf: &mut Vec<u8>, rt: Reg64, rn: Reg64, offset: u16) {
    // STR (64-bit): 11 111 0 01 00 imm12 Rn Rt
    let imm12 = (offset / 8) as u32; // Scale by 8 for 64-bit
    let insn = 0xF9000000 | (imm12 << 10) | ((rn.encoding() as u32) << 5) | (rt.encoding() as u32);
    emit(buf, insn);
}

/// STP - Store pair of registers (pre-index)
/// Encodes: STP Xt1, Xt2, [Xn, #offset]!
pub fn stp_pre_x(buf: &mut Vec<u8>, rt1: Reg64, rt2: Reg64, rn: Reg64, offset: i16) {
    // STP (pre-index, 64-bit): 10 101 0 011 imm7 Rt2 Rn Rt
    let imm7 = ((offset / 8) as u32) & 0x7F;
    let insn = 0xA9800000
        | (imm7 << 15)
        | ((rt2.encoding() as u32) << 10)
        | ((rn.encoding() as u32) << 5)
        | (rt1.encoding() as u32);
    emit(buf, insn);
}

/// LDP - Load pair of registers (post-index)
/// Encodes: LDP Xt1, Xt2, [Xn], #offset
pub fn ldp_post_x(buf: &mut Vec<u8>, rt1: Reg64, rt2: Reg64, rn: Reg64, offset: i16) {
    // LDP (post-index, 64-bit): 10 101 0 001 imm7 Rt2 Rn Rt
    let imm7 = ((offset / 8) as u32) & 0x7F;
    let insn = 0xA8C00000
        | (imm7 << 15)
        | ((rt2.encoding() as u32) << 10)
        | ((rn.encoding() as u32) << 5)
        | (rt1.encoding() as u32);
    emit(buf, insn);
}

// =============================================================================
// System Instructions
// =============================================================================

/// SVC - Supervisor call (system call)
pub fn svc(buf: &mut Vec<u8>, imm16: u16) {
    // SVC: 11010100 000 imm16 00001
    let insn = 0xD4000001 | ((imm16 as u32) << 5);
    emit(buf, insn);
}

/// NOP - No operation
pub fn nop(buf: &mut Vec<u8>) {
    // NOP: 11010101 00000011 00100000 00011111
    emit(buf, 0xD503201F);
}

/// BRK - Breakpoint
pub fn brk(buf: &mut Vec<u8>, imm16: u16) {
    // BRK: 11010100 001 imm16 00000
    let insn = 0xD4200000 | ((imm16 as u32) << 5);
    emit(buf, insn);
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Load a 64-bit immediate value into a register
/// Uses MOVZ + MOVK sequence
pub fn load_imm64(buf: &mut Vec<u8>, rd: Reg64, value: u64) {
    if value == 0 {
        // XOR with itself using ORR Xd, XZR, XZR
        let insn = 0xAA1F03E0 | (rd.encoding() as u32);
        emit(buf, insn);
        return;
    }

    let mut first = true;
    for shift in (0..64).step_by(16) {
        let imm16 = ((value >> shift) & 0xFFFF) as u16;
        if imm16 != 0 || (first && shift == 48) {
            if first {
                movz_x(buf, rd, imm16, shift as u8);
                first = false;
            } else {
                movk_x(buf, rd, imm16, shift as u8);
            }
        }
    }

    // If all parts were zero except we need at least one instruction
    if first {
        movz_x(buf, rd, 0, 0);
    }
}

/// Load a 32-bit immediate value into a register
pub fn load_imm32(buf: &mut Vec<u8>, rd: Reg32, value: u32) {
    if value == 0 {
        // MOV Wd, WZR
        let insn = 0x2A1F03E0 | (rd.encoding() as u32);
        emit(buf, insn);
        return;
    }

    let low = (value & 0xFFFF) as u16;
    let high = ((value >> 16) & 0xFFFF) as u16;

    if high == 0 {
        movz_w(buf, rd, low, 0);
    } else if low == 0 {
        movz_w(buf, rd, high, 16);
    } else {
        movz_w(buf, rd, low, 0);
        // MOVK for 32-bit
        let insn = 0x72A00000 | ((high as u32) << 5) | (rd.encoding() as u32);
        emit(buf, insn);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_movz_x() {
        let mut buf = Vec::new();
        movz_x(&mut buf, Reg64::X0, 42, 0);
        assert_eq!(buf.len(), 4);
        // MOVZ X0, #42 = 0xD2800540
        assert_eq!(
            u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]),
            0xD2800540
        );
    }

    #[test]
    fn test_add_x() {
        let mut buf = Vec::new();
        add_x(&mut buf, Reg64::X0, Reg64::X1, Reg64::X2);
        assert_eq!(buf.len(), 4);
        // ADD X0, X1, X2 = 0x8B020020
        assert_eq!(
            u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]),
            0x8B020020
        );
    }

    #[test]
    fn test_ret() {
        let mut buf = Vec::new();
        ret(&mut buf);
        assert_eq!(buf.len(), 4);
        // RET (X30) = 0xD65F03C0
        assert_eq!(
            u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]),
            0xD65F03C0
        );
    }

    #[test]
    fn test_svc() {
        let mut buf = Vec::new();
        svc(&mut buf, 0);
        assert_eq!(buf.len(), 4);
        // SVC #0 = 0xD4000001
        assert_eq!(
            u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]),
            0xD4000001
        );
    }

    #[test]
    fn test_load_imm64_small() {
        let mut buf = Vec::new();
        load_imm64(&mut buf, Reg64::X0, 42);
        assert_eq!(buf.len(), 4); // Single MOVZ instruction
    }

    #[test]
    fn test_load_imm64_large() {
        let mut buf = Vec::new();
        load_imm64(&mut buf, Reg64::X0, 0x123456789ABCDEF0);
        // Should use MOVZ + 3 MOVK = 4 instructions = 16 bytes
        assert_eq!(buf.len(), 16);
    }

    #[test]
    fn test_condition_invert() {
        assert_eq!(Condition::EQ.invert(), Condition::NE);
        assert_eq!(Condition::NE.invert(), Condition::EQ);
        assert_eq!(Condition::LT.invert(), Condition::GE);
        assert_eq!(Condition::GE.invert(), Condition::LT);
    }
}
