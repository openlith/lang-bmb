//! x64 Register Definitions
//!
//! All 16 general-purpose 64-bit registers with encoding values.
//! Follows System V AMD64 ABI for Linux.

use std::fmt;

/// x64 64-bit general purpose register
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Reg64 {
    RAX = 0,
    RCX = 1,
    RDX = 2,
    RBX = 3,
    RSP = 4,
    RBP = 5,
    RSI = 6,
    RDI = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

impl Reg64 {
    /// Get the 3-bit encoding for ModR/M and SIB bytes
    #[inline]
    pub fn encoding(self) -> u8 {
        (self as u8) & 0x07
    }

    /// Check if this register requires REX.B or REX.R bit
    #[inline]
    pub fn needs_rex_ext(self) -> bool {
        (self as u8) >= 8
    }

    /// Check if this register is callee-saved (System V ABI)
    pub fn is_callee_saved(self) -> bool {
        matches!(
            self,
            Reg64::RBX | Reg64::RBP | Reg64::R12 | Reg64::R13 | Reg64::R14 | Reg64::R15
        )
    }

    /// Check if this register is caller-saved (System V ABI)
    pub fn is_caller_saved(self) -> bool {
        !self.is_callee_saved() && self != Reg64::RSP
    }
}

impl fmt::Display for Reg64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Reg64::RAX => "rax",
            Reg64::RCX => "rcx",
            Reg64::RDX => "rdx",
            Reg64::RBX => "rbx",
            Reg64::RSP => "rsp",
            Reg64::RBP => "rbp",
            Reg64::RSI => "rsi",
            Reg64::RDI => "rdi",
            Reg64::R8 => "r8",
            Reg64::R9 => "r9",
            Reg64::R10 => "r10",
            Reg64::R11 => "r11",
            Reg64::R12 => "r12",
            Reg64::R13 => "r13",
            Reg64::R14 => "r14",
            Reg64::R15 => "r15",
        };
        write!(f, "{}", name)
    }
}

/// x64 32-bit register (lower 32 bits of 64-bit registers)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Reg32 {
    EAX = 0,
    ECX = 1,
    EDX = 2,
    EBX = 3,
    ESP = 4,
    EBP = 5,
    ESI = 6,
    EDI = 7,
    R8D = 8,
    R9D = 9,
    R10D = 10,
    R11D = 11,
    R12D = 12,
    R13D = 13,
    R14D = 14,
    R15D = 15,
}

impl Reg32 {
    #[inline]
    pub fn encoding(self) -> u8 {
        (self as u8) & 0x07
    }

    #[inline]
    pub fn needs_rex_ext(self) -> bool {
        (self as u8) >= 8
    }

    /// Convert to 64-bit register
    pub fn to_reg64(self) -> Reg64 {
        unsafe { std::mem::transmute(self as u8) }
    }
}

impl fmt::Display for Reg32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Reg32::EAX => "eax",
            Reg32::ECX => "ecx",
            Reg32::EDX => "edx",
            Reg32::EBX => "ebx",
            Reg32::ESP => "esp",
            Reg32::EBP => "ebp",
            Reg32::ESI => "esi",
            Reg32::EDI => "edi",
            Reg32::R8D => "r8d",
            Reg32::R9D => "r9d",
            Reg32::R10D => "r10d",
            Reg32::R11D => "r11d",
            Reg32::R12D => "r12d",
            Reg32::R13D => "r13d",
            Reg32::R14D => "r14d",
            Reg32::R15D => "r15d",
        };
        write!(f, "{}", name)
    }
}

/// System V AMD64 ABI argument registers (in order) - Linux
pub const SYSV_ARG_REGS: [Reg64; 6] = [
    Reg64::RDI,
    Reg64::RSI,
    Reg64::RDX,
    Reg64::RCX,
    Reg64::R8,
    Reg64::R9,
];

/// System V AMD64 ABI return register
pub const SYSV_RET_REG: Reg64 = Reg64::RAX;

/// System V AMD64 ABI callee-saved registers
pub const SYSV_CALLEE_SAVED: [Reg64; 6] = [
    Reg64::RBX,
    Reg64::RBP,
    Reg64::R12,
    Reg64::R13,
    Reg64::R14,
    Reg64::R15,
];

/// Windows x64 calling convention argument registers (in order)
pub const WIN64_ARG_REGS: [Reg64; 4] = [Reg64::RCX, Reg64::RDX, Reg64::R8, Reg64::R9];

/// Windows x64 calling convention return register
pub const WIN64_RET_REG: Reg64 = Reg64::RAX;

/// Windows x64 callee-saved registers (non-volatile)
pub const WIN64_CALLEE_SAVED: [Reg64; 7] = [
    Reg64::RBX,
    Reg64::RBP,
    Reg64::RDI,
    Reg64::RSI,
    Reg64::R12,
    Reg64::R13,
    Reg64::R14,
    // R15 is also callee-saved but often used for other purposes
];

/// Scratch registers available for codegen (caller-saved, excluding special purpose)
pub const SCRATCH_REGS: [Reg64; 7] = [
    Reg64::RAX,
    Reg64::RCX,
    Reg64::RDX,
    Reg64::R8,
    Reg64::R9,
    Reg64::R10,
    Reg64::R11,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_encoding() {
        assert_eq!(Reg64::RAX.encoding(), 0);
        assert_eq!(Reg64::RCX.encoding(), 1);
        assert_eq!(Reg64::R8.encoding(), 0);
        assert_eq!(Reg64::R15.encoding(), 7);
    }

    #[test]
    fn test_rex_extension() {
        assert!(!Reg64::RAX.needs_rex_ext());
        assert!(!Reg64::RDI.needs_rex_ext());
        assert!(Reg64::R8.needs_rex_ext());
        assert!(Reg64::R15.needs_rex_ext());
    }

    #[test]
    fn test_callee_saved() {
        assert!(Reg64::RBX.is_callee_saved());
        assert!(Reg64::RBP.is_callee_saved());
        assert!(!Reg64::RAX.is_callee_saved());
        assert!(!Reg64::RDI.is_callee_saved());
    }
}
