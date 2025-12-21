//! ARM64 (AArch64) Register Definitions
//!
//! Defines the 64-bit general-purpose registers and encoding for ARM64.

/// ARM64 General-Purpose Registers (64-bit X registers)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Reg64 {
    // General-purpose registers
    X0 = 0,
    X1 = 1,
    X2 = 2,
    X3 = 3,
    X4 = 4,
    X5 = 5,
    X6 = 6,
    X7 = 7,
    X8 = 8,
    X9 = 9,
    X10 = 10,
    X11 = 11,
    X12 = 12,
    X13 = 13,
    X14 = 14,
    X15 = 15,
    X16 = 16,
    X17 = 17,
    X18 = 18,
    X19 = 19,
    X20 = 20,
    X21 = 21,
    X22 = 22,
    X23 = 23,
    X24 = 24,
    X25 = 25,
    X26 = 26,
    X27 = 27,
    X28 = 28,
    X29 = 29, // Frame Pointer (FP)
    X30 = 30, // Link Register (LR)
    // Note: X31 is either SP or XZR depending on context
}

/// 32-bit W registers (low 32 bits of X registers)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Reg32 {
    W0 = 0,
    W1 = 1,
    W2 = 2,
    W3 = 3,
    W4 = 4,
    W5 = 5,
    W6 = 6,
    W7 = 7,
    W8 = 8,
    W9 = 9,
    W10 = 10,
    W11 = 11,
    W12 = 12,
    W13 = 13,
    W14 = 14,
    W15 = 15,
    W16 = 16,
    W17 = 17,
    W18 = 18,
    W19 = 19,
    W20 = 20,
    W21 = 21,
    W22 = 22,
    W23 = 23,
    W24 = 24,
    W25 = 25,
    W26 = 26,
    W27 = 27,
    W28 = 28,
    W29 = 29, // Frame Pointer (WFP)
    W30 = 30, // Link Register (WLR)
}

impl Reg64 {
    /// Get the register encoding (0-30)
    pub fn encoding(self) -> u8 {
        self as u8
    }

    /// Check if this is a callee-saved register
    pub fn is_callee_saved(self) -> bool {
        matches!(
            self,
            Reg64::X19
                | Reg64::X20
                | Reg64::X21
                | Reg64::X22
                | Reg64::X23
                | Reg64::X24
                | Reg64::X25
                | Reg64::X26
                | Reg64::X27
                | Reg64::X28
                | Reg64::X29
                | Reg64::X30
        )
    }

    /// Check if this is an argument register
    pub fn is_argument(self) -> bool {
        matches!(
            self,
            Reg64::X0
                | Reg64::X1
                | Reg64::X2
                | Reg64::X3
                | Reg64::X4
                | Reg64::X5
                | Reg64::X6
                | Reg64::X7
        )
    }

    /// Get the corresponding 32-bit register
    pub fn to_32bit(self) -> Reg32 {
        // Safe because Reg32 has same encoding values
        unsafe { std::mem::transmute(self as u8) }
    }
}

impl Reg32 {
    /// Get the register encoding (0-30)
    pub fn encoding(self) -> u8 {
        self as u8
    }

    /// Get the corresponding 64-bit register
    pub fn to_64bit(self) -> Reg64 {
        // Safe because Reg64 has same encoding values
        unsafe { std::mem::transmute(self as u8) }
    }
}

/// Special register constants
pub mod special {
    /// Stack Pointer register number (when X31 is used as SP)
    pub const SP: u8 = 31;

    /// Zero Register number (when X31 is used as XZR)
    pub const XZR: u8 = 31;

    /// Frame Pointer (alias for X29)
    pub const FP: u8 = 29;

    /// Link Register (alias for X30)
    pub const LR: u8 = 30;
}

/// ARM64 AAPCS64 calling convention
pub mod calling_convention {
    use super::Reg64;

    /// Argument registers (X0-X7)
    pub const ARGUMENT_REGS: [Reg64; 8] = [
        Reg64::X0,
        Reg64::X1,
        Reg64::X2,
        Reg64::X3,
        Reg64::X4,
        Reg64::X5,
        Reg64::X6,
        Reg64::X7,
    ];

    /// Return value register
    pub const RETURN_REG: Reg64 = Reg64::X0;

    /// Callee-saved registers (X19-X28, FP, LR)
    pub const CALLEE_SAVED: [Reg64; 12] = [
        Reg64::X19,
        Reg64::X20,
        Reg64::X21,
        Reg64::X22,
        Reg64::X23,
        Reg64::X24,
        Reg64::X25,
        Reg64::X26,
        Reg64::X27,
        Reg64::X28,
        Reg64::X29, // FP
        Reg64::X30, // LR
    ];

    /// Caller-saved (scratch) registers
    pub const CALLER_SAVED: [Reg64; 18] = [
        Reg64::X0,
        Reg64::X1,
        Reg64::X2,
        Reg64::X3,
        Reg64::X4,
        Reg64::X5,
        Reg64::X6,
        Reg64::X7,
        Reg64::X8,
        Reg64::X9,
        Reg64::X10,
        Reg64::X11,
        Reg64::X12,
        Reg64::X13,
        Reg64::X14,
        Reg64::X15,
        Reg64::X16,
        Reg64::X17,
    ];

    /// Indirect result location register (X8)
    pub const INDIRECT_RESULT: Reg64 = Reg64::X8;

    /// Intra-procedure-call scratch registers (X16-X17)
    pub const IP0: Reg64 = Reg64::X16;
    pub const IP1: Reg64 = Reg64::X17;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_encoding() {
        assert_eq!(Reg64::X0.encoding(), 0);
        assert_eq!(Reg64::X15.encoding(), 15);
        assert_eq!(Reg64::X30.encoding(), 30);
    }

    #[test]
    fn test_callee_saved() {
        assert!(Reg64::X19.is_callee_saved());
        assert!(Reg64::X29.is_callee_saved());
        assert!(Reg64::X30.is_callee_saved());
        assert!(!Reg64::X0.is_callee_saved());
        assert!(!Reg64::X16.is_callee_saved());
    }

    #[test]
    fn test_argument_registers() {
        assert!(Reg64::X0.is_argument());
        assert!(Reg64::X7.is_argument());
        assert!(!Reg64::X8.is_argument());
        assert!(!Reg64::X19.is_argument());
    }

    #[test]
    fn test_register_conversion() {
        assert_eq!(Reg64::X5.to_32bit(), Reg32::W5);
        assert_eq!(Reg32::W10.to_64bit(), Reg64::X10);
    }
}
