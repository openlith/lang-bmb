//! # BMB - Bare-Metal-Banter
//!
//! > "Omission is guessing, and guessing is error."
//!
//! A contract-first programming language designed for AI code generation.
//!
//! ## Verification Levels
//!
//! | Level | Name   | Guarantee              |
//! |-------|--------|------------------------|
//! | 0     | Stone  | Parsing success        |
//! | 1     | Bronze | Type safety            |
//! | 2     | Silver | Contract verification  |

pub mod ai;
pub mod ast;
pub mod contracts;
pub mod codegen;
pub mod parser;
pub mod types;

use thiserror::Error;

/// BMB compilation error types
#[derive(Error, Debug)]
pub enum BmbError {
    #[error("Parse error at {line}:{column}: {message}")]
    ParseError {
        line: usize,
        column: usize,
        message: String,
    },

    #[error("Type error: {message}")]
    TypeError { message: String },

    #[error("Contract error: {message}")]
    ContractError { message: String },

    #[error("Codegen error: {message}")]
    CodegenError { message: String },
}

/// Result type for BMB operations
pub type Result<T> = std::result::Result<T, BmbError>;

/// Verification level achieved during compilation
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VerificationLevel {
    /// Level 0: Parsing succeeded
    Stone = 0,
    /// Level 1: Type checking passed
    Bronze = 1,
    /// Level 2: Contract verification passed
    Silver = 2,
}

impl std::fmt::Display for VerificationLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationLevel::Stone => write!(f, "Stone (Level 0)"),
            VerificationLevel::Bronze => write!(f, "Bronze (Level 1)"),
            VerificationLevel::Silver => write!(f, "Silver (Level 2)"),
        }
    }
}

/// Compile BMB source code to WebAssembly
///
/// # Arguments
///
/// * `source` - The BMB source code to compile
///
/// # Returns
///
/// A tuple of (wasm_binary, verification_level)
pub fn compile(source: &str) -> Result<(Vec<u8>, VerificationLevel)> {
    // Phase 1: Parse
    let ast = parser::parse(source)?;

    // Phase 2: Type check
    let typed_ast = types::typecheck(&ast)?;

    // Phase 3: Contract check
    let verified_ast = contracts::verify(&typed_ast)?;

    // Phase 4: Generate Wasm
    let wasm = codegen::generate(&verified_ast)?;

    Ok((wasm, VerificationLevel::Silver))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_level_ordering() {
        assert!(VerificationLevel::Stone < VerificationLevel::Bronze);
        assert!(VerificationLevel::Bronze < VerificationLevel::Silver);
    }

    #[test]
    fn test_verification_level_display() {
        assert_eq!(VerificationLevel::Stone.to_string(), "Stone (Level 0)");
        assert_eq!(VerificationLevel::Bronze.to_string(), "Bronze (Level 1)");
        assert_eq!(VerificationLevel::Silver.to_string(), "Silver (Level 2)");
    }
}
