//! # BMB - Bare-Metal-Banter
//!
//! > "Omission is guessing, and guessing is error."
//!
//! A contract-first programming language designed for AI code generation.
//!
//! ## Verification Levels
//!
//! | Level | Name   | Guarantee                     |
//! |-------|--------|-------------------------------|
//! | 0     | Stone  | Parsing success               |
//! | 1     | Bronze | Type safety                   |
//! | 2     | Silver | Runtime contract verification |
//! | 3     | Gold   | Static contract proof (SMT)   |

pub mod ai;
pub mod arm64;
pub mod ast;
pub mod codegen;
pub mod contracts;
pub mod error;
pub mod fmt;
pub mod grammar;
pub mod ir;
pub mod lint;
pub mod modules;
pub mod optimize;
pub mod parser;
#[cfg(feature = "smt")]
pub mod smt;
#[cfg(feature = "smt")]
pub use smt::{
    AssertionResult, InvariantResult, NodeVerificationResult, SmtExpr, SmtVar, VerificationResult,
};
#[cfg(feature = "cli")]
pub mod testing;
pub mod types;
pub mod x64;

/// Host interface helpers for WASM runtime environments (v0.13+)
pub mod host;

use thiserror::Error;

pub use error::{Diagnostic, ErrorCode};
pub use modules::{MergedProgram, ModuleEntry, ModuleIndex, ModuleResolver, ResolvedModule};

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

    #[error("Module error: {message}")]
    ModuleError { message: String },

    /// Enhanced diagnostic error with full context
    #[error("{0}")]
    Diagnosed(Diagnostic),
}

impl BmbError {
    /// Convert to diagnostic if available, or create a basic one
    pub fn to_diagnostic(&self) -> Diagnostic {
        match self {
            BmbError::ParseError {
                line,
                column,
                message,
            } => Diagnostic::new(ErrorCode::E002, message.clone())
                .with_span(crate::ast::Span::new(0, 0, *line, *column)),
            BmbError::TypeError { message } => Diagnostic::new(ErrorCode::E100, message.clone()),
            BmbError::ContractError { message } => {
                Diagnostic::new(ErrorCode::E200, message.clone())
            }
            BmbError::CodegenError { message } => Diagnostic::new(ErrorCode::E300, message.clone()),
            BmbError::ModuleError { message } => Diagnostic::new(ErrorCode::E400, message.clone()),
            BmbError::Diagnosed(diag) => diag.clone(),
        }
    }

    /// Format error with source context
    pub fn format_with_source(&self, source: &str) -> String {
        self.to_diagnostic().format_with_source(source)
    }
}

impl From<Diagnostic> for BmbError {
    fn from(diag: Diagnostic) -> Self {
        BmbError::Diagnosed(diag)
    }
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
    /// Level 2: Runtime contract verification passed
    Silver = 2,
    /// Level 3: Static contract proof via SMT solver
    Gold = 3,
}

impl std::fmt::Display for VerificationLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationLevel::Stone => write!(f, "Stone (Level 0)"),
            VerificationLevel::Bronze => write!(f, "Bronze (Level 1)"),
            VerificationLevel::Silver => write!(f, "Silver (Level 2)"),
            VerificationLevel::Gold => write!(f, "Gold (Level 3)"),
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
    compile_with_opt(source, optimize::OptLevel::Basic)
}

/// Compile BMB source code to WebAssembly with specified optimization level
///
/// # Arguments
///
/// * `source` - The BMB source code to compile
/// * `opt_level` - The optimization level to apply
///
/// # Returns
///
/// A tuple of (wasm_binary, verification_level)
pub fn compile_with_opt(
    source: &str,
    opt_level: optimize::OptLevel,
) -> Result<(Vec<u8>, VerificationLevel)> {
    // Phase 1: Parse
    let ast = parser::parse(source)?;

    // Phase 2: Type check
    let typed_ast = types::typecheck(&ast)?;

    // Phase 3: Contract check
    let verified_ast = contracts::verify(&typed_ast)?;

    // Phase 4: Optimize
    let mut optimized_ast = verified_ast;
    optimize::optimize(&mut optimized_ast, opt_level);

    // Phase 5: Generate Wasm
    let wasm = codegen::generate(&optimized_ast)?;

    Ok((wasm, VerificationLevel::Silver))
}

/// Compile BMB source code to native x64 Linux ELF executable
///
/// This compiles BMB code directly to x64 machine code and wraps it in
/// an ELF64 executable format. The resulting binary can run directly on
/// Linux x86-64 systems without any runtime dependencies.
///
/// # Arguments
///
/// * `source` - The BMB source code to compile
///
/// # Returns
///
/// * The ELF64 executable bytes and verification level achieved
///
/// # Example
///
/// ```ignore
/// let source = r#"
/// @node main
/// @params
/// @returns i64
///   mov %result 42
///   ret %result
/// "#;
/// let (elf_bytes, level) = bmb::compile_to_x64(source)?;
/// std::fs::write("output", &elf_bytes)?;
/// ```
pub fn compile_to_x64(source: &str) -> Result<(Vec<u8>, VerificationLevel)> {
    compile_to_x64_with_opt(source, optimize::OptLevel::Basic)
}

/// Compile BMB source code to native x64 with specified optimization level
pub fn compile_to_x64_with_opt(
    source: &str,
    opt_level: optimize::OptLevel,
) -> Result<(Vec<u8>, VerificationLevel)> {
    // Phase 1: Parse
    let ast = parser::parse(source)?;

    // Phase 2: Type check
    let typed_ast = types::typecheck(&ast)?;

    // Phase 3: Verify contracts
    let mut verified_ast = contracts::verify(&typed_ast)?;

    // Phase 4: Optimize
    optimize::optimize(&mut verified_ast, opt_level);

    // Phase 5: Generate x64 machine code
    let mut codegen = x64::X64Codegen::new();
    let code = codegen.compile_executable(&verified_ast.program)?;

    // Phase 6: Wrap in ELF64 format
    let elf = x64::Elf64Builder::new().code(code).build();

    Ok((elf, VerificationLevel::Silver))
}

/// Compile BMB source code to native x64 Windows PE executable
///
/// This compiles BMB code directly to x64 machine code and wraps it in
/// a PE64 executable format. The resulting binary can run directly on
/// Windows x64 systems.
///
/// # Arguments
///
/// * `source` - The BMB source code to compile
///
/// # Returns
///
/// * The PE64 executable bytes and verification level achieved
pub fn compile_to_pe(source: &str) -> Result<(Vec<u8>, VerificationLevel)> {
    compile_to_pe_with_opt(source, optimize::OptLevel::Basic)
}

/// Compile BMB source code to Windows PE64 with specified optimization level
pub fn compile_to_pe_with_opt(
    source: &str,
    opt_level: optimize::OptLevel,
) -> Result<(Vec<u8>, VerificationLevel)> {
    // Phase 1: Parse
    let ast = parser::parse(source)?;

    // Phase 2: Type check
    let typed_ast = types::typecheck(&ast)?;

    // Phase 3: Verify contracts
    let mut verified_ast = contracts::verify(&typed_ast)?;

    // Phase 4: Optimize
    optimize::optimize(&mut verified_ast, opt_level);

    // Phase 5: Calculate IAT RVAs for small programs (< 4KB code)
    // For larger programs, we'd need a two-pass approach
    let iat_rvas = x64::Pe64Builder::calculate_iat_rvas_small();

    // Phase 6: Generate x64 machine code for Windows
    let mut codegen = x64::X64Codegen::new();
    let code = codegen.compile_executable_windows(&verified_ast.program, iat_rvas)?;

    // Phase 7: Verify code fits in expected size
    if code.len() > 0x1000 {
        return Err(BmbError::CodegenError {
            message: format!(
                "Generated code ({} bytes) exceeds single page limit for fixed IAT layout. \
                 Use a smaller program or wait for two-pass compilation support.",
                code.len()
            ),
        });
    }

    // Phase 8: Wrap in PE64 format
    let pe = x64::Pe64Builder::new().code(code).build();

    Ok((pe, VerificationLevel::Silver))
}

/// Compile BMB source code to native x64 macOS Mach-O executable
///
/// This compiles BMB code directly to x64 machine code and wraps it in
/// a Mach-O 64-bit executable format. The resulting binary can run directly on
/// macOS x86-64 systems.
///
/// # Arguments
///
/// * `source` - The BMB source code to compile
///
/// # Returns
///
/// * The Mach-O 64 executable bytes and verification level achieved
pub fn compile_to_macho(source: &str) -> Result<(Vec<u8>, VerificationLevel)> {
    compile_to_macho_with_opt(source, optimize::OptLevel::Basic)
}

/// Compile BMB source code to macOS Mach-O with specified optimization level
pub fn compile_to_macho_with_opt(
    source: &str,
    opt_level: optimize::OptLevel,
) -> Result<(Vec<u8>, VerificationLevel)> {
    // Phase 1: Parse
    let ast = parser::parse(source)?;

    // Phase 2: Type check
    let typed_ast = types::typecheck(&ast)?;

    // Phase 3: Verify contracts
    let mut verified_ast = contracts::verify(&typed_ast)?;

    // Phase 4: Optimize
    optimize::optimize(&mut verified_ast, opt_level);

    // Phase 5: Generate x64 machine code
    let mut codegen = x64::X64Codegen::new();
    let code = codegen.compile_executable(&verified_ast.program)?;

    // Phase 6: Wrap in Mach-O format
    let macho = x64::MachO64Builder::new().code(code).build();

    Ok((macho, VerificationLevel::Silver))
}

/// Compile BMB source code to native ARM64 Linux ELF executable
///
/// This compiles BMB code directly to ARM64 machine code and wraps it in
/// an ELF64 executable format. The resulting binary can run directly on
/// Linux aarch64 systems (e.g., Raspberry Pi 4, AWS Graviton).
///
/// # Arguments
///
/// * `source` - The BMB source code to compile
///
/// # Returns
///
/// * The ARM64 ELF64 executable bytes and verification level achieved
pub fn compile_to_arm64(source: &str) -> Result<(Vec<u8>, VerificationLevel)> {
    compile_to_arm64_with_opt(source, optimize::OptLevel::Basic)
}

/// Compile BMB source code to ARM64 Linux ELF with specified optimization level
pub fn compile_to_arm64_with_opt(
    source: &str,
    opt_level: optimize::OptLevel,
) -> Result<(Vec<u8>, VerificationLevel)> {
    // Phase 1: Parse
    let ast = parser::parse(source)?;

    // Phase 2: Type check
    let typed_ast = types::typecheck(&ast)?;

    // Phase 3: Verify contracts
    let mut verified_ast = contracts::verify(&typed_ast)?;

    // Phase 4: Optimize
    optimize::optimize(&mut verified_ast, opt_level);

    // Phase 5: Generate ARM64 machine code
    let mut codegen = arm64::Arm64Codegen::new();
    let code = codegen.compile_executable(&verified_ast.program)?;

    // Phase 6: Wrap in ELF64 format
    let elf = arm64::Arm64Elf64Builder::new().code(code).build();

    Ok((elf, VerificationLevel::Silver))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_level_ordering() {
        assert!(VerificationLevel::Stone < VerificationLevel::Bronze);
        assert!(VerificationLevel::Bronze < VerificationLevel::Silver);
        assert!(VerificationLevel::Silver < VerificationLevel::Gold);
    }

    #[test]
    fn test_verification_level_display() {
        assert_eq!(VerificationLevel::Stone.to_string(), "Stone (Level 0)");
        assert_eq!(VerificationLevel::Bronze.to_string(), "Bronze (Level 1)");
        assert_eq!(VerificationLevel::Silver.to_string(), "Silver (Level 2)");
        assert_eq!(VerificationLevel::Gold.to_string(), "Gold (Level 3)");
    }

    #[test]
    fn test_compile_to_macho() {
        let source = r#"
@node main
@params
@returns i32
  mov %result 42
  ret %result
"#;
        let (macho, level) = compile_to_macho(source).expect("Mach-O compilation failed");

        // Check Mach-O magic (little-endian: 0xFEEDFACF = MH_MAGIC_64)
        assert!(macho.len() >= 4, "Mach-O file too small");
        assert_eq!(
            &macho[0..4],
            &[0xCF, 0xFA, 0xED, 0xFE],
            "Not a Mach-O 64-bit file"
        );

        // Check CPU type at offset 4 (x86_64 = 0x01000007)
        let cputype = i32::from_le_bytes([macho[4], macho[5], macho[6], macho[7]]);
        assert_eq!(cputype, 0x0100_0007, "Not x86_64 CPU type");

        assert_eq!(level, VerificationLevel::Silver);
    }

    #[test]
    fn test_compile_to_arm64() {
        let source = r#"
@node main
@params
@returns i32
  mov %result 42
  ret %result
"#;
        let (elf, level) = compile_to_arm64(source).expect("ARM64 ELF compilation failed");

        // Check ELF magic
        assert!(elf.len() >= 20, "ELF file too small");
        assert_eq!(&elf[0..4], &[0x7F, b'E', b'L', b'F'], "Not an ELF file");

        // Check 64-bit class
        assert_eq!(elf[4], 2, "Not 64-bit ELF");

        // Check ARM64 machine type at offset 18
        let machine = u16::from_le_bytes([elf[18], elf[19]]);
        assert_eq!(machine, 183, "Not ARM64 (aarch64) machine type");

        assert_eq!(level, VerificationLevel::Silver);
    }
}
