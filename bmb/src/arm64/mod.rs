//! ARM64 (AArch64) Native Code Generation Backend
//!
//! Direct ARM64 machine code generation without runtime dependencies.
//!
//! ## Architecture
//!
//! ```text
//! TypedProgram → Arm64Codegen → MachineCode → ELF64 → Native Executable
//! ```
//!
//! ## Modules
//!
//! - `registers`: ARM64 register definitions (X0-X30, W0-W30)
//! - `encoding`: ARM64 instruction encoding (fixed 32-bit)
//! - `codegen`: BMB to ARM64 translation
//! - `elf`: ELF64 executable generation for Linux ARM64

pub mod codegen;
pub mod elf;
pub mod encoding;
pub mod registers;

pub use codegen::Arm64Codegen;
pub use elf::Arm64Elf64Builder;
