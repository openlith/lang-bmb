//! x64 Native Code Generation Backend
//!
//! Direct x64 machine code generation without runtime dependencies.
//! Philosophy: "Omission is guessing, and guessing is error."
//!
//! ## Architecture
//!
//! ```text
//! TypedProgram → X64Codegen → MachineCode → ELF64/PE64/MachO64 → Native Executable
//! ```
//!
//! ## Modules
//!
//! - `registers`: x64 register definitions and encoding
//! - `encoding`: x64 instruction encoding (REX, ModR/M, SIB)
//! - `elf`: ELF64 executable generation (Linux)
//! - `pe`: PE64 executable generation (Windows)
//! - `macho`: Mach-O 64 executable generation (macOS)
//! - `codegen`: BMB to x64 translation

pub mod codegen;
pub mod elf;
pub mod encoding;
pub mod macho;
pub mod pe;
pub mod registers;

pub use codegen::X64Codegen;
pub use elf::Elf64Builder;
pub use macho::MachO64Builder;
pub use pe::Pe64Builder;
