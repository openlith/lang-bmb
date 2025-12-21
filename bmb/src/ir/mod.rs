//! Intermediate Representation (IR) for BMB
//!
//! A lower-level, platform-independent representation optimized for analysis
//! and transformation. The IR sits between the typed AST and code generation.
//!
//! ## Design Principles
//!
//! - **Register-based**: Operations work on virtual registers
//! - **Explicit control flow**: Labels and jumps instead of structured blocks
//! - **Type-preserving**: Types are maintained for verification
//! - **Optimization-friendly**: Designed for inlining, constant propagation, etc.
//!
//! ## Pipeline
//!
//! ```text
//! TypedProgram → IrProgram → [Optimizations] → Codegen
//! ```

pub mod lower;
pub mod optimize;
pub mod types;

pub use lower::lower_program;
pub use optimize::{inline_functions, optimize_ir};
pub use types::*;
