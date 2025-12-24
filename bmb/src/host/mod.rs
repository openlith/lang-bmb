//! Host interface helpers for BMB runtime environments (v0.13+)
//!
//! This module provides reference implementations for host functions
//! that BMB programs can import via `@extern` declarations.

pub mod io;

pub use io::*;
