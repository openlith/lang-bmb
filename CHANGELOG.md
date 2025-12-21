# Changelog

All notable changes to BMB will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.0] - 2025-12-21

### Added

#### Core Language
- **Advanced Types**: Full support for `i64`, `f32`, `f64` types alongside `i32` and `bool`
- **Contract Literal Type Promotion**: Automatic type promotion for literals in contract expressions (e.g., `0` promotes to `0.0` in f64 contexts)
- **Verification Levels**: Three-tier verification system (Stone, Bronze, Silver)

#### Compiler
- **Optimizer**: Constant folding and dead code elimination optimization passes
- **Grammar Export**: Export BMB grammar in EBNF, JSON Schema, and GBNF formats
- **Validation API**: Quick validation endpoint for external tool integration

#### Developer Tools
- **Formatter** (`bmbc fmt`): Automatic code formatting with `--check` and `--write` options
- **Linter** (`bmbc lint`): Static analysis with warnings for:
  - Missing contracts
  - Division without zero-check
  - Unused registers
  - Unreachable code
- **Enhanced CLI**: Full-featured command-line interface with subcommands

#### Standard Library
- `stdlib/math.bmb`: Integer math functions (abs, max, min, clamp, sign, pow_simple, factorial, gcd, lcm)
- `stdlib/math_f64.bmb`: Float math functions (abs_f64, max_f64, min_f64, clamp_f64, lerp, sign_f64, reciprocal, average)
- `stdlib/logic.bmb`: Logic functions (is_even, is_odd, is_positive, is_negative, is_zero, in_range, xor_bool, nand, nor)

#### Documentation
- Comprehensive Language Reference (`docs/LANGUAGE_REFERENCE.md`)
- Step-by-step Tutorial (`docs/TUTORIAL.md`)
- Updated README with Quick Start guide

### Changed
- Improved error messages with source location context
- Enhanced type checker with better error diagnostics
- Optimized WASM code generation

### Fixed
- Type promotion in contract expressions for mixed-type comparisons
- Parser handling of float literals in all contexts

## [0.1.0] - 2025-12-21

### Added

#### Core Language
- **Node Definition**: Function definitions with `@node` directive
- **Parameters**: Typed parameters with `@params`
- **Return Types**: Explicit return types with `@returns`
- **Contracts**: Design-by-contract with `@pre` and `@post` conditions
- **Basic Types**: `i32` and `bool` primitive types

#### Instructions
- **Arithmetic**: `add`, `sub`, `mul`, `div`, `mod`
- **Comparison**: `eq`, `ne`, `lt`, `le`, `gt`, `ge`
- **Control Flow**: `jmp`, `jif`, `ret`, `call`
- **Data Movement**: `mov`, `load`, `store`

#### Compiler
- **PEG Parser**: pest-based parser with full BMB grammar
- **Type Checker**: Static type safety verification
- **WASM Codegen**: WebAssembly binary generation
- **Runtime Contract Verification**: Runtime checks for pre/post conditions

#### Infrastructure
- **CLI Tool** (`bmbc`): Basic compile and run commands
- **Integration Tests**: Comprehensive test suite
- **CI/CD**: GitHub Actions workflow

### Technical Details
- Built with Rust 2021 edition
- Uses pest 2.7 for parsing
- Uses wasm-encoder 0.220 for WASM generation
- Uses wasmtime 27 for runtime execution

---

## Versioning Policy

BMB follows [Semantic Versioning](https://semver.org/):

- **MAJOR**: Incompatible API changes or breaking language changes
- **MINOR**: New features in a backwards-compatible manner
- **PATCH**: Backwards-compatible bug fixes

## Verification Levels

| Level | Name | Guarantee |
|-------|------|-----------|
| 0 | Stone | Parsing success |
| 1 | Bronze | Type safety |
| 2 | Silver | Contract verification (runtime) |

[Unreleased]: https://github.com/openlith/bmb/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/openlith/bmb/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/openlith/bmb/releases/tag/v0.1.0
