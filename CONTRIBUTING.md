# Contributing to BMB

Thank you for your interest in contributing to BMB! This document provides guidelines and information for contributors.

## Code of Conduct

By participating in this project, you agree to maintain a respectful and inclusive environment.

## Getting Started

### Prerequisites

- Rust 1.75+ (2021 edition)
- Cargo package manager
- Git

### Setup

```bash
# Clone the repository
git clone https://github.com/openlith/lang-bmb.git
cd bmb/bmb

# Build the library
cargo build

# Build with CLI
cargo build --features cli

# Run tests
cargo test

# Run with release optimizations
cargo build --release --features cli
```

## How to Contribute

### Reporting Bugs

Before reporting a bug:
1. Search existing issues to avoid duplicates
2. Use the bug report template
3. Include:
   - BMB version (`bmbc --version`)
   - Operating system and version
   - Minimal reproduction code
   - Expected vs actual behavior
   - Error messages (full output)

### Suggesting Features

1. Search existing issues and discussions
2. Use the feature request template
3. Explain the use case and motivation
4. Consider how it aligns with BMB's philosophy

### Submitting Pull Requests

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/your-feature`
3. Make your changes
4. Add or update tests
5. Run the full test suite: `cargo test`
6. Run the formatter: `cargo fmt`
7. Run clippy: `cargo clippy`
8. Commit with a clear message
9. Push and create a Pull Request

## Development Guidelines

### Code Style

- Follow Rust conventions (use `cargo fmt`)
- Use `cargo clippy` and address warnings
- Write descriptive variable and function names
- Add comments for complex logic
- Keep functions focused and small

### Testing

- Add tests for new features
- Add regression tests for bug fixes
- Run `cargo test` before submitting
- Aim for meaningful test coverage

### Commit Messages

Follow conventional commits:

```
type(scope): description

[optional body]

[optional footer]
```

Types:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `test`: Test additions or fixes
- `refactor`: Code refactoring
- `perf`: Performance improvements
- `chore`: Build, CI, or tooling changes

Examples:
```
feat(parser): add support for i64 literals
fix(codegen): correct stack handling for nested calls
docs(tutorial): add factorial example
test(contracts): add edge case tests for division
```

### Branch Naming

- `feature/description` - New features
- `fix/issue-number` - Bug fixes
- `docs/topic` - Documentation updates
- `refactor/area` - Code refactoring

## Project Structure

```
bmb/
├── src/
│   ├── lib.rs          # Library entry point
│   ├── main.rs         # CLI entry point
│   ├── ast.rs          # Abstract Syntax Tree
│   ├── parser.rs       # PEG parser
│   ├── bmb.pest        # Grammar definition
│   ├── typecheck.rs    # Type checker
│   ├── codegen.rs      # WASM code generation
│   ├── contracts.rs    # Contract verification
│   ├── formatter.rs    # Code formatter
│   ├── linter.rs       # Static analysis
│   ├── optimize.rs     # Optimization passes
│   └── grammar.rs      # Grammar export
├── stdlib/             # Standard library
├── examples/           # Example programs
├── tests/              # Integration tests
└── grammar-dist/       # Exported grammar files
```

## Philosophy Alignment

BMB's core principles:

| Principle | Description |
|-----------|-------------|
| **Omission is Guessing** | Explicit over implicit |
| **Compile-time over Runtime** | Catch bugs early |
| **Contracts are Code** | Specifications are executable |
| **Precision over Convenience** | Correctness first |

Contributions should align with these principles. Avoid:
- Adding implicit behaviors
- Introducing "convenience" features that sacrifice precision
- Runtime-only error detection when compile-time is possible

## Review Process

1. All PRs require at least one review
2. CI must pass (tests, formatting, clippy)
3. Changes to core language semantics need discussion first
4. Documentation updates are encouraged

## Getting Help

- Open a Discussion for questions
- Check existing issues and discussions
- Read the documentation in `docs/`

## License

By contributing, you agree that your contributions will be licensed under the MIT License.
