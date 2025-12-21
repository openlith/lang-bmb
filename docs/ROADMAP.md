# BMB Implementation Roadmap

## Research Summary

### Prior Art

| Project | Relevance | Key Learnings |
|---------|-----------|---------------|
| **Eiffel** | Design by Contract origin | Pre/post conditions, class invariants |
| **SPARK/Ada** | Formal verification | Static verification, proof annotations |
| **Liquid Haskell** | Refinement types | SMT-based type checking |
| **MoonBit** | New Wasm-first language | Modern Wasm toolchain approach |

### Technology Stack (Recommended)

| Component | Technology | Rationale |
|-----------|------------|-----------|
| **Implementation Language** | Rust | Wasm ecosystem, performance, safety |
| **Parser** | pest or rust-peg | PEG-based, mature, good error messages |
| **Wasm Generation** | wasm-encoder | Direct Wasm binary generation |
| **Contract Checking** | Custom + z3 (future) | Runtime first, SMT later |
| **Constrained Decoding** | Outlines / XGrammar | Grammar enforcement for LLMs |

---

## Phase Overview

```
Phase 0: Foundation      [2 weeks]   ← Current
Phase 1: Parser          [3 weeks]
Phase 2: Type System     [3 weeks]
Phase 3: Code Generation [4 weeks]
Phase 4: Contracts       [3 weeks]
Phase 5: AI Integration  [3 weeks]
─────────────────────────────────────
Total:                   ~18 weeks
```

---

## Phase 0: Foundation

**Goal:** Project setup and infrastructure

### Tasks

- [ ] Initialize Rust project structure
- [ ] Set up CI/CD (GitHub Actions)
- [ ] Define project layout
- [ ] Create test framework
- [ ] Write initial BMB examples for testing

### Deliverables

```
bmb/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   ├── ast.rs          # AST definitions
│   ├── parser.rs       # Parser (Phase 1)
│   ├── types.rs        # Type system (Phase 2)
│   ├── codegen.rs      # Wasm generation (Phase 3)
│   └── contracts.rs    # Contract checking (Phase 4)
├── tests/
│   └── examples/
│       ├── factorial.bmb
│       ├── divide.bmb
│       └── fibonacci.bmb
└── grammar/
    └── bmb.pest        # PEG grammar
```

### Success Criteria

- `cargo build` succeeds
- `cargo test` framework works
- Example .bmb files exist

---

## Phase 1: Parser

**Goal:** Parse BMB source into AST

### Tasks

- [ ] Define formal grammar (PEG)
- [ ] Implement AST data structures
- [ ] Implement parser using pest/rust-peg
- [ ] Error reporting with line/column
- [ ] Unit tests for all syntax elements

### Grammar (PEG)

```peg
program     = { node+ }
node        = { "@node" ~ ident ~ params ~ returns ~ contracts ~ body }
params      = { "@params" ~ (param)+ }
param       = { ident ~ ":" ~ type }
returns     = { "@returns" ~ type }
contracts   = { pre? ~ post? }
pre         = { "@pre" ~ expr }
post        = { "@post" ~ expr }
body        = { instruction+ }
instruction = { (label | stmt) }
label       = { "_" ~ ident ~ ":" }
stmt        = { opcode ~ operands }
opcode      = { "add" | "sub" | "mul" | "div" | ... }
type        = { "i32" | "i64" | "f32" | "f64" | "bool" }
```

### Deliverables

- `parse(source: &str) -> Result<AST, ParseError>`
- Clear error messages with source location
- 100% grammar coverage tests

### Success Criteria

- All example files parse successfully
- Invalid syntax produces helpful errors

---

## Phase 2: Type System

**Goal:** Type checking and inference

### Tasks

- [ ] Implement type representation
- [ ] Implement type environment
- [ ] Implement type checking pass
- [ ] Register allocation tracking
- [ ] Type error reporting

### Type Rules

```
Γ ⊢ e1 : i32    Γ ⊢ e2 : i32
────────────────────────────
Γ ⊢ add %r e1 e2 : i32

Γ ⊢ params(f) match args
────────────────────────────
Γ ⊢ call %r f args : returns(f)
```

### Deliverables

- `typecheck(ast: &AST) -> Result<TypedAST, TypeError>`
- Type annotations on all expressions
- Type error messages with expected vs actual

### Success Criteria

- Well-typed programs pass
- Ill-typed programs produce clear errors
- Bronze verification level achieved

---

## Phase 3: Code Generation

**Goal:** Generate WebAssembly from typed AST

### Tasks

- [ ] Map BMB types to Wasm types
- [ ] Implement instruction translation
- [ ] Implement control flow (labels, jumps)
- [ ] Implement function calls
- [ ] Generate valid .wasm binary

### Type Mapping

| BMB Type | Wasm Type |
|----------|-----------|
| `i32` | `i32` |
| `i64` | `i64` |
| `f32` | `f32` |
| `f64` | `f64` |
| `bool` | `i32` (0/1) |

### Instruction Mapping

| BMB | Wasm |
|-----|------|
| `add %r a b` | `local.get a`, `local.get b`, `i32.add`, `local.set r` |
| `jif %c _label` | `local.get c`, `br_if label` |
| `ret %r` | `local.get r`, `return` |

### Deliverables

- `codegen(typed_ast: &TypedAST) -> Result<Vec<u8>, CodegenError>`
- Valid .wasm output
- Executable in wasmtime/wasmer

### Success Criteria

- `factorial(5)` returns `120`
- `fibonacci(10)` returns `55`
- All examples execute correctly

---

## Phase 4: Contracts

**Goal:** Runtime contract verification

### Tasks

- [ ] Parse contract expressions
- [ ] Generate contract check code
- [ ] Insert precondition checks at entry
- [ ] Insert postcondition checks before return
- [ ] Contract violation error messages

### Implementation Strategy

```
@pre b != 0

Compiles to:
  local.get $b
  i32.eqz
  if
    unreachable  ;; trap with "precondition failed: b != 0"
  end
```

### Deliverables

- Contract expressions in AST
- Runtime checks in generated Wasm
- Clear trap messages

### Success Criteria

- `divide(10, 0)` traps with precondition error
- `divide(10, 2)` returns `5`
- Silver verification level achieved

---

## Phase 5: AI Integration

**Goal:** Enable AI to generate valid BMB code

### Tasks

- [ ] Export grammar as JSON/EBNF
- [ ] Create Outlines/XGrammar schema
- [ ] Test with local LLM
- [ ] Measure first-gen success rate
- [ ] Create prompt templates

### Constrained Decoding Setup

```python
from outlines import models, generate

model = models.transformers("mistral-7b")
generator = generate.cfg(model, bmb_grammar)

code = generator("Write a BMB function that computes GCD")
# Guaranteed valid BMB syntax
```

### Deliverables

- BMB grammar for constrained decoding
- Integration examples with Outlines/XGrammar
- Benchmark results

### Success Criteria

- 100% syntax validity with constrained decoding
- Measured improvement over unconstrained generation

---

## Future Phases (v0.2+)

### Phase 6: Static Contract Verification

- SMT solver integration (z3)
- Compile-time contract proving
- Gold verification level

### Phase 7: Advanced Types

- Arrays `[T; N]`
- References `&T`
- Structs
- Enums/Sum types

### Phase 8: Module System

- Multi-file projects
- Import/export
- Standard library

### Phase 9: Optimizations

- Dead code elimination
- Constant folding
- Inline expansion

---

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Parser complexity | Use proven PEG library, start minimal |
| Wasm generation bugs | Extensive test suite, validate with wasmtime |
| Contract checking performance | Runtime checks first, optimize later |
| LLM integration issues | Test early with simple grammars |

---

## Decision Log

| Decision | Rationale | Date |
|----------|-----------|------|
| Rust for implementation | Wasm ecosystem, safety | TBD |
| pest for parser | PEG-based, good errors | TBD |
| Wasm as first target | Portability, sandboxing | TBD |
| Runtime contracts first | Simpler, prove value | TBD |

---

## Next Actions

1. **Immediate:** Initialize Rust project
2. **This week:** Complete Phase 0
3. **Next week:** Begin Phase 1 (Parser)
