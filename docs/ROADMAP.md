# BMB Development Roadmap

> **"Omission is guessing, and guessing is error."**

**Last Updated**: 2025-12-23
**Current Version**: v0.6.0
**Target**: v1.0.0 (Self-Hosted Compiler)

---

## Philosophy

This roadmap follows BMB's core principle: **no shortcuts, no guessing**. Each version represents a complete, testable milestone. The path from v0.6.0 to v1.0.0 is intentionally granular to ensure each step is achievable and verifiable.

---

## Current State (v0.6.0)

### Implemented Features

| Category | Features |
|----------|----------|
| **Parser** | PEG grammar, pest parser, error reporting |
| **Types** | i8-i64, u8-u64, f32, f64, bool, char, arrays, structs, enums, refs, pointers |
| **Contracts** | @pre, @post, @invariant, runtime verification |
| **Codegen** | WASM, x64 ELF64/PE64/Mach-O64, ARM64 ELF64 |
| **Verification** | SMT (Z3/CVC4/CVC5), static contract proving (Gold level) |
| **DevEx** | LSP server, formatter, linter |
| **Modules** | @use, @import, qualified calls, namespace |
| **Optimization** | IR, constant folding, DCE, function inlining |
| **Package Manager** | Gotgan with Cargo fallback |

---

## v0.7.0: Contract System Completion

**Goal**: Complete the contract system for mathematical proof claims

| Task | Priority | Status |
|------|----------|--------|
| `@variant` termination proof | Critical | Planned |
| `@pure` side-effect annotation | Critical | Planned |
| `@requires` contract chaining | High | Planned |
| `@contract` named contract definitions | High | Planned |
| `@constraint` in @struct | High | Planned |
| Loop invariant support in parser/verifier | Critical | Planned |

**Success Criteria**:
- `@variant` proves termination for recursive functions
- `@pure` functions verified for referential transparency
- Contract chaining works with `@requires`

---

## v0.8.0: Standard Library - Collections

**Goal**: Fundamental data structures with full contract coverage

| Task | Priority | Complexity |
|------|----------|------------|
| `Vector<T>` - dynamic array | Critical | High |
| `HashMap<K,V>` - hash table | Critical | Very High |
| `Option<T>` - nullable alternative | Critical | Medium |
| `Result<T,E>` - error handling | Critical | Medium |
| `Slice<T>` - view into array | High | Medium |
| `Range` - iteration bounds | High | Low |

**Contract Examples**:
```bmb
@struct Vector
  data:*T
  len:u64
  cap:u64
  @constraint len <= cap
  @constraint cap > 0 || data == null

@node vector_push
@params v:&Vector<T> item:T
@returns bool
@pre v.len < MAX_SIZE
@post v.len == old(v.len) + 1
@post v[v.len - 1] == item
```

**Success Criteria**:
- All collections have full @pre/@post contracts
- Gold-level verification passes for core operations

---

## v0.9.0: Standard Library - Strings & Text

**Goal**: UTF-8 string handling with safety contracts

| Task | Priority | Complexity |
|------|----------|------------|
| `String` - owned UTF-8 string | Critical | High |
| `Str` - string slice/view | Critical | Medium |
| String concatenation | High | Medium |
| UTF-8 validation contracts | Critical | High |
| Character iteration | High | Medium |
| Format/parsing utilities | Medium | High |

**Contract Examples**:
```bmb
@struct Str
  ptr:*u8
  len:u64
  @constraint valid_utf8(ptr, len)    # Structural guarantee

@node str_concat
@params a:Str b:Str
@returns String
@pure
@post ret.len == a.len + b.len
```

**Success Criteria**:
- UTF-8 validity enforced at type level
- No possibility of invalid string construction

---

## v0.10.0: Memory Management

**Goal**: Safe memory patterns without garbage collection

| Task | Priority | Complexity |
|------|----------|------------|
| Region-based allocation | Critical | Very High |
| Arena allocator | High | High |
| Ownership annotations | Critical | Very High |
| Borrow checking (simplified) | High | Very High |
| `@owns` and `@borrows` contracts | High | High |
| Stack allocation optimization | Medium | Medium |

**Contract Examples**:
```bmb
@node with_arena
@params size:u64
@returns Arena
@owns ret                              # Caller owns returned arena
@post arena_capacity(ret) >= size

@node arena_alloc
@params arena:&Arena size:u64
@returns *u8
@borrows arena                         # Borrows, doesn't own
@pre arena_remaining(arena) >= size
@post ret != null
```

**Success Criteria**:
- Memory leaks detectable at compile time
- Use-after-free impossible by construction

---

## v0.11.0: Diagnostics & Tooling

**Goal**: Actionable error messages with SMT counterexamples

| Task | Priority | Complexity |
|------|----------|------------|
| Structured error format (JSON) | High | Medium |
| SMT counterexample visualization | Critical | High |
| Fix suggestions in errors | High | Medium |
| IDE integration (LSP enhancements) | High | Medium |
| Coverage reporting | Medium | Medium |
| Performance profiling hooks | Low | Medium |

**Error Format**:
```
error[E202]: Postcondition violation
  --> src/math.bmb:15:1
   |
15 | @post ret >= 0
   |       ^^^^^^^^ Cannot prove this holds
   |
   = Counterexample:
     x = -5 → ret = -5

   = Suggestion: Add `@pre x >= 0` or change to `@post ret == x * x`
```

**Success Criteria**:
- Every error includes actionable suggestion
- SMT failures show concrete counterexamples

---

## v0.12.0: FFI & Interoperability

**Goal**: Seamless integration with Rust/C ecosystem

| Task | Priority | Complexity |
|------|----------|------------|
| C FFI (`extern "C"`) | Critical | High |
| Rust FFI with type mapping | Critical | Very High |
| `@extern` annotation | High | Medium |
| Automatic bindgen for simple types | High | Very High |
| WASM import/export refinement | High | Medium |
| Cross-language contract propagation | Medium | Very High |

**Type Mapping**:
| Rust Type | BMB Type | Notes |
|-----------|----------|-------|
| `i32`, `u64`, etc. | Same | Direct mapping |
| `bool` | `bool` | Direct |
| `*const T` | `*T` | Raw pointer |
| `&T` | `&T` | Immutable ref |
| `Option<T>` | `Option<T>` | Requires BMB Option |
| `Result<T,E>` | `Result<T,E>` | Requires BMB Result |
| Complex generics | ❌ | Not supported |
| Lifetimes | Implicit | Simplified model |

**Success Criteria**:
- `#[no_std]` Rust crates usable from BMB
- BMB functions callable from Rust

---

## v0.13.0: Self-Hosting Preparation

**Goal**: All primitives needed to write a compiler

| Task | Priority | Complexity |
|------|----------|------------|
| File I/O abstraction | Critical | High |
| Command-line argument parsing | High | Medium |
| Tree data structures (AST) | Critical | High |
| Pattern matching syntax | High | High |
| Error accumulation patterns | High | Medium |
| Source location tracking | High | Medium |

**Required Capabilities**:
```bmb
# Must be expressible in BMB:
- Read file → Vec<u8>
- Parse bytes → AST tree
- Walk tree recursively
- Generate output bytes
- Write to file
```

**Success Criteria**:
- Simple text processor writable in BMB
- All compiler primitives available

---

## v0.14.0: Compiler Components in BMB

**Goal**: Core compiler logic rewritten in BMB

| Task | Priority | Complexity |
|------|----------|------------|
| Lexer/Tokenizer | Critical | Medium |
| Parser (subset of BMB grammar) | Critical | Very High |
| AST definitions | Critical | High |
| Type checker (core) | Critical | Very High |
| Basic WASM emitter | High | High |
| Integration with Rust compiler | High | High |

**Milestones**:
1. BMB tokenizer tokenizes BMB source
2. BMB parser parses simple BMB programs
3. BMB type checker validates simple programs
4. BMB emits valid WASM for trivial functions

**Success Criteria**:
- `factorial.bmb` compiled by BMB-written components
- Output matches Rust-compiled version

---

## v0.15.0: Bootstrapping

**Goal**: BMB compiler compiles itself

| Task | Priority | Complexity |
|------|----------|------------|
| Complete parser in BMB | Critical | Very High |
| Complete type checker in BMB | Critical | Very High |
| Complete contract verifier in BMB | Critical | Very High |
| Complete WASM codegen in BMB | Critical | Very High |
| Cross-compilation verification | Critical | High |
| Performance benchmarking | High | Medium |

**Bootstrap Stages**:
```
Stage 0: bmbc (Rust) compiles BMB source
Stage 1: bmbc-stage1 (BMB, compiled by Rust) compiles BMB source
Stage 2: bmbc-stage2 (BMB, compiled by Stage 1) compiles BMB source
Stage 3: bmbc-stage3 (BMB, compiled by Stage 2) compiles BMB source

Verification: Stage 2 binary == Stage 3 binary (fixed point)
```

**Success Criteria**:
- Fixed point achieved
- Performance within 2x of Rust version

---

## v1.0.0: Production Release 🎯

**Goal**: Stable, self-hosted, production-ready compiler

| Requirement | Status |
|-------------|--------|
| Self-hosted compiler | Stage 2 = Stage 3 |
| All contracts proven | Gold level |
| Documentation complete | All features documented |
| Tooling stable | LSP, formatter, linter |
| Package ecosystem | Gotgan registry operational |
| Performance benchmarks | Published baselines |

**Deliverables**:
- `bmbc` binary (self-compiled)
- Standard library with full contracts
- Language specification (frozen for 1.x)
- Migration guide from 0.x

---

## Post-v1.0: Future Directions

| Feature | Description | Priority |
|---------|-------------|----------|
| Effect system | Track and verify side effects | High |
| Refinement types | `x:i32 where x > 0` | High |
| Dependent types (limited) | Type-level computation | Medium |
| GPU/SIMD targets | Parallel computation | Medium |
| Incremental compilation | Faster rebuilds | High |
| Formal semantics | Coq/Lean formalization | Low |

---

## Risk Register

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| SMT solver limitations | Medium | High | Fallback to runtime checks |
| Bootstrap complexity | High | Critical | Incremental, tested stages |
| Memory model complexity | High | High | Start simple, extend gradually |
| FFI type mapping | Medium | Medium | Limit to simple types first |
| Performance regression | Medium | Medium | Continuous benchmarking |

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 4.0 | 2025-12-23 | Extended roadmap v0.7-v0.15, realistic phases |
| 3.0 | 2025-12-22 | v0.4.0 current status |
| 2.0 | 2025-12-21 | Initial v0.2.0 roadmap |
