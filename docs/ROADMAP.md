# BMB Development Roadmap

> **"Omission is guessing, and guessing is error."**

**Last Updated**: 2025-12-24
**Current Version**: v0.11.0
**Target**: v1.0.0 (Performance Transcendence)

---

## Philosophy

This roadmap follows BMB's core principle: **no shortcuts, no guessing**. Each version represents a complete, testable milestone. The path from v0.6.0 to v1.0.0 is intentionally granular to ensure each step is achievable and verifiable.

### Version Strategy

```
v0.6-v0.15: Foundation (Self-Hosting)
v0.16-v0.18: Bronze Stage (Language Features)
v0.19-v0.21: Silver Stage (LLVM Integration)
v0.22-v0.24: Gold Stage (Optimization)
v1.0.0: Performance Transcendence Complete 🎯
```

---

## Current State (v0.10.0)

### Implemented Features

| Category | Features |
|----------|----------|
| **Parser** | PEG grammar, pest parser, error reporting |
| **Types** | i8-i64, u8-u64, f32, f64, bool, char, arrays, structs, enums, refs, pointers |
| **Generics** | Option<T>, Result<T,E>, Vector<T>, Slice<T> |
| **Refined Types** | `@type nz_i32 i32 where self != 0` |
| **Strings** | String (owned), Str (view), UTF-8 validity |
| **Contracts** | @pre, @post, @invariant, @requires, @pure, @contract, @assert, @variant, runtime & static verification |
| **Linear Types** | @consume (use-once), @device (MMIO), @volatile (hardware regs) |
| **Codegen** | WASM, x64 ELF64/PE64/Mach-O64, ARM64 ELF64 |
| **Verification** | SMT (Z3/CVC4/CVC5), static contract proving (Gold level), purity checking, linear type checking |
| **DevEx** | LSP server, formatter, linter |
| **Modules** | @use, @import, qualified calls, namespace |
| **Optimization** | IR, constant folding, DCE, function inlining |
| **Package Manager** | Gotgan with Cargo fallback |
| **Bitwise ISA** | and, or, xor, shl, shr, not |

---

## v0.7.0: Contract System Completion ✅

**Goal**: Complete the contract system for mathematical proof claims

| Task | Priority | Status |
|------|----------|--------|
| `@variant` termination proof (grammar/AST/parser) | Critical | ✅ Done |
| `@pure` side-effect annotation (grammar/AST/parser) | Critical | ✅ Done |
| `@requires` contract chaining (grammar/AST/parser) | High | ✅ Done |
| `@contract` named contract definitions | High | ✅ Done |
| `@constraint` timing (on_create/on_mutate) | High | ✅ Spec |
| Bitwise ISA (and/or/xor/shl/shr/not) | High | ✅ Done |
| `@requires` verification logic | Critical | ✅ Done |
| `@pure` verification logic | Critical | ✅ Done |
| Loop invariant runtime verification | Critical | ✅ Done |

**Success Criteria**:
- ✅ `@variant` proves termination for recursive functions
- ✅ `@pure` functions verified for referential transparency (no xcall, print, or impure calls)
- ✅ Contract chaining works with `@requires` (parameter substitution)
- ✅ Bitwise operations available for systems programming
- ✅ Loop invariants verified at runtime (trap on violation)

---

## v0.8.0: Efficient Explicitness & Collections ✅

**Goal**: Token-efficient syntax without compromising "Omission is guessing" philosophy, plus fundamental data structures

> **Design Principle**: "Signal Density Maximization" - Optimize for *useful information per token*, not token reduction. BMB is AI-native: explicit contracts are signals that boost AI accuracy, not noise to be minimized.

### Part 1: Signal Density Optimization

> **AI-Native Principle**: BMB optimizes for *signal density*, not token reduction. Explicit contracts are signals that HELP AI accuracy. The goal is maximizing useful information per token, not minimizing tokens.

| Task | Priority | Complexity | Status | AI Impact |
|------|----------|------------|--------|-----------|
| Refined Types (`@type`) | Critical | High | ✅ Done | ✅ High signal (type name = constraint) |
| Spec-Defined Defaults (zero-init) | Low | Medium | Conditional | ⚠️ Needs tooling (AI requires spec injection) |
| Auto-SSA operator (`!`) | Low | Medium | Deferred | ❌ Hidden state harms AI understanding |

#### Refined Types (`@type`)

Embed constraints in type definitions. Constraints become part of the type's identity.

```bmb
# Type definitions with embedded constraints
@type nz_i32 i32 where self != 0
@type pos_i32 i32 where self > 0
@type percent u8 where self <= 100
@type index[N] u64 where self < N

# Usage - constraint is part of the type, not hidden
@node divide
@params a:i32 b:nz_i32    # b != 0 is explicit in type name
@returns i32
@post ret * b == a

  div %r a b
  ret %r
```

**Semantic Rules**:
- Refined type expands to base type + constraint at verification time
- SMT solver receives full constraint: `(assert (not (= b 0)))`
- No information is hidden; type name documents the constraint

**Philosophy Alignment**:
- ✅ Constraints are explicit (in type definition)
- ✅ No guessing (type name reveals constraint)
- ✅ Mathematically complete (SMT receives full expansion)

#### Spec-Defined Defaults (Zero-Initialization) [Conditional]

**Status**: Conditional on tooling support. Requires `.bmbmap` or LSP to inject specification context.

All registers are zero-initialized by language specification. This is **not** implicit behavior—it is **specified behavior** documented in the language spec.

```bmb
# Old style (explicit initialization)
mov %i 0
mov %sum 0

# New style (spec-defined default)
# %i and %sum are i32, spec says: "i32 initializes to 0"
# No guessing - behavior is defined by spec, not assumed
```

**Specification Rule**:
> "Every register of type T is initialized to T's zero-value upon declaration. Zero-values: integers → 0, floats → 0.0, bool → false, pointers → null."

**Philosophy Alignment**:
- ✅ Not omission (spec explicitly defines behavior)
- ✅ Not guessing (documented, deterministic)
- ✅ Mathematically equivalent to explicit `mov %r 0`

**AI-Native Concern** (Research-backed):
- ⚠️ AI models don't inherently know BMB spec
- ⚠️ Without spec injection, AI sees "uninitialized" registers
- ⚠️ "Lost in the middle" phenomenon: spec rules often ignored if not proximate

**Tooling Requirement**:
- `.bmbmap` must include zero-value table for AI context
- LSP hover must show "initialized to 0 (BMB spec §4.3)"
- IDE integration must surface spec-defined behavior at point of use

**Adoption Gate**: Implement only after Structural Synthesis (v0.11.0) provides spec injection mechanism.

#### Auto-SSA Operator (`!`) [Deferred]

**Status**: Deferred indefinitely. Hidden state tracking fundamentally conflicts with AI-native design.

Explicit version increment for SSA without manual naming.

```bmb
# Manual SSA versioning
add %i_1 %i 1
add %i_2 %i_1 1

# Auto-SSA with explicit operator (DEFERRED)
add %i! %i 1    # Creates next version of %i
add %i! %i 1    # Creates another version
```

**AI-Native Analysis** (Research-backed):
- ❌ **Hidden state**: AI must track invisible version numbers mentally
- ❌ **Context burden**: AI accuracy degrades with implicit state tracking
- ❌ **Error debugging**: When AI generates `%i!`, which version did it mean?
- ❌ **"Lost in the middle"**: Version context easily forgotten in long functions

**Contrast with Explicit SSA**:
```bmb
# Explicit SSA - AI sees exactly what it's working with
add %i_1 %i 1     # Clear: %i_1 depends on %i
add %i_2 %i_1 1   # Clear: %i_2 depends on %i_1
```

**Decision**: The verbosity cost of explicit SSA names is the correct trade-off for AI-native design. Token count is not the goal; signal clarity is.

**Reconsideration Criteria**:
- Only if research demonstrates AI accuracy improves with Auto-SSA
- Only if tooling can perfectly reconstruct version history for AI context

### Part 2: Standard Library - Collections

| Task | Priority | Complexity | Status |
|------|----------|------------|--------|
| `Option<T>` - nullable alternative (type) | Critical | Medium | ✅ Done |
| `Result<T,E>` - error handling (type) | Critical | Medium | ✅ Done |
| `Vector<T>` - dynamic array (type) | Critical | High | ✅ Done |
| `Slice<T>` - view into array (type) | High | Medium | ✅ Done |
| Collection stdlib implementation | Critical | Very High | Planned |
| `HashMap<K,V>` - hash table | Critical | Very High | Planned |
| `Range` - iteration bounds | High | Low | Planned |

**Contract Examples** (using Refined Types):
```bmb
@type cap_u64 u64 where self > 0

@struct Vector
  data:*T
  len:u64
  cap:cap_u64           # Capacity is always positive (refined type)
  @constraint len <= cap

@node vector_push
@params v:&Vector<T> item:T
@returns bool
@pre v.len < MAX_SIZE
@post v.len == old(v.len) + 1
@post v[v.len - 1] == item
```

**Success Criteria**:
- ✅ Refined Types grammar, parser, and type checker implemented
- ✅ Generic type definitions (Option<T>, Result<T,E>, Vector<T>, Slice<T>) implemented
- ✅ Type compatibility checks for refined types
- Spec-defined defaults documented and implemented (Conditional on v0.11.0)
- Auto-SSA deferred (AI-native analysis)
- Collection stdlib with full @pre/@post contracts (Next phase)
- Gold-level verification passes for core operations (Next phase)

---

## v0.9.0: Standard Library - Strings & Text ✅ COMPLETE

**Goal**: UTF-8 string handling with safety contracts

| Task | Priority | Status |
|------|----------|--------|
| `String` - owned UTF-8 string | Critical | ✅ Complete |
| `Str` - string slice/view | Critical | ✅ Complete |
| UTF-8 validity at type level | Critical | ✅ Complete |
| String concatenation | High | Next phase |
| Character iteration | High | Next phase |
| Format/parsing utilities | Medium | Next phase |

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

## v0.10.0: Low-Level Safety ✅ COMPLETE

**Goal**: Comprehensive memory safety and hardware interaction for bare-metal systems

**Philosophy**: BMB uses **contract-based pointer verification** rather than Rust-style ownership. This maintains "Omission is guessing" principle with explicit, verifiable contracts. As a "Bare-Metal" language, BMB must also support hardware interaction primitives.

### Implemented Features (v0.10.0)

| Feature | Description | Status |
|---------|-------------|--------|
| `@consume` annotation | Linear types - use exactly once | ✅ Complete |
| `@device` annotation | MMIO pointer parameters | ✅ Complete |
| `@volatile` annotation | Hardware register structs | ✅ Complete |
| `DeviceDef` | `@device NAME 0xADDRESS` declarations | ✅ Complete |
| Linear Type Checker | Compile-time usage tracking | ✅ Complete |
| Hex address literals | `0x40000000` format support | ✅ Complete |

### Planned Features (Future)

### Spatial Pointer Safety

| Task | Priority | Complexity |
|------|----------|------------|
| Pointer predicate builtins | Critical | High |
| `valid(ptr)` - allocation check | Critical | High |
| `no_alias(ptr1, ptr2)` - aliasing check | Critical | Very High |
| `in_bounds(ptr, base, len)` - bounds | High | Medium |
| Region-based contracts | High | High |
| Arena allocator with contracts | Medium | Medium |

### Temporal Pointer Safety (Linear Types)

| Task | Priority | Complexity |
|------|----------|------------|
| `@consume` annotation | Critical | High |
| Linear type checking | Critical | High |
| Use-after-free prevention | Critical | High |
| Double-free prevention | Critical | Medium |
| Ownership transfer semantics | High | Medium |

**Linear Type Examples**:
```bmb
@node consume_buffer
@params buf:*u8 @consume    # Linear: must be used exactly once
@returns void
@pre valid(buf)
@post freed(buf)            # Postcondition: buffer is freed

  # buf can only be used once - compiler enforces this
  call free buf
  ret

@node transfer_ownership
@params src:*Resource @consume
@returns *Resource
@post valid(ret)
@post freed(src)            # Old pointer invalidated

  # Ownership transferred - src cannot be used after this
  ret src
```

### Hardware Interaction (MMIO)

| Task | Priority | Complexity |
|------|----------|------------|
| `@device` region annotation | Critical | Medium |
| `@volatile` ordering guarantee | Critical | Medium |
| Memory-mapped I/O support | Critical | High |
| Interrupt-safe annotations | High | Medium |
| Hardware register modeling | High | Medium |

**Hardware Interaction Examples**:
```bmb
@device UART_BASE 0x40000000    # Memory-mapped UART base address
@device UART_SIZE 0x100         # UART register region size

@struct UartRegs @volatile      # All fields have volatile semantics
  data:u8                       # 0x00: Data register
  status:u8                     # 0x01: Status register
  control:u8                    # 0x02: Control register

@node uart_write
@params uart:*UartRegs @device  # Pointer to device memory
@params byte:u8
@returns void
@pre valid_device(uart, UART_BASE, UART_SIZE)
@pre uart.status & TX_READY != 0

  # Volatile write - cannot be reordered or optimized away
  store uart.data byte
  ret

@node uart_read
@params uart:*UartRegs @device
@returns u8
@pre valid_device(uart, UART_BASE, UART_SIZE)
@pre uart.status & RX_READY != 0

  # Volatile read - always reads from hardware
  load %byte uart.data
  ret %byte
```

### Spatial Safety Contract Examples

```bmb
@node safe_deref
@params ptr:*i32
@returns i32
@pre valid(ptr)                        # Pointer validity contract
@pre aligned(ptr, 4)                   # Alignment contract
@pre not_null(ptr)                     # Null check contract
@post true

  load %value ptr 0
  ret %value

@node process_buffer
@params buf:*u8 len:u32
@returns void
@pre valid_region(buf, len)            # Region validity
@pre no_alias_region(buf, len, other)  # No aliasing
@post true
```

**Built-in Predicates**:
| Predicate | Description | Verification Level |
|-----------|-------------|-------------------|
| `valid(ptr)` | Points to allocated memory | Silver/Gold |
| `not_null(ptr)` | Not null | Bronze |
| `aligned(ptr, n)` | n-byte aligned | Bronze |
| `in_bounds(ptr, base, len)` | Within bounds | Silver/Gold |
| `no_alias(p1, p2)` | No aliasing | Gold |
| `freed(ptr)` | Pointer has been freed | Gold |
| `valid_device(ptr, base, size)` | Valid MMIO region | Bronze |

**Success Criteria**:
- Spatial pointer safety verified through contracts
- Temporal safety via linear types (@consume)
- Hardware interaction via @device/@volatile
- No ownership/borrow complexity
- Philosophy consistency maintained

---

## v0.11.0: Diagnostics & Tooling ✅ COMPLETE

**Goal**: Actionable error messages, SMT counterexamples, contract assistance, and structural analysis

| Task | Priority | Complexity | Status |
|------|----------|------------|--------|
| Structured error format (JSON) | High | Medium | ✅ Done |
| SMT counterexample visualization | Critical | High | ✅ Done |
| Fix suggestions in errors | High | Medium | ✅ Done |
| IDE integration (LSP enhancements) | High | Medium | ✅ Done |
| **Invariant suggestion mode** | High | Very High | ✅ Done |
| **Structural Synthesis (`.bmbmap`)** | High | High | Planned |
| Coverage reporting | Medium | Medium | Planned |
| Performance profiling hooks | Low | Medium | Planned |

### Structural Synthesis (`.bmbmap`)

Auto-generated project architecture map. The compiler scans the codebase and synthesizes structural metadata—developers write logic, the tool generates the map.

```bash
# Generate structural map
bmbc map --output project.bmbmap

# Query the map
bmbc query --map project.bmbmap --callers "auth.validate"
bmbc query --map project.bmbmap --data-flow "user_input -> database"
```

**Generated `.bmbmap` Contents**:
```yaml
# Auto-generated - DO NOT EDIT
version: 0.11.0
generated: 2025-12-23T10:00:00Z

modules:
  auth:
    nodes: [validate, hash_password, check_token]
    verified_level: gold

call_graph:
  main -> auth.validate -> db.query

data_flow:
  user_input:
    sources: [http.request]
    sinks: [db.query]
    contracts_applied: [sanitize, validate]

contract_coverage:
  total_nodes: 45
  with_pre: 42
  with_post: 38
  gold_verified: 30
```

**Philosophy Alignment**:
- Tool generates metadata, not developer
- No syntax changes to BMB language
- Supplements contracts, doesn't replace them

### Invariant Suggestion Mode

**Philosophy**: Automatic invariant synthesis can conflict with "Omission is guessing". BMB's solution: the compiler **suggests** invariants, but the developer must **confirm** them. This preserves explicit requirements while reducing the verification burden.

**CLI Usage**:
```bash
# Suggest invariants for loops without @invariant
bmbc verify program.bmb --suggest-invariants

# Interactive mode: suggest and prompt for confirmation
bmbc verify program.bmb --suggest-invariants --interactive

# Output suggested invariants to file for review
bmbc verify program.bmb --suggest-invariants --output suggestions.bmb
```

**Suggestion Output Format**:
```
info[I301]: Loop invariant suggestion
  --> src/sum.bmb:15:1
   |
15 | _loop:
   |  ^^^^^ No @invariant specified
   |
   = Suggested invariants (review and add explicitly):
     @invariant _loop %i >= 0
     @invariant _loop %i <= len
     @invariant _loop %sum >= 0

   = To apply: Add these to your source file after @params/@returns
   = Note: Suggestions are heuristic - verify they match your intent
```

**Supported Heuristics**:
| Pattern | Suggested Invariant |
|---------|---------------------|
| Counter `%i` with `lt %cond %i N` | `%i >= 0 && %i <= N` |
| Accumulator `add %sum %sum %x` | `%sum >= 0` (if inputs positive) |
| Array index in bounds check | `%idx < len` |
| Decreasing counter | `%i >= 0` (termination) |

### Error Format

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
- Invariant suggestion mode helps users write correct contracts
- Suggestions require explicit confirmation (no implicit contracts)

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

## v0.15.0: Self-Hosted Compiler

**Goal**: BMB compiler compiles itself - Production-ready self-hosted compiler

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
- `bmbc` binary (self-compiled)
- Standard library with full contracts
- Tooling stable: LSP, formatter, linter
- Package ecosystem: Gotgan registry operational

---

# Performance Transcendence Roadmap

> **Vision**: Surpass C/Rust performance through proof-guided optimization
>
> BMB's contract system enables optimizations impossible in languages where the compiler must assume the worst case. When contracts are proven, the compiler gains knowledge that enables aggressive optimizations.

---

## Bronze Stage (v0.16 - v0.18): Language Foundation

**Goal**: Complete language features enabling advanced optimization

### v0.16.0: Region-Based Memory

| Task | Description | Research Basis |
|------|-------------|----------------|
| `@region` declaration | Named memory regions | Cyclone/MLKit model |
| Region polymorphism | Functions parameterized by region | MLKit stack allocation |
| Escape analysis | Auto stack/heap allocation | Go/Java JVM escape analysis |
| `@no_escape` annotation | Guarantee no pointer escape | LLVM noalias generation |

**Contract Examples**:
```bmb
@region local
  @node process_data
  @params data:*i32@local len:u32
  @returns i32
  @pre valid_region(data, len, local)
  @post no_escape(data)    # Enables stack allocation
    # ... processing ...
```

**Success Criteria**:
- Region-scoped allocation verified at compile time
- Stack allocation for non-escaping data

### v0.17.0: Effect System

| Task | Description | Research Basis |
|------|-------------|----------------|
| `@effect` annotation | Declare side effects | Koka effect system |
| Effect inference | Automatic effect detection | Type-and-effects systems |
| `@pure` verification | Prove no side effects | Referential transparency |
| Effect polymorphism | Generic over effects | Effect handlers |

**Effect Categories**:
```bmb
@effect IO        # File/network operations
@effect Alloc     # Memory allocation
@effect Panic     # Can trap/abort
@effect Diverge   # May not terminate

@node pure_compute
@params x:i32 y:i32
@returns i32
@pure                    # No effects allowed
@effect !IO !Alloc       # Explicit effect denial
  add %r x y
  ret %r
```

**Success Criteria**:
- Effect system integrates with contract verification
- @pure functions provably side-effect free

### v0.18.0: Liquid Types

| Task | Description | Research Basis |
|------|-------------|----------------|
| Refinement type syntax | `x:i32{x > 0}` inline | Liquid Haskell, F* |
| SMT predicate embedding | Type predicates → SMT | Liquid Types paper |
| Refinement inference | Automatic refinement | LiquidHaskell |
| Bounds check elimination | Proven bounds → no check | Dependent ML |

**Type Examples**:
```bmb
# Type-level refinements replace runtime checks
@typedef PosInt = i32{v > 0}
@typedef BoundedIdx = u32{v < len}

@node safe_index
@params arr:[i32; 100] idx:u32{idx < 100}
@returns i32
  # No bounds check needed - proven at type level
  load %val arr idx
  ret %val
```

**Success Criteria**:
- Refinement types integrate with @pre/@post
- Automatic bounds check elimination for proven cases

---

## Silver Stage (v0.19 - v0.21): LLVM Integration

**Goal**: Translate contract knowledge into LLVM optimization hints

### v0.19.0: LLVM Backend Foundation

| Task | Description | Priority |
|------|-------------|----------|
| LLVM IR generation | Basic codegen | Critical |
| Type mapping | BMB → LLVM types | Critical |
| Function ABI | Calling conventions | Critical |
| Basic optimization passes | mem2reg, simplifycfg | High |

**LLVM Integration Strategy**:
```
BMB Source → AST → TypedProgram → VerifiedProgram → LLVM IR → Native
                                        ↓
                                   SMT Proofs
                                        ↓
                                  LLVM Metadata
```

### v0.20.0: Contract-Driven Metadata

| Task | Description | LLVM Feature |
|------|-------------|--------------|
| Range metadata | Proven value ranges | `!range` |
| Noalias annotations | Proven non-aliasing | `noalias`, `restrict` |
| Nonnull pointers | Proven non-null | `!nonnull` |
| Alignment info | Proven alignment | `align` attribute |
| Dereferenceable | Safe to load | `dereferenceable` |

**Metadata Injection**:
```llvm
; From @pre x > 0 && x < 100
define i32 @process(i32 %x) {
  ; BMB injects: x has range [1, 99]
  %x.range = !{i32 1, i32 100}

  ; From @pre no_alias(a, b)
  define void @swap(i32* noalias %a, i32* noalias %b)

  ; From @pre not_null(ptr)
  define i32 @deref(i32* nonnull dereferenceable(4) %ptr)
}
```

**Success Criteria**:
- Contract proofs generate LLVM metadata
- 10-30% performance improvement over basic codegen

### v0.21.0: Advanced LLVM Optimization

| Task | Description | Research Basis |
|------|-------------|----------------|
| Loop metadata | Vectorization hints | LLVM loop metadata |
| Profile-guided opt | Runtime → compile hints | PGO (5-30% gains) |
| Alive2 integration | Verify optimizations | SMT-based verification |
| Link-time optimization | Whole-program opt | LTO/ThinLTO |

**PGO Integration**:
```bash
# Stage 1: Instrumented build
bmbc compile program.bmb --emit llvm --pgo-gen -o program.prof

# Stage 2: Profile collection
./program.prof < typical_input.txt

# Stage 3: Optimized build
bmbc compile program.bmb --emit llvm --pgo-use=profile.data -o program
```

**Success Criteria**:
- PGO integration achieves 10-20% additional speedup
- Alive2 verifies optimization correctness

---

## Gold Stage (v0.22 - v0.24): Performance Transcendence

**Goal**: Surpass C/Rust through proof-guided optimization

### v0.22.0: Proof-Guided Loop Optimization

| Task | Description | Optimization Enabled |
|------|-------------|---------------------|
| Invariant code motion | Move proven-invariant code | Loop hoisting |
| Bounds elimination | Proven bounds → no check | Vectorization enable |
| Iteration bounds | Proven trip count | Loop unrolling |
| Dependence analysis | Proven independence | Parallelization |

**Optimization Example**:
```bmb
@node sum_array
@params arr:[i32; N] len:u32
@returns i64
@pre len <= N              # Proves bounds
@invariant _loop i < len   # Enables vectorization

  mov %sum 0
  mov %i 0
_loop:
  lt %cond %i len
  jif %cond _body _done
_body:
  # No bounds check - proven by invariant
  load %val arr %i
  add %sum %sum %val
  add %i %i 1
  jmp _loop
_done:
  ret %sum
```

**Generated LLVM** (with proof metadata):
```llvm
define i64 @sum_array([N x i32]* %arr, i32 %len) {
  ; Loop vectorization enabled - bounds proven safe
  !{!"llvm.loop.vectorize.enable", i1 true}
  ; No bounds checks in loop body
}
```

### v0.23.0: Comptime Execution

| Task | Description | Research Basis |
|------|-------------|----------------|
| `@comptime` annotation | Compile-time execution | Zig comptime |
| Constant propagation | Extended folding | @pure + comptime |
| Type computation | Type-level values | Dependent types |
| Generic instantiation | Monomorphization | Rust generics |

**Comptime Examples**:
```bmb
@comptime
@node factorial_ct
@params n:u64
@returns u64
@pre n <= 20
@pure
  # Executes at compile time
  eq %base n 0
  jif %base _one _recurse
_one:
  ret 1
_recurse:
  sub %n1 n 1
  call %sub factorial_ct %n1
  mul %r n %sub
  ret %r

# Usage - computed at compile time
@node main
@returns u64
  # factorial_ct(10) = 3628800 (computed at compile time)
  mov %result @comptime factorial_ct(10)
  ret %result
```

### v0.24.0: SIMD & Vectorization

| Task | Description | Target |
|------|-------------|--------|
| Explicit SIMD types | `v128`, `v256` | Portable SIMD |
| SIMD intrinsics | Platform-specific ops | AVX2, NEON |
| Auto-vectorization hints | Contract-driven | LLVM vectorizer |
| Parallel iteration | Proven independence | OpenMP-style |

**SIMD Examples**:
```bmb
@node dot_product
@params a:[f32; N] b:[f32; N]
@returns f32
@pre N % 8 == 0           # Enables AVX vectorization
@pre aligned(a, 32)       # 32-byte aligned for AVX
@pre aligned(b, 32)
@pure

  # Compiler auto-vectorizes with AVX2
  # Contract proves safety of 8-wide operations
```

---

## v1.0.0: Performance Transcendence Complete 🎯

| Capability | C | Rust | BMB |
|------------|---|------|-----|
| Bounds check elimination | Manual | Partial | **Proven** |
| Alias analysis | Limited | Borrow checker | **SMT proven** |
| Null safety | None | Option | **Contract proven** |
| Vectorization hints | Manual | Limited | **Auto from contracts** |
| Dead code elimination | Limited | Good | **Proof-based** |
| Loop optimization | Manual hints | Some | **Invariant-proven** |

**Transcendence Mechanism**:
```
C:    Compiler assumes worst case → conservative optimization
Rust: Type system provides some guarantees → better optimization
BMB:  Contracts PROVE properties → OPTIMAL optimization

Example: Array access
  C:    Must check bounds (or undefined behavior)
  Rust: Borrow checker helps, but not all cases
  BMB:  @pre proves bounds → NO check, FULL vectorization
```

**Success Criteria**:
- Benchmark suite shows BMB ≥ C performance
- Proof-guided optimization documented and reproducible
- Philosophy maintained: "Omission is guessing, and guessing is error"

**Deliverables**:
- `bmbc` binary with LLVM backend
- Full proof-guided optimization pipeline
- Comprehensive benchmark suite vs C/Rust
- Performance transcendence documentation

---

## Research-Backed Optimization Summary

| Technique | Source | BMB Integration | Expected Gain |
|-----------|--------|-----------------|---------------|
| Region memory | Cyclone, MLKit | @region, escape analysis | 10-20% allocation |
| Liquid types | LiquidHaskell | Type refinements | 15-30% bounds checks |
| PGO | LLVM | --pgo-gen/--pgo-use | 5-30% overall |
| LLVM metadata | LLVM docs | Contract → metadata | 10-30% optimization |
| Escape analysis | Go, Java JVM | @no_escape | Stack allocation |
| Alive2 | Research | Optimization verification | Correctness |
| Comptime | Zig | @comptime, @pure | Compile-time eval |

---

## Future Directions (Post-v1.0)

| Feature | Description | Priority |
|---------|-------------|----------|
| GPU/Compute targets | CUDA, OpenCL codegen | Medium |
| Formal semantics | Coq/Lean formalization | Low |
| Incremental compilation | Faster rebuilds | High |
| Distributed verification | Parallel SMT solving | Medium |
| AI-assisted contracts | Contract suggestion | Low |
| WebGPU backend | Browser-based GPU compute | Medium |
| Embedded targets | ARM Cortex-M, RISC-V | High |

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
| 11.0 | 2025-12-24 | v0.11.0 Complete: Diagnostics struct + JSON serialization, LSP-compatible errors, SMT counterexample visualization, invariant suggestion with SMT verification and CLI --suggest-invariants |
| 10.0 | 2025-12-24 | v0.10.0 Complete: @consume/@device/@volatile annotations, Linear Type Checker, DeviceDef, hex address literals |
| 9.0 | 2025-12-24 | v0.9.0 Complete: String/Str types with UTF-8 validity constraints |
| 8.2 | 2025-12-23 | v0.8.0 Complete: Refined Types, Option<T>, Result<T,E>, Vector<T>, Slice<T> type definitions implemented |
| 8.1 | 2025-12-23 | AI-Native re-evaluation: "Signal Density" replaces "Token Efficiency"; Spec-Defined Defaults conditional on tooling; Auto-SSA deferred |
| 8.0 | 2025-12-23 | v0.8.0 "Efficient Explicitness": Refined Types, Spec-Defined Defaults, Auto-SSA; v0.11.0 adds Structural Synthesis |
| 7.1 | 2025-12-23 | v0.10.0 expanded to "Low-Level Safety": @consume, @device, @volatile; v0.11.0 adds invariant suggestion mode |
| 7.0 | 2025-12-23 | v0.7.0 complete: @requires chaining, @pure verification, @invariant runtime checks |
| 6.0 | 2025-12-23 | Version restructure: v1.0.0 = Performance Transcendence, all prior stages v0.x |
| 5.0 | 2025-12-23 | Performance Transcendence Roadmap (Bronze/Silver/Gold stages, research-backed) |
| 4.0 | 2025-12-23 | Extended roadmap v0.7-v0.15, realistic phases |
| 3.0 | 2025-12-22 | v0.4.0 current status |
| 2.0 | 2025-12-21 | Initial v0.2.0 roadmap |
