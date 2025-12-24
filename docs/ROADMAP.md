# BMB Development Roadmap

> **"Omission is guessing, and guessing is error."**

**Last Updated**: 2025-12-24
**Current Version**: v0.15.3
**Target**: v1.0.0 (Performance Transcendence)

---

## Philosophy

This roadmap follows BMB's core principle: **no shortcuts, no guessing**. Each version represents a complete, testable milestone. The path from v0.6.0 to v1.0.0 is intentionally granular to ensure each step is achievable and verifiable.

### Version Strategy

```
v0.6-v0.13: Foundation (Core Language Complete)
v0.14-v0.15: Self-Hosting Preparation (Boilerplate Reduction, Tooling)
v0.15.1-v0.15.3: Implementation Hardening (Verify features work)
v0.16-v0.18: Self-Hosting (Incremental Compiler in BMB)
v0.19-v0.21: Bronze Stage (Advanced Generics & Type System)
v0.21.1-v0.21.3: Rust Interoperability (C/Rust FFI, Cargo integration)
v0.22-v0.24: Silver Stage (LLVM Integration)
v0.25-v0.27: Gold Stage (Optimization)
v0.27.1-v0.27.3: Tool Ecosystem Maturation (Package manager, IDE)
v1.0.0: Performance Transcendence Complete 🎯

Parallel Track: Benchmark Suite (Continuous from v0.22+)
```

### Positioning Philosophy (v0.15+)

> **"Difficult to learn, but highly effective."**

BMB deliberately trades convenience for precision:
- **Speed**: Contract-proven code enables aggressive optimization
- **Safety**: Explicit contracts eliminate undefined behavior
- **Reliability**: "Omission is guessing" prevents subtle bugs

**Implicit Target**: AI-assisted development. BMB's explicit contracts provide high signal density that helps AI code generators produce correct code on the first attempt. The verbosity is not noise—it's semantic information.

### Boilerplate Reduction Strategy (v0.14+)

> **Problem**: BMB's explicit contracts can create boilerplate. This reduces signal density.
>
> **Solution**: Inference and templates that preserve "Omission is guessing" through **suggest-then-confirm** patterns.

| Technique | Reduction | Version | Philosophy |
|-----------|-----------|---------|------------|
| Refined Types | 40-60% | ✅ v0.8.0 | Type name = constraint (explicit) |
| Frame Inference | 30-50% | ✅ v0.14.0 | Auto-detect writes, suggest @modifies |
| Postcondition Inference | 20-40% | ✅ v0.14.0 | Strongest postcondition → suggestion |
| Contract Templates | 15-25% | ✅ v0.7.0 | @contract + @requires (explicit) |
| Default Type Contracts | 10-20% | v0.15 | Type-level invariants auto-applied |

**Key Principle**: Inference generates **suggestions**, not implicit behavior. Developer confirms explicitly.

### Generics Philosophy: Contract-Propagating Monomorphic Generics

> **Problem**: Without generics, BMB requires repetitive code for each type (Vector<i32>, Vector<f64>, etc.)
> This repetition reduces signal density and hides the essential pattern.
>
> **Solution**: Monomorphic generics with contract propagation
> - **One definition** → N type-specific instantiations (pattern preserved)
> - **Contracts propagate** automatically to each instantiation
> - **Zero runtime cost** via monomorphization
> - **Declaration-time checking** prevents "surprise" errors at instantiation

---

## Current State (v0.13.0)

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
| **FFI** | @extern with calling conventions (C/SysV64/Win64), @pub visibility, WASM import modules |
| **Codegen** | WASM, x64 ELF64/PE64/Mach-O64, ARM64 ELF64 |
| **Verification** | SMT (Z3/CVC4/CVC5), static contract proving (Gold level), purity checking, linear type checking |
| **DevEx** | LSP server, formatter, linter, SMT counterexamples, invariant suggestions |
| **Modules** | @use, @import, qualified calls, namespace |
| **Optimization** | IR, constant folding, DCE, function inlining |
| **Package Manager** | Gotgan with Cargo fallback |
| **Bitwise ISA** | and, or, xor, shl, shr, not |
| **Self-Hosting Prep** | Box<T> heap allocation, enhanced Span, ErrorCollector, File I/O abstraction, CLI argument parser |

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

## v0.12.0: FFI & Interoperability ✅ COMPLETE

**Goal**: Seamless integration with Rust/C ecosystem via explicit calling conventions

| Task | Priority | Complexity | Status |
|------|----------|------------|--------|
| `@extern` annotation with calling convention | Critical | High | ✅ Done |
| C ABI (`extern "C"`, System V) | Critical | High | ✅ Done |
| Windows x64 ABI (`extern "win64"`) | High | Medium | ✅ Done |
| WASM import module names | High | Medium | ✅ Done |
| `@pub` export visibility annotation | High | Medium | ✅ Done |
| `xcall` extern function integration | High | Medium | ✅ Done |
| Cross-language contract propagation | Medium | Very High | Planned |
| Automatic bindgen | Medium | Very High | Planned |

### @extern Declaration (v0.12+)

Explicit FFI declarations with calling convention specification:

```bmb
# C function with System V ABI (Linux/macOS)
@extern "C" from "libc"
@node puts
@params s:*i8
@returns i32
@pre valid(s)

# Windows-specific function
@extern "win64" from "kernel32"
@node GetLastError
@params
@returns u32

# Default env module (no "from")
@extern "C"
@node custom_logger
@params msg:*i8 level:i32
@returns void
```

### @pub Visibility (v0.12+)

Explicit export control with backwards compatibility:

```bmb
# Public - exported from module
@pub
@node public_api
@params x:i32
@returns i32
  ret x

# Private - NOT exported (when any @pub exists)
@node internal_helper
@params y:i32
@returns i32
  ret y

# Legacy: If NO @pub in file, all functions are exported (backwards compatible)
```

### Calling Conventions

| Convention | Registers (Args) | Return | Use Case |
|------------|------------------|--------|----------|
| `"C"` (SysV64) | RDI, RSI, RDX, RCX, R8, R9 | RAX | Linux, macOS |
| `"win64"` | RCX, RDX, R8, R9 | RAX | Windows x64 |
| `"system"` | Platform default | RAX | Auto-select |

### Philosophy Alignment

- ✅ Explicit calling conventions ("Omission is guessing")
- ✅ Two-level WASM namespace (module + function name)
- ✅ Contract support for extern functions (@pre only)
- ✅ Backwards-compatible visibility defaults

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

## v0.13.0: Self-Hosting Preparation ✅ COMPLETE

**Goal**: All primitives needed to write a compiler

| Task | Priority | Complexity | Status |
|------|----------|------------|--------|
| Box<T> heap allocation (box/unbox/drop) | Critical | High | ✅ Done |
| Enhanced Span (multi-line tracking) | High | Medium | ✅ Done |
| ErrorCollector (accumulation pattern) | High | Medium | ✅ Done |
| File I/O abstraction (stdlib/io.bmb) | Critical | High | ✅ Done |
| CLI argument parsing (platform-independent) | High | Medium | ✅ Done |
| Tree data structures (AST) | Critical | High | Planned (v0.15) |
| Pattern matching syntax | High | High | Planned (v0.15) |

**Implemented Capabilities**:
```bmb
# Now expressible in BMB (v0.13+):
- Box<T> heap allocation with bump allocator
- Multi-line source location tracking
- Multiple error accumulation
- File I/O via @extern host imports
- CLI argument parsing (short/long options, subcommands)
```

**Success Criteria**:
- ✅ Heap allocation primitives (box/unbox/drop)
- ✅ Source location tracking with snippets
- ✅ Error collection without early termination
- ✅ File I/O abstraction for compiler
- ✅ CLI parsing for bmbc reimplementation

---

## v0.14.0: Contract Inference & Boilerplate Reduction

**Goal**: Reduce boilerplate while maintaining "Omission is guessing" through suggest-then-confirm patterns

> **Philosophy**: Inference generates **suggestions** displayed to developer. Developer must explicitly add to code.

| Task | Priority | Complexity | Research Basis |
|------|----------|------------|----------------|
| **Frame Inference** | Critical | High | SPARK Ada, Frama-C |
| **Postcondition Inference** | High | Very High | Strongest postcondition calculus |
| **Default Type Contracts** | High | Medium | Refined types extension |
| **Contract Templates Library** | Medium | Low | Reusable @contract definitions |
| **`bmbc suggest` CLI** | High | Medium | Dafny --suggest-invariants |

### Frame Inference (30-50% reduction)

Automatically detect which memory locations a function modifies.

```bash
# CLI usage
bmbc suggest --frame myprogram.bmb

# Output:
# Suggested @modifies for node 'process_buffer' at line 42:
#   @modifies buf[0..len]
#   @modifies global_count
# Add explicitly to your code to confirm.
```

**Implementation**:
1. Analyze `store` instructions → identify modified locations
2. Track pointer arithmetic → infer modified regions
3. Generate `@modifies` suggestions
4. Developer adds to source (explicit confirmation)

### Postcondition Inference (20-40% reduction)

Compute strongest postcondition from function body.

```bash
bmbc suggest --post myprogram.bmb:add_one

# Output:
# Suggested @post for 'add_one':
#   @post ret == x + 1
# This was computed from the function body. Add if correct.
```

**Implementation (Dijkstra's Guarded Commands)**:
```
sp(skip, P) = P
sp(x := E, P) = ∃x'. P[x'/x] ∧ x = E[x'/x]
sp(S1; S2, P) = sp(S2, sp(S1, P))
```

### Default Type Contracts

Type-level invariants automatically applied at function boundaries.

```bmb
# Type with default contract
@type bounded_u8 u8 where self <= 100

# When used as parameter, @pre auto-suggested
@node process
@params val:bounded_u8
# Suggested: @pre val <= 100  (from type definition)
@returns void
```

**Philosophy Alignment**:
- ✅ Type definition is explicit (developer wrote it)
- ✅ Suggestion is shown, not silently applied
- ✅ Developer confirms by adding @pre

**Success Criteria**:
- `bmbc suggest --frame` works for simple functions
- `bmbc suggest --post` computes basic postconditions
- Suggestions shown in CLI with add instructions
- 20-40% reduction in manual contract writing (measured)

---

## v0.15.0: Pattern Matching & AST Structures ✅ COMPLETE

**Goal**: Language features needed for compiler implementation

| Task | Priority | Status |
|------|----------|--------|
| `@match` expression syntax | Critical | ✅ Complete (v0.13) |
| Exhaustiveness checking | Critical | ✅ Complete |
| AST enum definitions | Critical | ✅ Complete (v0.13) |
| Recursive data structures | High | ✅ Complete (Box<T> v0.13) |
| Tree traversal patterns | High | Pattern match supports |
| String operations (concat, split) | High | Deferred to v0.15.1 |

### Pattern Matching

```bmb
@enum Token
  Number: i64
  Ident: String
  Plus
  Minus

@node token_value
@params tok:Token
@returns Option[i64]
  @match tok
    Token::Number(n) => ret Some(n)
    Token::Ident(_) => ret None
    Token::Plus => ret None
    Token::Minus => ret None
  @end
```

### Recursive AST

```bmb
@enum Expr
  Literal: i64
  BinOp: { op:Op, left:Box<Expr>, right:Box<Expr> }
  Var: String

@node eval
@params e:&Expr
@returns i64
@pure
  @match *e
    Expr::Literal(n) => ret n
    Expr::BinOp(op, l, r) =>
      call %lv eval l
      call %rv eval r
      @match op
        Op::Add => add %res %lv %rv; ret %res
        Op::Sub => sub %res %lv %rv; ret %res
      @end
    Expr::Var(_) => ret 0  # Would need environment
  @end
```

**Success Criteria**:
- Pattern matching with exhaustiveness
- Recursive enum types work with Box<T>
- Tree traversal expressible in BMB

---

## v0.15.1-v0.15.3: Implementation Hardening 🔧

> **Goal**: Verify all documented features actually work in codegen, not just parsing.
>
> **Problem Identified**: Gap analysis revealed ~40% of documented features parse correctly but fail in code generation or runtime. This phase audits and fixes implementation completeness.

### v0.15.1: String & Memory Operations

| Task | Priority | Current State | Target |
|------|----------|---------------|--------|
| String concat codegen | Critical | Parses only | WASM + x64 working |
| String slice operations | Critical | Parses only | Bounds-checked slicing |
| `load`/`store` all types | Critical | Partial | All primitive + compound types |
| Array initialization | High | Partial | Static + dynamic init |
| Struct field access | High | Partial | Full codegen |

**Verification Method**:
```bash
# Each feature must have:
# 1. Parsing test (already exists)
# 2. Type checking test
# 3. WASM codegen test (execute with wasmtime)
# 4. x64 codegen test (execute natively)

cargo test test_string_concat_wasm
cargo test test_string_concat_x64
cargo test test_load_store_all_types
```

**Success Criteria**:
- `String` operations work end-to-end
- `load`/`store` works for i8-i64, f32, f64, bool, arrays, structs
- 100% of v0.9.0 String features actually execute

### v0.15.2: Module & FFI Verification

| Task | Priority | Current State | Target |
|------|----------|---------------|--------|
| `@use`/`@import` codegen | Critical | Spec only | Multi-file compilation |
| Qualified calls | High | Spec only | Cross-module function calls |
| `@extern` WASM imports | High | Partial | Full host function binding |
| `@extern` native linking | Medium | Scaffold | Linux/Windows/macOS linking |

**Test Suite**:
```bmb
# tests/examples/multi_module/main.bmb
@use math

@node test_import
@params x:i32
@returns i32
  call %r math::square x
  ret %r
```

```bmb
# tests/examples/multi_module/math.bmb
@pub
@node square
@params n:i32
@returns i32
@post ret == n * n
  mul %r n n
  ret %r
```

**Success Criteria**:
- Multi-file compilation produces single WASM/ELF
- `@extern` functions can call libc
- Import resolution errors are clear

### v0.15.3: Implementation Completeness Audit

| Task | Priority | Description |
|------|----------|-------------|
| Feature Matrix | Critical | Document implemented vs documented |
| Codegen Coverage | Critical | Every AST node → codegen test |
| Native Backend Audit | High | x64/ARM64 completeness check |
| Documentation Alignment | High | Update docs to match reality |

**Audit Deliverables**:

```markdown
# Implementation Status Report (v0.15.3)

| Feature | Parser | TypeCheck | WASM | x64 | ARM64 |
|---------|--------|-----------|------|-----|-------|
| i32 arithmetic | ✅ | ✅ | ✅ | ✅ | ⚠️ |
| String ops | ✅ | ✅ | ⚠️ | ❌ | ❌ |
| @extern C | ✅ | ✅ | ✅ | ⚠️ | ❌ |
| Modules | ✅ | ⚠️ | ❌ | ❌ | ❌ |
| ... | ... | ... | ... | ... | ... |
```

**Success Criteria**:
- Complete feature matrix published
- All ✅ features have integration tests
- Documentation matches implementation
- Roadmap updated with realistic timelines

---

## v0.16.0: Lexer & Tokenizer in BMB

**Goal**: First compiler component written in BMB (Ghuloum Phase 1)

| Task | Priority | Complexity |
|------|----------|------------|
| Character classification | Critical | Low |
| Token enum definition | Critical | Medium |
| Lexer state machine | Critical | Medium |
| Error recovery | High | Medium |
| Source position tracking | High | Low |

**Milestone**: BMB tokenizer tokenizes BMB source

```bmb
@enum Token
  # Keywords
  KwNode | KwParams | KwReturns | KwPre | KwPost
  # Literals
  IntLit: i64 | FloatLit: f64 | StringLit: String
  # Operators
  Plus | Minus | Star | Slash | Percent
  # Punctuation
  LParen | RParen | Colon | At
  # Identifiers
  Ident: String | Register: String
  # Special
  Eof | Error: String

@node tokenize
@params source:Str
@returns Vector<Token>
@post valid_tokens(ret)
  # ... lexer implementation
```

**Success Criteria**:
- `tokenize("@node foo")` → `[KwNode, Ident("foo")]`
- Error tokens for invalid input
- Position tracking works

---

## v0.17.0: Parser in BMB

**Goal**: Recursive descent parser for BMB subset (Ghuloum Phase 2)

| Task | Priority | Complexity |
|------|----------|------------|
| AST type definitions | Critical | Medium |
| Recursive descent functions | Critical | High |
| Precedence parsing (Pratt) | High | Medium |
| Error messages | High | Medium |
| Span attachment | High | Low |

**Milestone**: BMB parser parses simple BMB programs

```bmb
@struct ParseResult
  ast: Option<Program>
  errors: Vector<Diagnostic>

@node parse
@params tokens:&Vector<Token>
@returns ParseResult
@post ret.ast.is_some => ret.errors.is_empty
  # ... parser implementation
```

**Success Criteria**:
- Parse `@node/@params/@returns` declarations
- Parse arithmetic expressions
- Parse control flow (jmp, jif, ret)
- Meaningful error messages

---

## v0.18.0: Type Checker & Self-Hosted Compiler

**Goal**: Complete self-hosted compiler bootstrap (Ghuloum Phase 3-4)

| Task | Priority | Complexity |
|------|----------|------------|
| Type checker in BMB | Critical | Very High |
| Contract verifier (basic) | High | High |
| WASM codegen in BMB | Critical | High |
| Bootstrap verification | Critical | High |

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
- `factorial.bmb` compiled by BMB-written compiler

---

# Performance Transcendence Roadmap

> **Vision**: Surpass C/Rust performance through proof-guided optimization
>
> BMB's contract system enables optimizations impossible in languages where the compiler must assume the worst case. When contracts are proven, the compiler gains knowledge that enables aggressive optimizations.

---

## Bronze Stage (v0.19 - v0.21): Advanced Generics & Type System

**Goal**: Complete language features enabling advanced optimization, including **Contract-Propagating Monomorphic Generics** to eliminate boilerplate while preserving verifiability.

> **Design Philosophy**: "Contract-Propagating Monomorphic Generics"
> - **Monomorphization**: Zero runtime cost (like Rust/C++, unlike Java erasure)
> - **Contract Propagation**: Generic contracts automatically apply to instantiated types
> - **Declaration-time Checking**: Type errors caught at generic definition, not instantiation (unlike Zig)
> - **Explicit Bounds**: No implicit interface satisfaction (unlike Go)

### v0.19.0: Parametric Data Types & Region Memory

**Goal**: Type parameters for structs/enums + memory region foundations

#### Parametric Data Types (Generics Foundation)

| Task | Description | Research Basis |
|------|-------------|----------------|
| Type parameter syntax `[T]` | Struct/enum type parameters | ML parametric polymorphism |
| Monomorphization | Generate specialized types | Rust/C++ model |
| Generic struct definitions | `@struct Container[T]` | SPARK Ada generics |
| Generic enum definitions | `@enum Result[T, E]` | ML algebraic types |
| Current hardcoded → generic | Option, Result, Vector, Slice | Internal refactor |

**Syntax Examples**:
```bmb
# Parametric struct - T is explicit type parameter
@struct Container[T]
  data: *T
  len: u64
  cap: u64
  @constraint len <= cap    # Contract preserved across T

# Parametric enum
@enum Result[T, E]
  Ok: T
  Err: E

# Instantiation - type parameter explicit (no inference)
@node example
@params
@returns Container[i32]     # Explicit: Container specialized for i32
  mov %c Container[i32]::new
  ret %c
```

**Philosophy Alignment**:
- ✅ "Omission is guessing": Type parameter `[T]` is explicit
- ✅ "Signal density": One definition → N instantiations (pattern, not repetition)
- ✅ Verifiable: Contracts apply to each monomorphized instance

#### Region-Based Memory

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
- Generic structs/enums with type parameters
- Monomorphization produces specialized code
- Region-scoped allocation verified at compile time

### v0.20.0: Generic Functions & Effect System

**Goal**: Type-parameterized functions with contract propagation

#### Generic Functions

| Task | Description | Research Basis |
|------|-------------|----------------|
| Function type parameters | `@node[T] func_name` | ML/Rust generics |
| Contract propagation | Generic @pre/@post apply to T | SPARK Ada |
| Type parameter inference | At call site (optional) | Hindley-Milner |
| Multi-parameter generics | `@node[K, V] map_insert` | Standard parametricity |

**Syntax Examples**:
```bmb
# Generic function - contracts are T-independent
@node[T] container_get
@params c:&Container[T] idx:u64
@returns Option[&T]
@pre idx < c.len              # ← Valid for any T
@pre valid(c)                 # ← Valid for any T
@post ret.is_some => idx < c.len
  lt %in_bounds idx c.len
  jif %in_bounds _valid _none
_valid:
  # ... return Some(&c.data[idx])
_none:
  ret Option[&T]::None

# Usage - T inferred from arguments
@node example
@params v:&Container[i32]
@returns Option[&i32]
  call %r container_get v 0   # T = i32 inferred
  ret %r
```

**Contract Propagation Rules**:
```
Generic Contract          │ Instantiated Contract
─────────────────────────│──────────────────────────
@pre idx < c.len          │ @pre idx < c.len (unchanged)
@pre valid(c)             │ @pre valid(c:Container[i32])
@post ret.is_some         │ @post ret.is_some (unchanged)
```

#### Effect System

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
- Generic functions with contract propagation
- Effect system integrates with contract verification
- @pure functions provably side-effect free

### v0.21.0: Bounded Generics & Liquid Types

**Goal**: Contract-based type bounds + refinement types

#### Bounded Generics (Contract-Based Bounds)

| Task | Description | Research Basis |
|------|-------------|----------------|
| `where T satisfies` clause | Contract-based bounds | SPARK Ada formal generics |
| Named contract as bound | `where T satisfies @contract Comparable` | Design by Contract |
| Built-in bounds | `Sized`, `Copy`, `Default` | Rust-style but simpler |
| Structural bounds | `where T has .len:u64` | Go-style explicit |

**Syntax Examples**:
```bmb
# Contract as bound - explicit requirement
@contract Comparable(a:T, b:T)
@post ret == -1 || ret == 0 || ret == 1

@node[T] binary_search
@params arr:&[T] target:T
@returns Option[u64]
@where T satisfies @contract Comparable  # ← Explicit bound
@pre sorted(arr)                         # ← Requires Comparable
@post ret.is_some => arr[ret.unwrap] == target
  # ... implementation using compare(a, b)

# Built-in bounds
@node[T] swap
@params a:&T b:&T
@returns void
@where T: Sized                          # ← Must know size at compile time
@pre valid(a) && valid(b)
@post *a == old(*b) && *b == old(*a)
  # ... implementation
```

**What We Avoid (and Why)**:
| Pattern | Problem | BMB Alternative |
|---------|---------|-----------------|
| Type Erasure | Runtime type loss = Omission | Monomorphization |
| Implicit Interface (Go) | Accidental satisfaction = Guessing | Explicit `satisfies` |
| Virtual Dispatch | Unknown callee = Guessing | Static dispatch only |
| Deep Inheritance | Hidden state = Omission | Composition |

#### Liquid Types

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

**Generics + Liquid Types Integration**:
```bmb
# Combine parametric polymorphism with refinement types
@node[T] checked_get
@params arr:&[T; N] idx:u64{idx < N}
@returns &T
@pure
  # Bounds check eliminated - idx < N proven at type level
  # Works for any T - monomorphized per type
  load %val arr idx
  ret %val
```

**Success Criteria**:
- Contract-based type bounds (`where T satisfies`)
- Refinement types integrate with @pre/@post
- Automatic bounds check elimination for proven cases
- Generics + Liquid Types work together seamlessly

---

## Rust Interoperability (v0.21.1 - v0.21.3): Ecosystem Bridge 🦀

> **Strategic Goal**: Address ecosystem gap by enabling BMB ↔ Rust interoperability.
>
> BMB has no ecosystem alone. Rust has crates.io with 150,000+ packages. This phase bridges BMB to Rust's ecosystem, enabling gradual adoption without sacrificing BMB's contract guarantees.

### v0.21.1: C ABI Foundation

| Task | Priority | Description | Research Basis |
|------|----------|-------------|----------------|
| `#[repr(C)]` equivalent | Critical | Explicit struct layout control | Rust FFI |
| Name mangling control | Critical | `@no_mangle` annotation | cbindgen |
| Calling convention enforcement | Critical | Validate @extern ABI | LLVM ABI |
| C header generation | High | `bmbc emit-header` command | cbindgen |

**Syntax Extensions**:
```bmb
# Explicit C-compatible layout
@repr C
@struct Point
  x: f64
  y: f64

# No name mangling - symbol exactly as written
@no_mangle
@pub
@extern "C"
@node calculate_distance
@params p1:*Point p2:*Point
@returns f64
@pre valid(p1) && valid(p2)
  # ... implementation
```

**Header Generation**:
```bash
bmbc emit-header lib.bmb -o lib.h

# Generated:
# typedef struct { double x; double y; } Point;
# double calculate_distance(const Point* p1, const Point* p2);
```

**Success Criteria**:
- C libraries can call BMB functions
- BMB can call C libraries via @extern
- struct layouts match C expectations

### v0.21.2: Rust Type Mapping

| Task | Priority | Description |
|------|----------|-------------|
| Primitive type mapping | Critical | i32↔i32, bool↔bool, etc. |
| Option<T> interop | High | BMB Option ↔ Rust Option (repr(C)) |
| Result<T,E> interop | High | BMB Result ↔ Rust Result |
| Slice/reference mapping | High | &[T] ↔ Slice<T> |
| String mapping | Medium | Str ↔ &str (via ptr+len) |

**Type Mapping Table**:
```
BMB Type        │ Rust Type           │ C ABI Representation
────────────────│─────────────────────│──────────────────────
i32, u64, ...   │ i32, u64, ...       │ Direct (same)
bool            │ bool                │ u8 (0 or 1)
*T              │ *const T / *mut T   │ Pointer
&T              │ &T                  │ Pointer (non-null)
Option<T>       │ Option<T>           │ (discriminant, T) or null-ptr opt
Result<T,E>     │ Result<T,E>         │ (discriminant, union{T,E})
Str             │ &str                │ (*const u8, usize)
String          │ String              │ Opaque (via FFI helpers)
```

**Contract Preservation at FFI Boundary**:
```bmb
# When calling Rust, BMB inserts contract checks
@extern "rust"
@from "mylib"
@node rust_divide
@params a:i32 b:i32
@returns i32
@pre b != 0      # BMB verifies BEFORE calling Rust
@post ret * b == a  # BMB verifies AFTER Rust returns

# This is "Omission is guessing" applied to FFI
# We don't trust Rust's implicit behavior - we verify explicitly
```

**Success Criteria**:
- Rust `#[no_std]` crates usable from BMB
- BMB libraries usable from Rust
- Contract violations at boundary are caught

### v0.21.3: Cargo Integration

| Task | Priority | Description |
|------|----------|-------------|
| `cargo-bmb` subcommand | Critical | Build BMB within Cargo |
| build.rs integration | Critical | Compile .bmb files in Rust projects |
| Dependency management | High | Reference BMB crates from Cargo.toml |
| Mixed Rust/BMB projects | High | Seamless compilation |

**cargo-bmb Workflow**:
```toml
# Cargo.toml
[package]
name = "my_project"

[dependencies]
my_bmb_lib = { path = "./bmb_lib" }

[build-dependencies]
bmb-build = "0.21"
```

```rust
// build.rs
fn main() {
    bmb_build::compile("src/core.bmb")
        .verify(bmb_build::Level::Silver)
        .emit_rust_bindings("src/core_bindings.rs")
        .run();
}
```

```rust
// src/main.rs
mod core_bindings;

fn main() {
    // Call BMB function from Rust
    let result = core_bindings::my_bmb_function(42);
    println!("Result: {}", result);
}
```

**BMB Package Format**:
```toml
# bmb.toml (BMB package manifest, Cargo-compatible structure)
[package]
name = "my_bmb_lib"
version = "0.1.0"
verification_level = "silver"

[dependencies]
std = { version = "0.21" }

[rust-interop]
generate_bindings = true
generate_headers = true
```

**Success Criteria**:
- `cargo bmb build` compiles BMB sources
- Rust projects can depend on BMB packages
- `cargo bmb test` runs contract verification
- Mixed-language debugging works

---

## Silver Stage (v0.22 - v0.24): LLVM Integration

**Goal**: Translate contract knowledge into LLVM optimization hints

### v0.22.0: LLVM Backend Foundation

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

### v0.23.0: Contract-Driven Metadata

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

### v0.24.0: Advanced LLVM Optimization

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

## Gold Stage (v0.25 - v0.27): Performance Transcendence

**Goal**: Surpass C/Rust through proof-guided optimization

### v0.25.0: Proof-Guided Loop Optimization

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

### v0.26.0: Comptime Execution

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

### v0.27.0: SIMD & Vectorization

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

## Tool Ecosystem Maturation (v0.27.1 - v0.27.3): Developer Experience 🛠️

> **Goal**: Transform BMB from a research language to a production-ready tool.
>
> Without good tooling, even the best language fails adoption. This phase builds the developer experience that makes BMB practical for real projects.

### v0.27.1: Package Manager Enhancement

| Task | Priority | Description |
|------|----------|-------------|
| Registry backend | Critical | Central package registry (gotgan.bmb.dev) |
| Semantic versioning | Critical | Contract-aware version resolution |
| Lock file format | High | Reproducible builds |
| Private registries | Medium | Enterprise deployment support |

**Package Resolution with Contracts**:
```toml
# bmb.toml
[dependencies]
http = "^1.0"  # Standard semver
math = { version = "^2.0", verify = "gold" }  # Require Gold verification
```

```bash
# Package manager commands
gotgan add http --verify silver
gotgan update --verify-deps
gotgan publish --verify gold  # Must pass Gold verification to publish
```

**Contract-Aware Versioning Rules**:
```
Major (X.0.0): Contract changes (breaking @pre/@post)
Minor (0.X.0): New features, non-breaking contract additions
Patch (0.0.X): Bug fixes, implementation changes (contracts unchanged)
```

**Success Criteria**:
- `gotgan add/remove/update` works reliably
- Contract verification integrated into publish
- Private registry deployment documented

### v0.27.2: IDE & LSP Enhancement

| Task | Priority | Description |
|------|----------|-------------|
| VS Code extension | Critical | Full-featured BMB extension |
| Contract visualization | High | Inline @pre/@post display |
| Verification status | High | Real-time SMT feedback |
| IntelliJ plugin | Medium | JetBrains family support |
| Neovim LSP config | Medium | Terminal-based development |

**VS Code Features**:
```json
// .vscode/extensions/bmb/features
{
  "inlineContractHints": true,
  "verificationStatusBar": true,
  "smtCounterexampleViewer": true,
  "contractCompletions": true,
  "quickFixSuggestions": true
}
```

**Contract Visualization**:
```
┌─────────────────────────────────────────────────────┐
│ @node divide                                        │
│ @params a:i32 b:nz_i32   ◀── [nz_i32: self != 0]   │
│ @returns i32                                        │
│ @post ret * b == a       ◀── [✓ Verified by SMT]   │
│                                                     │
│   div %r a b                                        │
│   ret %r                                            │
└─────────────────────────────────────────────────────┘
```

**Success Criteria**:
- VS Code extension with 1-click install
- Real-time verification feedback (<2s latency)
- Counterexample visualization works

### v0.27.3: Debugging & Profiling

| Task | Priority | Description |
|------|----------|-------------|
| DWARF debug info | Critical | Source-level debugging |
| GDB/LLDB integration | Critical | Breakpoints, stepping |
| Contract-aware debugger | High | Show active @pre/@post |
| Performance profiler | Medium | Contract overhead analysis |
| Memory profiler | Medium | Allocation tracking |

**Debugging Example**:
```bash
# Compile with debug info
bmbc compile program.bmb -g -o program

# Debug with GDB
gdb program
(gdb) break main
(gdb) run
(gdb) info contracts  # BMB extension: show active contracts
(gdb) verify          # BMB extension: check current @pre
```

**Contract-Aware Debugging**:
```
Breakpoint 1, divide (a=10, b=0) at program.bmb:15
Contract violation: @pre b != 0
  Parameter b = 0 violates precondition

Call stack:
  #0 divide(a=10, b=0) at program.bmb:15
  #1 main() at program.bmb:25
```

**Success Criteria**:
- Source-level debugging works on Linux/macOS/Windows
- Contract violations show clear error messages
- Profiler identifies contract overhead

---

## Benchmark Suite (Parallel Track v0.22+): Proof of Claims 📊

> **Strategic Imperative**: Claims without evidence are marketing, not engineering.
>
> BMB claims "Performance Transcendence" - surpassing C/Rust. This must be proven, not asserted. The benchmark suite runs continuously from v0.22 onwards.

### Benchmark Categories

| Category | Description | Comparison Targets |
|----------|-------------|-------------------|
| **Microbenchmarks** | Single operations (arithmetic, memory) | C, Rust, Zig |
| **Kernels** | Compute kernels (matrix, FFT, sort) | C, Rust, Fortran |
| **Real Programs** | Actual applications (parsers, compressors) | C, Rust implementations |
| **Contract Overhead** | Cost of verification | With/without contracts |

### Benchmark Suite Structure

```
benchmarks/
├── micro/
│   ├── arithmetic.bmb      # Basic ops
│   ├── memory.bmb          # Load/store patterns
│   └── control_flow.bmb    # Branching
├── kernels/
│   ├── matrix_mul.bmb      # Dense matrix multiply
│   ├── quicksort.bmb       # Sorting
│   ├── sha256.bmb          # Hashing
│   └── json_parse.bmb      # Parsing
├── baseline/
│   ├── c/                  # C implementations
│   ├── rust/               # Rust implementations
│   └── zig/                # Zig implementations
└── results/
    ├── 2024-Q1.json
    └── latest.json
```

### Continuous Benchmarking

```yaml
# .github/workflows/benchmark.yml
on:
  push:
    branches: [main]
  schedule:
    - cron: '0 0 * * 0'  # Weekly

jobs:
  benchmark:
    runs-on: [ubuntu-latest, macos-latest, windows-latest]
    steps:
      - run: bmbc bench benchmarks/ --compare baseline/
      - run: |
          if [ $(cat results/latest.json | jq '.regression_detected') == "true" ]; then
            exit 1  # Fail on performance regression
          fi
```

### Performance Tracking Dashboard

```
┌─────────────────────────────────────────────────────────────┐
│ BMB Performance Tracker                          v0.25.0    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Matrix Multiply (1024x1024)                                │
│  ├─ C (gcc -O3):        1.00x (baseline)                   │
│  ├─ Rust (release):     0.98x                              │
│  ├─ BMB (no contracts): 1.02x                              │
│  └─ BMB (verified):     0.97x                              │
│                                                             │
│  Quicksort (1M elements)                                    │
│  ├─ C (gcc -O3):        1.00x                              │
│  ├─ Rust (release):     1.05x                              │
│  ├─ BMB (no contracts): 1.08x  ← Contract elimination win  │
│  └─ BMB (verified):     1.01x                              │
│                                                             │
│  Overall Status: 🟡 Parity (target: 🟢 Transcendence)       │
└─────────────────────────────────────────────────────────────┘
```

### Success Metrics by Version

| Version | Target | Metric |
|---------|--------|--------|
| v0.22.0 | Parity | BMB ≥ 0.8x C on 50% of benchmarks |
| v0.24.0 | Close | BMB ≥ 0.95x C on 80% of benchmarks |
| v0.26.0 | Match | BMB ≥ 1.0x C on 90% of benchmarks |
| v1.0.0 | Transcend | BMB > 1.0x C on verified code paths |

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
| Monomorphic generics | Rust, C++, SPARK Ada | `@struct[T]`, `@node[T]` | Code reuse, zero runtime cost |
| Contract-based bounds | SPARK Ada | `where T satisfies @contract` | Type-safe polymorphism |
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
| **Implementation gap** | **High** | **High** | v0.15.1-v0.15.3 Hardening phase |
| **Rust interop complexity** | Medium | High | Start with C ABI, layer Rust on top |
| **Ecosystem adoption** | High | Critical | Cargo integration, gradual migration path |
| **Benchmark credibility** | Medium | High | Third-party reproducible benchmarks |
| **Tooling debt** | High | Medium | Dedicated v0.27.1-v0.27.3 phase |

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 15.1 | 2025-12-24 | **Major Roadmap Restructure**: Added 4 new phase groups addressing identified gaps. (1) v0.15.1-v0.15.3 Implementation Hardening - verify documented features work. (2) v0.21.1-v0.21.3 Rust Interoperability - C ABI, Rust type mapping, Cargo integration. (3) v0.27.1-v0.27.3 Tool Ecosystem Maturation - package manager, IDE/LSP, debugging. (4) Benchmark Suite parallel track from v0.22+. Added "Positioning Philosophy" section. Updated Risk Register with 5 new risks. |
| 15.0 | 2025-12-24 | v0.15.0 Complete: Exhaustiveness checking for pattern matching (Maranget-style usefulness algorithm), integration tests for non-exhaustive patterns, example BMB programs for @match. String operations deferred to v0.15.1. |
| 14.0 | 2025-12-24 | v0.14.0 Complete: Contract Inference system with frame analysis (@modifies) and postcondition suggestions. Boilerplate reduction through intelligent inference. |
| 13.0 | 2025-12-24 | v0.13.0 Complete: Box<T>/unbox/drop opcodes, enhanced Span, ErrorCollector, File I/O abstraction, CLI argument parser. **Roadmap restructured**: Added v0.14 (Contract Inference), v0.15 (Pattern Matching), v0.16-v0.18 (Self-Hosting phases). Bronze→v0.19-v0.21, Silver→v0.22-v0.24, Gold→v0.25-v0.27. Added Boilerplate Reduction Strategy section. |
| 12.1 | 2025-12-24 | Bronze Stage reorganized: Contract-Propagating Monomorphic Generics integrated (v0.16 Parametric Data Types, v0.17 Generic Functions, v0.18 Bounded Generics) |
| 12.0 | 2025-12-24 | v0.12.0 Complete: @extern FFI with calling conventions, @pub visibility annotation, WASM import modules |
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
