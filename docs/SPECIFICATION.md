# BMB - Bare-Metal-Banter Specification

**Version:** 0.4.0

---

## 1. Philosophy

### 1.1 Slogan

> **"Omission is guessing, and guessing is error."**

### 1.2 Core Principles

| Principle | Technical Implication | Decision Criterion |
| --- | --- | --- |
| **Omission is Guessing** | Implicit behavior is prohibited. Every state change must be declared. | **Enforce Explicit** over Allow Omission |
| **Explicit is Mandatory** | Clarity is a grammatical requirement, not a stylistic choice. | **Required** over Optional |
| **Compile-time over Runtime** | Logic must be mathematically verifiable before execution. | **Static Verification** over Runtime Checks |
| **Contracts are Code** | Formal specifications replace prose documentation. | **Executable Contract** over Text Doc |
| **Precision over Convenience** | The language optimizes for correctness, not ergonomics. Verbosity is acceptable; ambiguity is not. | **Precision** over Convenience |

### 1.3 Comments and Documentation are Human Limitations

Traditional programming requires comments and documentation because:
- **Comments**: Compensate for human memory limitations (forgets intent between reads)
- **Documentation**: Compensate for human system-view limitations (can't hold entire codebase)

**In the AI/LLM era, these become obsolete burdens that waste tokens.**

BMB replaces them with machine-verifiable alternatives:

| Human Limitation Device | BMB Replacement | Property |
| --- | --- | --- |
| Comments | **Contracts** | Verifiable at compile/runtime |
| Documentation | **Index** | Searchable, queryable metadata |

### 1.4 The Two Replacement Systems

#### CONTRACTS (Replaces Comments)

Comments describe intent → Contracts **enforce** intent.

```
Comment: "b must not be zero"     →  @pre b != 0
Comment: "returns exact quotient" →  @post ret * b == a
Comment: "loop terminates"        →  @invariant i < n
Comment: "this should work"       →  @test expect(result, 42)
```

#### INDEX (Replaces Documentation)

Documentation describes structure → Index **exposes** structure.

```
README: "Math utilities"          →  @tags [math, utility, pure]
API docs: "In math module"        →  @module math.arithmetic
```

### 1.5 Self-Describing Syntax for AI Comprehension

Any AI unfamiliar with BMB should understand it through pattern recognition:

| Prefix | Meaning | Examples |
| --- | --- | --- |
| `@` | Directive (metadata) | `@node`, `@params`, `@pre`, `@tags` |
| `%` | Register (storage) | `%result`, `%temp`, `%is_zero` |
| `_` | Label (jump target) | `_loop`, `_exit`, `_handle_error` |

**Pattern Recognition Example:**
```bmb
@node add           # @ = directive, "node" = function definition
@params a:i32 b:i32 # name:type pairs
@returns i32        # return type
@pre a >= 0         # precondition (verifiable comment replacement)
@post ret == a + b  # postcondition (verifiable result contract)

  add %result a b   # opcode %dest operands...
  ret %result       # return register value
```

### 1.6 Decision Framework

When evaluating language features:

1. **Does this feature allow omission?** → If yes, redesign to make omission impossible.
2. **Is the error discovered at runtime or compile-time?** → Move to compile/verification stage.
3. **Is this for human convenience or precision?** → If convenience (sugar), remove or redesign.
4. **Is this in separate documentation?** → Integrate as verifiable contract or queryable index.
5. **Can an unfamiliar AI understand this from pattern?** → If no, make syntax self-describing.

### 1.7 Terminology

* **Writer**: The entity generating BMB code—human developer, automated tool, or AI assistant.
* **Tool**: The BMB ecosystem (Parser, Type Checker, SMT Solver, Codegen).

---

## 2. Contract System (Replaces Comments)

### 2.1 Contract Types

| Contract | Purpose | Verification |
| --- | --- | --- |
| `@pre` | Precondition - caller's obligation | Runtime or SMT |
| `@post` | Postcondition - function's guarantee | Runtime or SMT |
| `@invariant` | Loop invariant - maintained each iteration | SMT proof |
| `@assert` | Inline assertion - point-in-time truth | Runtime check |
| `@test` | Executable test case - expected behavior | Test runner |

### 2.2 Contract Examples

```bmb
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0              # Replaces: "Input b cannot be zero"
@post ret * b == a       # Replaces: "Returns exact quotient"
@test expect(divide(10.0, 2.0), 5.0)

  div %r a b
  ret %r
```

```bmb
@node binary_search
@params arr:[i32;N] target:i32 low:i32 high:i32
@returns i32
@pre low >= 0
@pre high < N
@pre low <= high
@invariant low <= mid <= high    # Loop maintains bounds
@post ret == -1 || arr[ret] == target

  # ... implementation
```

### 2.3 Contract Semantics

- **@pre failure**: Caller violated obligation → trap before execution
- **@post failure**: Function violated guarantee → trap after execution
- **@invariant failure**: Loop logic error → verification failure
- **@assert failure**: Unexpected state → trap at assertion point
- **@test failure**: Behavior mismatch → test report

---

## 3. Index System (Replaces Documentation)

### 3.1 Index Directives

| Directive | Purpose | Queryable |
| --- | --- | --- |
| `@tags [...]` | Searchable labels | By category, purpose, domain |
| `@module` | Namespace path | By hierarchy, dependency |
| `@version` | Semantic version | By compatibility |
| `@author` | Attribution | By contributor |
| `@deprecated` | Lifecycle status | By migration needs |

### 3.2 Index Examples

```bmb
@module math.arithmetic
@tags [math, pure, overflow-safe]
@version 1.0.0

@node safe_add
@params a:i32 b:i32
@returns i32
@tags [addition, saturating]
@pre true
@post ret <= 2147483647

  # saturating addition implementation
```

### 3.3 Index Queries (Tool Support)

```bash
# Find all pure math functions
bmbc query --tags "math,pure"

# List functions in module
bmbc query --module "math.arithmetic"

# Find deprecated APIs
bmbc query --deprecated

# Dependency graph
bmbc graph --module "math"
```

---

## 4. Syntax

### 4.1 Full Syntax

```bmb
@node <function_name>
@module <namespace.path>           # Optional: module membership
@tags [<tag1>, <tag2>, ...]        # Optional: searchable labels
@params <name>:<type> ...
@returns <type>
@pre <condition>                   # Optional: multiple allowed
@post <condition>                  # Optional: multiple allowed
@test <test_expression>            # Optional: multiple allowed

  <instructions>
  ret <value>
```

### 4.2 Compact Syntax (Token Efficiency Mode)

For context-limited AI generation, abbreviated forms are valid:

| Full Form | Compact | Meaning |
| --- | --- | --- |
| `@node` | `@n` | Function definition |
| `@params` | `@p` | Parameter list |
| `@returns` | `@r` | Return type |
| `@pre` | `@<` | Precondition (input constraint) |
| `@post` | `@>` | Postcondition (output guarantee) |
| `@tags` | `@#` | Index tags |
| `@test` | `@?` | Test case |
| `@module` | `@.` | Module path |
| `@invariant` | `@~` | Loop invariant |
| `@assert` | `@!` | Inline assertion |

**Compact Example:**
```bmb
@n factorial
@p n:i32
@r i32
@< n >= 0
@> ret >= 1
@? expect(factorial(5), 120)

  eq %z n 0
  jif %z _zero
  sub %m n 1
  call %rec factorial %m
  mul %out n %rec
  ret %out
_zero:
  ret 1
```

### 4.3 Primitive Types

| Type | Description |
| --- | --- |
| `i32`, `i64` | Signed integers (fixed width) |
| `f32`, `f64` | IEEE 754 Floating point |
| `bool` | Boolean (`true`/`false`) |
| `[T; N]` | Fixed-size array |
| `&T` | Immutable reference |

### 4.4 Instruction Set Architecture (ISA)

| Category | Opcodes |
| --- | --- |
| Arithmetic | `add`, `sub`, `mul`, `div`, `mod` |
| Comparison | `eq`, `ne`, `lt`, `le`, `gt`, `ge` |
| Control Flow | `ret`, `jmp`, `jif`, `call` |
| Memory | `mov`, `load`, `store` |

### 4.5 Operand Syntax

| Form | Meaning | Example |
| --- | --- | --- |
| `%name` | Register | `%result`, `%temp` |
| `123` | Integer literal | `42`, `-1` |
| `1.5` | Float literal | `3.14`, `-0.5` |
| `true/false` | Boolean literal | `true` |
| `_label` | Jump target | `_exit`, `_loop` |
| `name` | Parameter reference | `a`, `b` |

---

## 5. Compilation & Verification

### 5.1 Pipeline

```
.bmb Source → Parser → Type Checker → Contract Verifier → Optimizer → Codegen
                                                             ↓
                              ┌──────────────────────────────┼──────────────────────────────┐
                              ↓                              ↓                              ↓
                           .wasm                         Native x64                    Native ARM64
                        (WebAssembly)              ┌────────┼────────┐                     ↓
                                                   ↓        ↓        ↓                   ELF64
                                                ELF64    Mach-O64   PE64               (Linux)
                                               (Linux)   (macOS)  (Windows)
```

### 5.2 Verification Levels (Compliance)

| Level | Name | Requirement | Guarantee |
| --- | --- | --- | --- |
| 0 | **Stone** | Successful AST parsing | Syntactically valid |
| 1 | **Bronze** | Static type safety | Type-correct execution |
| 2 | **Silver** | Runtime contract checks | Contract violations trapped |
| 3 | **Gold** | SMT verification of contracts | Mathematical proof of correctness |

### 5.3 Target Environments

| Target | Format | Use Case |
| --- | --- | --- |
| WebAssembly | `.wasm` | Sandboxed, portable execution |
| Linux x64 | ELF64 | Native Linux binaries |
| macOS x64 | Mach-O64 | Native macOS binaries |
| Windows x64 | PE64 | Native Windows executables |
| Linux ARM64 | ELF64 | ARM64 Linux systems |

---

## 6. AI Integration

### 6.1 Constrained Decoding

BMB provides grammar-aware token prediction for AI code generation:

```
Parser State + Grammar Rules → Valid Next Tokens → Constrained AI Output
```

This eliminates syntax errors in AI-generated code by construction.

### 6.2 Self-Describing Patterns

AI can learn BMB syntax from minimal examples:

**Pattern 1: Directive-first structure**
```
@directive value
@directive name:type
```

**Pattern 2: Register-based operations**
```
opcode %destination source1 source2
```

**Pattern 3: Label-based control flow**
```
jif %condition _target
_target:
  instructions
```

### 6.3 Token Efficiency

| Feature | Token Savings | Mechanism |
| --- | --- | --- |
| Compact syntax | 30-40% | `@n` vs `@node` |
| No comments needed | 15-25% | Contracts are self-documenting |
| No documentation | 20-30% | Index replaces prose |
| Consistent prefixes | 10-15% | Pattern-based inference |

---

## 7. Examples

### 7.1 Standard Form

```bmb
@module math.basic
@tags [math, pure, integer]

@node factorial
@params n:i32
@returns i32
@pre n >= 0
@post ret >= 1
@test expect(factorial(0), 1)
@test expect(factorial(5), 120)

  eq %is_zero n 0
  jif %is_zero _base_case
  sub %n_minus_one n 1
  call %recursive_result factorial %n_minus_one
  mul %final_result n %recursive_result
  ret %final_result
_base_case:
  ret 1
```

### 7.2 Compact Form (Token-Efficient)

```bmb
@. math.basic
@# [math, pure, integer]

@n factorial
@p n:i32
@r i32
@< n >= 0
@> ret >= 1
@? expect(factorial(0), 1)
@? expect(factorial(5), 120)

  eq %z n 0
  jif %z _b
  sub %m n 1
  call %rec factorial %m
  mul %out n %rec
  ret %out
_b:
  ret 1
```

### 7.3 Division with Full Contracts

```bmb
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0              # Division by zero is caller's fault
@post ret * b == a       # Mathematical definition of division
@test expect(divide(10.0, 2.0), 5.0)
@test expect(divide(7.0, 2.0), 3.5)

  div %result a b
  ret %result
```

---

## 8. Roadmap

| Version | Features |
| --- | --- |
| 0.1 | Core syntax, basic types, WASM codegen |
| 0.2 | Arrays, references, native x64 |
| 0.3 | Module system, ARM64 support |
| 0.4 | Index system, compact syntax, AI integration |
| 0.5 | SMT verification (Gold level) |
| 1.0 | Production-ready release |

---

## Appendix: Quick Reference Card

```
DIRECTIVES (@)           REGISTERS (%)           LABELS (_)
─────────────────       ─────────────────       ─────────────────
@node / @n              %name                   _name:
@params / @p            %result                 _loop:
@returns / @r           %temp                   _exit:
@pre / @<
@post / @>              TYPES                   OPCODES
@tags / @#              ─────────────────       ─────────────────
@test / @?              i32, i64                add sub mul div mod
@module / @.            f32, f64                eq ne lt le gt ge
@invariant / @~         bool                    ret jmp jif call
@assert / @!            [T; N]                  mov load store
                        &T
```
