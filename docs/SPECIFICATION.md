# BMB - Bare-Metal-Banter Specification

**Version:** 0.1

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
| **Writer Diligence** | Optimized for a tireless writer (AI) rather than human brevity. | **Precision** over Convenience |

### 1.3 Decision Framework

When evaluating language features or implementation details, the **BMB Framework** must be applied:

1. **Does this feature allow omission?** * If yes, redesign to make it impossible to omit.
2. **Is the error discovered at runtime or compile-time?** * If runtime, move the discovery to the compile/verification stage.
3. **Is this for human convenience or writer accuracy?** * If human convenience (sugar), remove or redesign for accuracy.
4. **Is this information in separate documentation?** * If yes, integrate it into the language spec as a verifiable contract.

### 1.4 Terminology

* **Writer**: The entity generating BMB code (primarily AI, but includes high-precision human developers).
* **Tool**: The BMB ecosystem (Parser, Type Checker, SMT Solver, Codegen).

### 1.5 Code = Documentation

BMB eliminates the "Sync Gap" between code and documentation by promoting specifications to first-class citizens.

* **Traditional:** `Code + README + Comments + API Docs = Inconsistency`
* **BMB:** `Verified Code + Verifiable Contracts = Absolute Truth`

**The "Doc-to-Contract" Promotion:**

* **Comments**  Promoted to `@pre` / `@post` contracts (must be verifiable).
* **API Descriptions**  Expressed through rigorous Type Definitions.
* **Meta Info**  Extracted on-demand by tools (e.g., dependency graphs, complexity analysis).

---

## 2. Goals

### 2.1 Quantitative Benchmarks

| Metric | Industry Standard (C/Asm) | BMB Target |
| --- | --- | --- |
| First-generation Success Rate | 60% | **90%+** |
| Debug Iterations | 3 - 5 | **0 - 1** |
| Syntax Error Frequency | 5 - 15% | **0%** |
| Type/Logic Discrepancy | 10 - 20% | **0%** |

### 2.2 Scope of Responsibility

| BMB Guarantees | BMB Does Not Guarantee |
| --- | --- |
| Syntactic integrity | High-level business logic alignment |
| Strict type safety | Accuracy of external requirements |
| Formally verified contracts | Unstated/Omitted constraints |
| Deterministic memory safety | Performance at the cost of safety |

---

## 3. Syntax

### 3.1 Function Definition (`@node`)

Every unit of execution must define its boundaries and expectations explicitly.

```bmb
@node <function_name>
@params <name>:<type> ...
@returns <type>
@pre <condition>
@post <condition>

  <instructions>
  ret <value>

```

### 3.2 Primitive Types

| Type | Description |
| --- | --- |
| `i32`, `i64` | Signed integers (fixed width) |
| `f32`, `f64` | IEEE 754 Floating point |
| `bool` | Boolean (explicit `true`/`false`) |
| `[T; N]` | Fixed-size array (v0.2) |
| `&T` | Immutable reference (v0.2) |

### 3.3 Instruction Set Architecture (ISA)

* **Arithmetic:** `add`, `sub`, `mul`, `div`, `mod`
* **Comparison:** `eq`, `lt`, `gt`, `le`, `ge`, `ne`
* **Control Flow:** `ret`, `jmp`, `jif` (jump-if), `call`
* **Memory/Registers:** `mov`, `load`, `store`

### 3.4 Formal Contracts

Contracts replace prose. A BMB file is effectively a mathematical proof.

```bmb
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0           # Documentation: "Input b cannot be zero"
@post ret * b == a    # Documentation: "Returns the exact quotient"

  div %r a b
  ret %r

```

---

## 4. Compilation & Verification

### 4.1 Pipeline

```
.bmb Source → Parser → Type Checker → SMT/Contract Verifier → Codegen → .wasm

```

### 4.2 Verification Levels (Compliance)

| Level | Name | Requirement |
| --- | --- | --- |
| 0 | **Stone** | Successful AST parsing |
| 1 | **Bronze** | Static type safety and register allocation |
| 2 | **Silver** | Mathematical verification of all `@pre` and `@post` conditions |

### 4.3 Target Environment

**WebAssembly (WASI)**: Providing a sandboxed, deterministic execution environment for bare-metal logic.

---

## 5. Examples

### Recursive Factorial with Constraints

```bmb
@node factorial
@params n:i32
@returns i32
@pre n >= 0
@post ret >= 1

  eq %is_zero n 0
  jif %is_zero _handle_zero
  sub %n_minus_one n 1
  call %rec_result factorial %n_minus_one
  mul %final_result n %rec_result
  ret %final_result
_handle_zero:
  ret 1

```
