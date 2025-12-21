# BMB - Bare-Metal-Banter

**Version 0.1**

---

## 1. Philosophy

### 1.1 Slogan

> **"Omission is guessing, and guessing is error."**

### 1.2 Core Principles

| Principle | Description | Decision Criterion |
|-----------|-------------|-------------------|
| **Omission is Guessing** | What is omitted must be guessed. Guessing leads to errors. | Allow omission vs Enforce explicit → Enforce |
| **Explicit is Mandatory** | Explicitness is not preferred, it's grammatically enforced. | Optional vs Required → Required |
| **Compile-time over Runtime** | Errors should be caught at compile-time, not runtime. | Runtime check vs Compile check → Compile |
| **Contracts are Code** | Contracts are verified code, not comments. | Documentation vs Contract → Contract |
| **Writer Diligence over Human Convenience** | Assumes tireless writer (AI), abandons human convenience. | Write less vs Write precisely → Precisely |

### 1.3 Decision Framework

When facing a choice during development:

```
Q1: Does this feature allow omission?
    → Yes → Make it impossible to omit

Q2: Is it discovered at runtime or compile-time?
    → Runtime → Move to compile-time

Q3: Is it for human convenience or writer accuracy?
    → Human convenience → Remove or redesign

Q4: Is this information in separate documentation?
    → Yes → Integrate into language spec (contracts)
```

### 1.4 Terminology

| Term | Meaning |
|------|---------|
| **Writer** | The entity that writes BMB code (AI or human) |
| **Tool** | Compiler, analyzer, and other BMB processing systems |

BMB is designed assuming the writer is AI. Humans can write BMB, but human convenience is not considered.

### 1.5 Code = Documentation

**Traditional paradigm:**
```
Code + README + Comments + API docs + Diagrams
  ↓
Sync issues, stale docs, scattered information
```

**BMB paradigm:**
```
Code = Documentation
  ↓
Contracts (@pre, @post) are both spec and docs
Types are both description and constraint
Derived info is generated on-demand by tools
```

**Principles:**
- Comments → Promoted to contracts (must be verifiable)
- Descriptions → Expressed as types/contracts (code is docs)
- Meta info → Generated on-demand by tools (dependencies, complexity, call graphs, etc.)

---

## 2. Goals

### 2.1 Quantitative Goals

| Metric | Current (Traditional) | Target (BMB) |
|--------|----------------------|--------------|
| First-gen success rate | 60% | 90%+ |
| Debug iterations | 3-5 | 0-1 |
| Syntax errors | 5-15% | 0% |
| Type errors | 10-20% | 0% |

### 2.2 Scope of Responsibility

| BMB Guarantees | BMB Does Not Guarantee |
|----------------|------------------------|
| Syntax correctness | Business logic correctness |
| Type safety | Requirements alignment |
| Stated contract verification | Unstated constraints |
| Memory safety | Performance optimization |

---

## 3. Syntax

### 3.1 Structure

```bmb
@node <function_name>
@params <name>:<type> ...
@returns <type>
@pre <precondition>
@post <postcondition>

  <instructions>
  ret <value>
```

### 3.2 Types

| Type | Description |
|------|-------------|
| `i32`, `i64` | Signed integers |
| `f32`, `f64` | Floating point |
| `bool` | Boolean |
| `[T; N]` | Fixed array (v0.2) |
| `&T` | Reference (v0.2) |

### 3.3 Instructions

**Arithmetic:** `add`, `sub`, `mul`, `div`, `mod`
**Comparison:** `eq`, `lt`, `gt`, `le`, `ge`, `ne`
**Control:** `ret`, `jmp`, `jif`, `call`
**Variables:** `mov`, `load`, `store`

### 3.4 Contracts

```bmb
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0           # Precondition: b is not zero
@post ret * b == a    # Postcondition: result verification

  div %r a b
  ret %r
```

Contracts = Documentation:
- `@pre b != 0` replaces "b must not be zero" documentation
- `@post ret * b == a` replaces "guarantees correct division" documentation
- No separate explanation needed (contracts are the spec)

---

## 4. Compilation

### 4.1 Pipeline

```
.bmb → Parser → Type Checker → Contract Checker → Codegen → .wasm
```

### 4.2 Verification Levels

| Level | Name | Guarantee |
|-------|------|-----------|
| 0 | Stone | Parsing success |
| 1 | Bronze | Type safety |
| 2 | Silver | Contract verification |

### 4.3 Target

WebAssembly (WASI)

---

## 5. Examples

```bmb
@node factorial
@params n:i32
@returns i32
@pre n >= 0
@post ret >= 1

  eq %base n 0
  jif %base _one
  sub %n1 n 1
  call %r factorial %n1
  mul %r n %r
  ret %r
_one:
  ret 1
```

---

## 6. Roadmap

- [x] Philosophy definition
- [x] Syntax design
- [ ] Parser
- [ ] Type checker
- [ ] Contract checker
- [ ] Wasm codegen
