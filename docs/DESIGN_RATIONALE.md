# BMB Design Rationale

> **"Omission is guessing, and guessing is error."**

This document explains the key design decisions in BMB and the philosophy behind them. Understanding these choices helps developers appreciate why BMB works the way it does.

---

## Why Register-Based Syntax?

### The Question

Many developers first encountering BMB ask: *"Why use register-based syntax instead of expression trees?"*

```bmb
# BMB (register-based)
add %sum x y
mul %result %sum z
ret %result

# Hypothetical expression-based alternative
ret (mul (add x y) z)
```

The expression-based syntax appears more concise. So why did BMB choose the register-based approach?

### The Answer: Explicit Data Flow

BMB's register-based syntax is a **deliberate design choice**, not a limitation. It directly embodies our core philosophy: **"Omission is guessing, and guessing is error."**

#### 1. No Hidden Temporaries

Expression trees create implicit temporary values:

```
# Expression tree: ret (mul (add x y) z)
# Compiler internally creates:
#   temp1 = add x y    <- WHERE is this stored?
#   temp2 = mul temp1 z <- HOW LONG does temp1 live?
#   ret temp2
```

These questions have answers, but they're **hidden from the programmer**. In BMB's philosophy, hidden behavior is guessing.

With register-based syntax:

```bmb
add %sum x y       # Explicit: result goes to %sum
mul %result %sum z # Explicit: uses %sum, stores in %result
ret %result        # Explicit: returns %result
```

Every data location and every data movement is visible.

#### 2. Verifiable Data Flow

BMB's contract system can verify properties about specific registers:

```bmb
@node safe_divide
@params a:i32 b:i32
@returns i32
@pre b != 0
@post %result == a / b    # Can reference specific register

  div %result a b
  ret %result
```

With expression trees, contracts would need to reference implicit temporaries or use complex path expressions.

#### 3. Bare-Metal Transparency

BMB targets bare-metal environments where developers need to understand exactly what the compiler generates. Register-based syntax provides a 1:1 mental model with the generated code:

| BMB Source | Generated WASM |
|------------|----------------|
| `add %r x y` | `local.get $x; local.get $y; i32.add; local.set $r` |
| `ret %r` | `local.get $r; return` |

With expression trees, the mapping becomes compiler-dependent and non-obvious.

#### 4. Optimization Visibility

When BMB's optimizer eliminates dead code or folds constants, you can see exactly what changes:

```bmb
# Before optimization
mov %unused 42    # Dead store - will be eliminated
add %result x y
ret %result

# After optimization (visible in --emit ir)
add %result x y
ret %result
```

Expression trees hide these optimizations inside the compiler.

### The Trade-off

Yes, register-based syntax requires more lines of code. This is intentional:

| Aspect | Expression Trees | Register-Based |
|--------|------------------|----------------|
| Conciseness | More concise | More verbose |
| Data flow visibility | Hidden | **Explicit** |
| Contract precision | Indirect | **Direct** |
| Bare-metal mapping | Abstracted | **Transparent** |
| Learning curve | Gentler | Steeper |

BMB optimizes for **correctness and transparency**, not ergonomics. For safety-critical bare-metal systems, explicit data flow is worth the verbosity cost.

### Mitigation: Tooling

BMB's tooling helps manage the verbosity:

1. **LSP Integration**: Register usage highlighting, dead store detection
2. **Formatter**: Consistent alignment of register assignments
3. **Linter**: Warns about unused registers, suggests simplifications
4. **IR Viewer**: `bmbc compile --emit ir` shows optimized register usage

---

## Why Contracts Instead of Ownership?

### The Question

Rust uses ownership and borrowing for memory safety. Why does BMB use contracts instead?

### The Answer: Verification Over Restriction

Rust's approach: **Restrict what you can write** to prevent errors.

BMB's approach: **Verify what you write** is correct.

```bmb
# BMB: State your guarantees explicitly
@node safe_deref
@params ptr:*i32
@returns i32
@pre valid(ptr)           # Explicit validity contract
@pre not_null(ptr)        # Explicit null check
@pre aligned(ptr, 4)      # Explicit alignment

  load %val ptr 0
  ret %val
```

This approach has several advantages:

1. **No Hidden Rules**: All safety requirements are visible in the contract
2. **Flexible**: Can express properties ownership can't (e.g., "these pointers don't alias")
3. **Verifiable**: SMT solver proves contracts hold at compile time
4. **Gradual**: Start with runtime checks (Silver), upgrade to static proofs (Gold)

The trade-off is that you must write the contracts. But in BMB's philosophy, making requirements explicit is a feature, not a burden.

---

## Why Static Single Assignment (SSA)?

BMB uses SSA form internally, and this shows through in the syntax. Each register assignment creates a new "version" of the value.

### Benefits

1. **Simpler Dataflow Analysis**: Each definition has exactly one use-def chain
2. **Easier Optimization**: Dead code elimination, constant propagation become straightforward
3. **Contract Verification**: SMT translation is direct from SSA form

### In Practice

```bmb
# Each register assigned once per path
mov %i 0
_loop:
  add %i_next %i 1    # New version for loop
  lt %done %i_next 10
  jif %done _loop _end
_end:
  ret %i_next
```

---

## Why No OOP?

BMB deliberately excludes object-oriented programming constructs (classes, inheritance, virtual dispatch).

### The Reason: Implicit Behavior

OOP introduces implicit behavior that conflicts with BMB's philosophy:

| OOP Construct | Implicit Behavior |
|---------------|-------------------|
| Constructor | Automatic initialization |
| Destructor | Automatic cleanup |
| Virtual dispatch | Runtime method resolution |
| Inheritance | Hidden parent behavior |

Instead, BMB uses **constraint-based data modeling**:

```bmb
@struct Buffer
  data:*u8
  len:u64
  cap:u64
  @constraint len <= cap              # Structural invariant
  @constraint cap > 0 || data == null # Valid state contract
```

All behavior is explicit. All constraints are visible and verifiable.

---

## Frequently Asked Questions

### Q: Isn't the verbose syntax slower to write?

**A:** Yes, but BMB optimizes for reading and verification, not writing speed. Code is read far more often than written, especially in safety-critical systems where audits are common.

### Q: Can I use expression syntax in the future?

**A:** There are no plans to add expression tree syntax. It would undermine the explicit data flow that makes BMB's verification powerful. However, tooling improvements (better LSP, snippets, templates) continue to reduce friction.

### Q: Why not provide both syntaxes?

**A:** Supporting two syntaxes would:
1. Double the parser/AST/codegen complexity
2. Create inconsistent code styles across projects
3. Undermine the "one way to do things" principle

BMB chooses one syntax and makes it work well.

### Q: Is BMB suitable for rapid prototyping?

**A:** No. BMB is designed for **production-critical systems** where correctness matters more than development speed. For prototyping, use a higher-level language, then port to BMB when requirements are stable.

### Q: How does BMB compare to Rust?

| Aspect | Rust | BMB |
|--------|------|-----|
| Safety mechanism | Ownership + Borrowing | Contracts + SMT |
| Syntax | Expression-based | Register-based |
| Paradigm | Multi-paradigm | Procedural + Contracts |
| Learning curve | Steep (ownership) | Steep (contracts) |
| Target | General systems | Bare-metal, safety-critical |
| Verification | Type system | Formal proofs |

They solve similar problems differently. BMB's approach is more explicit and formally verifiable; Rust's approach is more ergonomic and catches errors earlier in the type system.

### Q: What about IDE support for register tracking?

**A:** The BMB LSP server provides:
- Register definition/usage highlighting
- Dead register detection
- Register lifetime visualization
- Contract hover information

Use `bmb-lsp` with VS Code, Neovim, or any LSP-compatible editor.

---

## Summary

BMB's design choices all flow from one principle: **"Omission is guessing, and guessing is error."**

| Choice | Rationale |
|--------|-----------|
| Register-based syntax | Explicit data flow, no hidden temporaries |
| Contract-based safety | Visible requirements, formal verification |
| SSA form | Clean dataflow, direct SMT translation |
| No OOP | No implicit behavior |
| Verbose over concise | Clarity over brevity |

These choices make BMB different from other languages. They're not limitations to work around but features that enable BMB's unique strengths: formal verification, bare-metal transparency, and provable correctness.

---

## Further Reading

- [BMB Specification](./SPECIFICATION.md) - Complete language specification
- [BMB Roadmap](./ROADMAP.md) - Development plans and milestones
- [Language Reference](./LANGUAGE_REFERENCE.md) - Syntax and semantics guide
