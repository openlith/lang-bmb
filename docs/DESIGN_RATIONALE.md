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

## Why BMB is AI-Native

### The Question

*"Why design a language for AI agents? Shouldn't we focus on human developers?"*

### The Answer: AI is the New Audience

BMB is designed for the AI era. The primary consumer of BMB code is not a human developer typing at a keyboard—it's an AI agent generating, analyzing, and verifying code. This fundamental shift changes everything.

### The Research Evidence

Academic research consistently shows that **explicit constraints HELP AI accuracy**:

| Finding | Source | Implication for BMB |
|---------|--------|---------------------|
| Design constraints boost code generation accuracy | IEEE 2024 | @pre/@post are *signals*, not overhead |
| "Context rot" degrades LLM performance with irrelevant context | Chroma Research | Contracts are relevant; comments may be noise |
| "Lost in the middle" phenomenon | ACL 2024 | Put constraints at function boundaries, not buried in code |
| Preconditions + postconditions reduce false alarms | NL2Contract | Formal contracts > informal comments |

### Signal vs Noise

The critical insight: **Not all tokens are equal.**

| Token Type | AI Impact | Example |
|------------|-----------|---------|
| **Signal** | ✅ HELPS accuracy | `@pre x > 0`, `@post ret >= 0` |
| **Noise** | ❌ HURTS accuracy | `// TODO: fix later`, redundant comments |
| **Context** | ⚠️ Depends on proximity | Spec rules far from use point may be ignored |

BMB's verbose syntax is **high-signal density**. Every line carries meaningful semantic information:

```bmb
@node safe_divide
@params a:i32 b:nz_i32    # Signal: b is non-zero (refined type)
@returns i32
@pre b != 0               # Signal: precondition (redundant with type, but explicit)
@post ret * b == a        # Signal: mathematical relationship

  div %result a b         # Signal: operation
  ret %result             # Signal: explicit return
```

Compare to equivalent C:
```c
int safe_divide(int a, int b) {
    return a / b;  // assumes b != 0 - who validates this?
}
```

The C version is shorter but has **zero signal density**. An AI reading it must *guess* the invariants. BMB makes them explicit.

### The Tooling Imperative

AI-native design requires AI-native tooling:

| Tool | Role | AI Benefit |
|------|------|------------|
| `.bmbmap` | Structural metadata | Context injection for AI |
| LSP | Hover information | Spec rules at point of use |
| Contract expansion | Type → full constraint | Complete context for verification |
| Invariant suggestion | Heuristic → explicit | AI can validate suggestions |

**Key Principle**: Tools exist to *inject* specification context into AI's working memory, not to hide complexity from humans.

---

## The True Cost of Brevity

### The Question

*"BMB code is 10x more lines than C. Isn't that too expensive?"*

### The Answer: The C "3 Lines" Is an Illusion

Consider a simple divide function:

**C (3 lines)**:
```c
int divide(int a, int b) {
    return a / b;
}
```

**BMB (12 lines)**:
```bmb
@node divide
@params a:i32 b:nz_i32
@returns i32
@pre b != 0
@post ret * b == a

  div %result a b
  ret %result
```

The C version *appears* cheaper. But the true cost includes:

| Hidden Cost | C | BMB |
|-------------|---|-----|
| Documentation | External (separate file) | **Inline** (@pre/@post) |
| Unit tests | External (separate file) | **Provable** (SMT verifies) |
| Edge case handling | Manual audit required | **Explicit** (contracts) |
| Code review burden | Reviewer must infer intent | **Self-documenting** |
| Debugging time | Undefined behavior possible | **Impossible** (trap on violation) |
| Maintenance uncertainty | "Will this change break something?" | **Verifiable** (contracts check) |

### The Real Comparison

**Production-ready C code**:
```c
/**
 * Divides a by b.
 * @param a dividend
 * @param b divisor (must be non-zero)
 * @return quotient
 * @pre b != 0
 * @throws undefined behavior if b == 0
 */
int divide(int a, int b) {
    assert(b != 0);  // Debug only, removed in release
    return a / b;
}

// test_divide.c
void test_divide() {
    assert(divide(10, 2) == 5);
    assert(divide(9, 3) == 3);
    assert(divide(-6, 2) == -3);
    // What about divide(5, 0)? Undefined behavior!
}
```

Now count: documentation (6 lines) + code (4 lines) + tests (6 lines) = **16 lines** of C ecosystem, scattered across multiple files, with **no formal guarantee**.

BMB: **12 lines**, self-contained, **mathematically proven correct**.

### The Front-Loading Principle

BMB front-loads all costs:

```
Traditional Development:
  Write code (fast) → Debug (slow) → Document (often skipped) → Test (incomplete) → Maintain (expensive)

BMB Development:
  Write code + contracts (slower upfront) → DONE (verified, documented, tested by construction)
```

The verbosity is not waste—it's **investment**. Every @pre/@post line eliminates hours of future debugging, documentation, and maintenance.

### The AI Perspective

For AI agents, BMB's verbosity is a **feature**:

- **Clear specifications**: AI knows exactly what to generate
- **Verifiable output**: AI can check its own work
- **No guessing**: AI doesn't need to infer implicit requirements
- **Self-documenting**: AI doesn't need external documentation

The "expensive" verbosity is actually the *cheapest* path to correct code.

---

## Signal Density Optimization (v0.8+)

### The Question

*"BMB's verbosity costs tokens in AI-assisted development. Can we reduce syntax without compromising the philosophy?"*

### The Answer: Maximize Signal, Not Minimize Tokens

The original proposal framed this as "token efficiency." Research revealed this framing was wrong.

> **The goal is not fewer tokens. The goal is higher signal-to-noise ratio.**

BMB v0.8 introduces "Signal Density Optimization"—ensuring every token carries maximum semantic information for AI parsing. The revised key insight:

> **"Omission is guessing" applies to unspecified behavior. But optimizing for tokens can also harm AI accuracy if it hides state or removes context.**

### Re-Evaluated Mechanisms

#### 1. Refined Types

Constraints embedded in types are **explicit**, just relocated:

```bmb
# Old: Constraint in function signature
@params b:i32
@pre b != 0

# New: Constraint in type definition
@type nz_i32 i32 where self != 0
@params b:nz_i32    # Type name documents the constraint
```

**Philosophy Alignment**:
- The constraint is visible (in the type name and definition)
- SMT receives the full expanded constraint
- No information is hidden or guessed

#### 2. Spec-Defined Defaults [Conditional]

**Status**: Conditional on tooling. AI needs specification injected into context.

Zero-initialization is **specified behavior**, not implicit:

```bmb
# The spec says: "i32 registers initialize to 0"
# This is not guessing—it's documented, deterministic behavior
```

**Philosophy Alignment** (Partial):
- ✅ Behavior is defined in the language specification
- ✅ Equivalent to explicit `mov %r 0` in semantics
- ⚠️ But AI doesn't know BMB spec unless injected

**AI-Native Concern**:
- AI models don't inherently know BMB specification
- Without spec injection, AI sees "uninitialized" registers
- "Lost in the middle" phenomenon: spec rules often ignored if not proximate to code

**Tooling Requirement**: `.bmbmap` and LSP must surface zero-value rules at point of use. Adoption gated on v0.11.0 Structural Synthesis.

#### 3. Auto-SSA Operator [Deferred]

**Status**: Deferred indefinitely. Hidden state fundamentally conflicts with AI-native design.

The `!` operator **explicitly requests** a new version:

```bmb
add %i! %i 1    # "!" explicitly says: "create new version"
```

**Philosophy Alignment** (Failed):
- ✅ The operator explicitly signals intent
- ❌ But AI must track invisible version numbers mentally
- ❌ Hidden state tracking degrades AI accuracy
- ❌ Error debugging becomes ambiguous ("which version?")

**Decision**: The verbosity cost of explicit SSA names (`%i_1`, `%i_2`) is the correct trade-off. Token count is not the goal; signal clarity is.

### Why Global Profiles Were Rejected

The proposal included "Global Contract Profiles" that would apply contracts implicitly across modules:

```bmb
# REJECTED PROPOSAL
@use_profile std.math.checked  # Auto-applies overflow checks everywhere
```

**Rejection Rationale**:

| Concern | Problem |
|---------|---------|
| **Hidden behavior** | Developer doesn't see which contracts apply to each function |
| **Conflict resolution** | No mechanism for resolving conflicting profiles |
| **Philosophy violation** | "Use profile X" is itself a form of omission—what does X contain? |
| **Debugging difficulty** | Errors may reference contracts from profiles the developer didn't write |

**Key Difference**:
- Refined Types: Type name documents the constraint (`nz_i32` ≈ "non-zero")
- Global Profiles: Profile name hides the constraints (`std.math.checked` ≈ ???)

The philosophy permits **explicit abstraction** (refined types) but rejects **implicit application** (global profiles).

### The AI-Native Litmus Test

When evaluating syntax proposals, apply this enhanced test:

**Philosophy Check** (Original):
1. **Is the behavior specified?** (In spec, type definition, or explicit annotation)
2. **Can a reader understand without external lookup?** (Type name reveals constraint)
3. **Does SMT receive complete information?** (No constraints lost in expansion)

**AI-Native Check** (v0.8+):
4. **Does AI have the context?** (Spec rules must be injectable via tooling)
5. **Is state visible?** (No hidden counters, versions, or implicit tracking)
6. **Does signal density increase?** (Fewer tokens only if per-token meaning increases)

**Evaluation Matrix**:

| Feature | Philosophy | AI-Native | Decision |
|---------|------------|-----------|----------|
| Refined Types | ✅ Pass | ✅ High signal | **Adopt** |
| Spec-Defined Defaults | ✅ Pass | ⚠️ Needs tooling | **Conditional** |
| Auto-SSA Operator | ✅ Pass | ❌ Hidden state | **Defer** |
| Global Profiles | ❌ Fail | ❌ Hidden contracts | **Reject** |

If all six are "yes," the feature is compatible with BMB's AI-native design.

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

BMB's design choices flow from two principles:

1. **"Omission is guessing, and guessing is error."** (Original)
2. **"Signal density over token count."** (AI-Native, v0.8+)

| Choice | Rationale |
|--------|-----------|
| Register-based syntax | Explicit data flow, no hidden temporaries |
| Contract-based safety | Visible requirements, formal verification |
| SSA form | Clean dataflow, direct SMT translation |
| No OOP | No implicit behavior |
| Verbose over concise | Clarity over brevity |
| **AI-native design** | Explicit constraints boost AI accuracy |
| **Signal density** | Every token carries semantic meaning |
| **Tooling-first** | Tools inject context, don't hide complexity |

These choices make BMB different from other languages. They're not limitations to work around but features that enable BMB's unique strengths: formal verification, bare-metal transparency, provable correctness, **and AI-native code generation**.

---

## Further Reading

- [BMB Specification](./SPECIFICATION.md) - Complete language specification
- [BMB Roadmap](./ROADMAP.md) - Development plans and milestones
- [Language Reference](./LANGUAGE_REFERENCE.md) - Syntax and semantics guide
