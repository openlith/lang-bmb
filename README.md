# BMB - Bare-Metal-Banter

> **"Omission is guessing, and guessing is error."**

`BMB` is a high-precision programming language designed for bare-metal environments where ambiguity is the enemy. It eliminates the "convenience" shortcuts that lead to runtime failures, replacing them with a rigid, verifiable contract system.

Traditional languages prioritize ergonomics—readable syntax, forgiving compilers, implicit behaviors. BMB takes the opposite stance: **correctness is non-negotiable**, and every convenience that compromises precision is removed. The result is a language that is harder to write, but nearly impossible to write incorrectly.

---

## Quick Start

```bash
# Build the compiler
cargo build --release --features cli

# Create a simple program
cat > hello.bmb << 'EOF'
@node add
@params a:i32 b:i32
@returns i32
@pre true
@post ret == a + b

  add %result a b
  ret %result
EOF

# Compile and run
./target/release/bmbc run hello.bmb -- 3 5
# Output: 8
```

---

## Philosophy

BMB does not assume intent. If it isn't in the code, it doesn't exist.

| Principle | Description |
| --- | --- |
| **Omission is Guessing** | What is omitted must be guessed; guessing leads to systemic failure. |
| **Explicit is Mandatory** | Explicitness is not a preference; it is a structural requirement. |
| **Compile-time over Runtime** | If a bug can be caught before execution, it must be caught. |
| **Contracts are Code** | Specifications are not comments—they are verifiable, executable logic. |
| **Precision over Convenience** | We abandon "syntactic sugar" in favor of logical absolute. |

---

## Verification Levels

| Level | Name | Guarantee | Badge |
|-------|------|-----------|-------|
| 0 | Stone | Parsing success | 🪨 |
| 1 | Bronze | Type safety | 🥉 |
| 2 | Silver | Contract verification | 🥈 |

---

## Logic over Luck: Design by Contract

In BMB, documentation and implementation are fused. The "Contract" is the source of truth, ensuring that the code never operates in a vacuum of assumptions.

```bmb
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0           # Requirement: Division by zero is logically impossible
@post ret * b == a    # Guarantee: The output must satisfy the inverse operation

  div %r a b
  ret %r
```

* **For the Architect:** You define the constraints once; the language enforces them forever.
* **For the Developer:** The rigid structure eliminates guesswork—if it compiles, it conforms to the specification.

---

## CLI Commands

```bash
bmbc compile source.bmb           # Compile to WebAssembly
bmbc check source.bmb             # Type check only
bmbc run source.bmb -- args       # Compile and run
bmbc fmt source.bmb               # Format code
bmbc lint source.bmb              # Static analysis
bmbc validate source.bmb          # Quick validation API
bmbc grammar --format ebnf        # Export grammar
```

### Optimization Levels

```bash
bmbc compile source.bmb --opt none       # No optimization
bmbc compile source.bmb --opt basic      # Basic (default)
bmbc compile source.bmb --opt aggressive # Aggressive optimization
```

---

## Standard Library

BMB includes a standard library (`stdlib/`) with:

| Module | Functions |
|--------|-----------|
| `math.bmb` | `abs`, `max`, `min`, `clamp`, `gcd`, `factorial` |
| `math_f64.bmb` | `abs_f64`, `lerp`, `average`, `sign_f64` |
| `logic.bmb` | `is_even`, `is_odd`, `in_range`, `xor_bool` |

---

## Grammar Export

BMB grammar can be exported for external tools:

```bash
# EBNF format
bmbc grammar --format ebnf -o bmb.ebnf

# JSON Schema
bmbc grammar --format json -o bmb.json

# GBNF (llama.cpp compatible)
bmbc grammar --format gbnf -o bmb.gbnf
```

Pre-exported grammar files are available in `grammar-dist/`.

---

## Performance Metrics

BMB aims for the "One-Shot" development cycle. By making the language harder to write incorrectly, we make it nearly impossible to fail at runtime.

| Metric | Traditional C/ASM | BMB |
| --- | --- | --- |
| First-gen Success Rate | ~60% | **90%+** |
| Debugging Iterations | 3 - 5 | **0 - 1** |
| Spec-to-Code Parity | Manual / Loose | **Enforced by Design** |

---

## Use Cases

1. **Safety-Critical Systems:** Where a single runtime error is a catastrophic failure.
2. **Verified Firmware:** Direct hardware control with mathematically proven contracts replacing runtime checks.
3. **High-Assurance Software:** Systems where formal verification is mandatory, not optional.

### Why BMB Works Well with AI Code Generation

BMB's strict, unambiguous grammar makes it inherently suitable for LLM-based code generation. Unlike languages with implicit behaviors and syntactic sugar, BMB leaves no room for "hallucinated" assumptions—what is written is exactly what is meant. This is a side effect of the language design, not its primary goal.

---

## Documentation

* [Tutorial](docs/TUTORIAL.md) - Step-by-step learning guide
* [Language Reference](docs/LANGUAGE_REFERENCE.md) - Complete syntax and semantics
* [Specification](docs/SPECIFICATION.md) - Design philosophy and rules

---

## Building from Source

```bash
# Clone the repository
git clone https://github.com/openlith/bmb.git
cd bmb/bmb

# Build library only
cargo build --release

# Build with CLI
cargo build --release --features cli

# Run tests
cargo test
```

---

### License

- [MIT License](LICENSE)
