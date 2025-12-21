# BMB Tutorial

> **"Omission is guessing, and guessing is error."**

Welcome to BMB! This tutorial will guide you through writing your first BMB programs.

## Getting Started

### Installation

```bash
# Clone the repository
git clone https://github.com/openlith/bmb.git
cd bmb

# Build the compiler
cargo build --release --features cli

# Add to PATH (optional)
export PATH=$PATH:$(pwd)/target/release
```

### Your First Program

Create a file `hello.bmb`:

```bmb
@node add_two
@params a:i32 b:i32
@returns i32
@pre true
@post ret == a + b

  add %result a b
  ret %result
```

Compile and run:

```bash
# Compile to WebAssembly
bmbc compile hello.bmb

# Or compile and run directly
bmbc run hello.bmb -- 3 5
# Output: 8
```

---

## Understanding BMB Structure

### Nodes (Functions)

Every BMB function is called a **node**. A node has:

1. **Name**: Unique identifier
2. **Parameters**: Input values with types
3. **Return type**: Output value type
4. **Contracts**: Pre/post conditions
5. **Body**: Instructions

```bmb
@node function_name        # 1. Name
@params x:i32 y:i32       # 2. Parameters
@returns i32               # 3. Return type
@pre x >= 0                # 4. Precondition
@post ret >= x             # 4. Postcondition

  add %r x y               # 5. Body
  ret %r
```

### Types

BMB is strongly typed. Available types:

| Type | Example | Description |
|------|---------|-------------|
| `i32` | `42` | 32-bit integer |
| `i64` | `9999999999` | 64-bit integer |
| `f32` | `3.14` | 32-bit float |
| `f64` | `3.141592653589793` | 64-bit float |
| `bool` | condition result | Boolean |

---

## Step-by-Step Examples

### Example 1: Maximum of Two Numbers

```bmb
@node max
@params a:i32 b:i32
@returns i32
@pre true
@post ret >= a && ret >= b

  gt %a_greater a b
  jif %a_greater _ret_a
  ret b
_ret_a:
  ret a
```

**Explanation:**
1. `gt %a_greater a b` - Compare a > b, store result in %a_greater
2. `jif %a_greater _ret_a` - If true, jump to _ret_a
3. `ret b` - Otherwise return b
4. `ret a` - Return a (jumped here if a > b)

Run it:
```bash
bmbc run max.bmb -- 10 20
# Output: 20
```

### Example 2: Absolute Value

```bmb
@node abs
@params x:i32
@returns i32
@pre true
@post ret >= 0

  lt %is_negative x 0
  jif %is_negative _negate
  ret x
_negate:
  sub %result 0 x
  ret %result
```

**Explanation:**
1. Check if x < 0
2. If negative, jump to negate it
3. Return original if positive
4. Compute 0 - x and return

### Example 3: Factorial

```bmb
@node factorial
@params n:i32
@returns i32
@pre n >= 0 && n <= 12
@post ret >= 1

  eq %is_zero n 0
  jif %is_zero _base_case

  mov %result 1
  mov %counter 1
_loop:
  gt %done %counter n
  jif %done _end
  mul %result %result %counter
  add %counter %counter 1
  jmp _loop

_base_case:
  mov %result 1
  ret %result
_end:
  ret %result
```

**Note the precondition**: `n <= 12` prevents integer overflow!

### Example 4: GCD (Euclidean Algorithm)

```bmb
@node gcd
@params a:i32 b:i32
@returns i32
@pre a >= 0 && b >= 0
@post ret >= 0

  eq %b_zero b 0
  jif %b_zero _done
_loop:
  mod %rem a b
  mov a b
  mov b %rem
  eq %b_zero b 0
  jif %b_zero _done
  jmp _loop
_done:
  ret a
```

---

## Understanding Contracts

Contracts are the heart of BMB. They specify:
- **@pre**: What must be true BEFORE the function runs
- **@post**: What will be true AFTER the function completes

### Why Contracts Matter

```bmb
# BAD: No contract - division might fail
@node divide_bad
@params a:i32 b:i32
@returns i32
@pre true
@post true

  div %r a b
  ret %r

# GOOD: Contract prevents division by zero
@node divide_good
@params a:i32 b:i32
@returns i32
@pre b != 0
@post true

  div %r a b
  ret %r
```

The linter will warn you about division without a non-zero check:

```bash
bmbc lint divide_bad.bmb
# warning at line 7: [W003] division by 'b' without precondition check
#   help: add '@pre b != 0' to prevent division by zero
```

### Contract Expressions

Contracts use expression syntax:

```bmb
# Arithmetic
@pre a + b < 100

# Comparisons
@pre x >= 0 && x < 10

# Return value reference
@post ret == a + b

# Complex conditions
@pre (a > 0 && b > 0) || (a < 0 && b < 0)
```

---

## Control Flow Patterns

### If-Then-Else Pattern

```bmb
# if (condition) { ... } else { ... }
  eq %cond x 0
  jif %cond _then_branch
  # else branch code
  jmp _endif
_then_branch:
  # then branch code
_endif:
  # continue
```

### Loop Pattern

```bmb
# while (condition) { ... }
_loop:
  lt %continue i n
  jif %continue _loop_body
  jmp _loop_end
_loop_body:
  # loop body
  add %i %i 1
  jmp _loop
_loop_end:
  # after loop
```

### For Loop Pattern

```bmb
# for (i = 0; i < n; i++) { ... }
  mov %i 0
_for:
  ge %done %i n
  jif %done _for_end
  # loop body
  add %i %i 1
  jmp _for
_for_end:
```

---

## Working with Floats

```bmb
@node average
@params a:f64 b:f64
@returns f64
@pre true
@post true

  add %sum a b
  div %avg %sum 2.0
  ret %avg
```

Float operations work similarly to integer operations.

---

## CLI Commands

### Compile

```bash
# Compile to WASM
bmbc compile source.bmb

# Compile with specific output
bmbc compile source.bmb -o output.wasm

# Output WAT (text format)
bmbc compile source.bmb --emit wat

# Print AST
bmbc compile source.bmb --emit ast

# Optimization levels
bmbc compile source.bmb --opt none      # No optimization
bmbc compile source.bmb --opt basic     # Basic (default)
bmbc compile source.bmb --opt aggressive # Aggressive
```

### Check

```bash
# Type check only
bmbc check source.bmb

# Check to specific level
bmbc check source.bmb --level bronze
```

### Run

```bash
# Run with arguments
bmbc run source.bmb -- arg1 arg2

# Run specific function
bmbc run source.bmb --func multiply -- 3 4
```

### Format

```bash
# Print formatted code
bmbc fmt source.bmb

# Format in place
bmbc fmt source.bmb --write

# Check formatting (for CI)
bmbc fmt source.bmb --check
```

### Lint

```bash
# Lint for issues
bmbc lint source.bmb

# Treat warnings as errors
bmbc lint source.bmb --deny-warnings
```

### Validate

```bash
# Quick validation
bmbc validate source.bmb

# JSON output (for tooling)
bmbc validate source.bmb --json
```

### Grammar Export

```bash
# Export EBNF grammar
bmbc grammar --format ebnf

# Export for llama.cpp
bmbc grammar --format gbnf -o bmb.gbnf

# Export JSON schema
bmbc grammar --format json
```

---

## Standard Library

BMB includes a standard library in `stdlib/`:

### math.bmb
- `abs(x)` - Absolute value
- `max(a, b)` - Maximum
- `min(a, b)` - Minimum
- `clamp(x, low, high)` - Clamp to range
- `gcd(a, b)` - Greatest common divisor
- `factorial(n)` - Factorial (n! for n ≤ 12)

### math_f64.bmb
- `abs_f64(x)` - Absolute value (float)
- `lerp(a, b, t)` - Linear interpolation
- `average(a, b)` - Average of two values

### logic.bmb
- `is_even(x)` - Check if even
- `is_odd(x)` - Check if odd
- `in_range(x, low, high)` - Range check
- `xor_bool(a, b)` - XOR operation

---

## Best Practices

1. **Always write contracts** - Even `@pre true` and `@post true` is better than nothing.

2. **Use meaningful names** - `%counter` is better than `%c`.

3. **Check division** - Always have `@pre divisor != 0` before division.

4. **Document range limits** - Use preconditions to prevent overflow.

5. **Use the linter** - `bmbc lint` catches common mistakes.

6. **Format consistently** - Use `bmbc fmt --write` to maintain style.

---

## Next Steps

- Read the [Language Reference](LANGUAGE_REFERENCE.md) for complete syntax
- Explore the [Standard Library](../bmb/stdlib/) for examples
- Check the [Specification](SPECIFICATION.md) for design rationale
