# BMB Language Reference

> **"Omission is guessing, and guessing is error."**

BMB (Bare-Metal-Banter) is a contract-first programming language designed for AI code generation, targeting WebAssembly.

## Table of Contents

1. [Program Structure](#program-structure)
2. [Types](#types)
3. [Instructions](#instructions)
4. [Contracts](#contracts)
5. [Expressions](#expressions)
6. [Verification Levels](#verification-levels)

---

## Program Structure

A BMB program consists of one or more **nodes** (functions).

### Node Definition

```bmb
@node function_name
@params param1:type1 param2:type2 ...
@returns return_type
@pre precondition_expression
@post postcondition_expression

  instruction1
  instruction2
  ...
```

### Example

```bmb
@node add
@params a:i32 b:i32
@returns i32
@pre true
@post ret == a + b

  add %result a b
  ret %result
```

---

## Types

BMB supports the following primitive types:

| Type | Description | Size | Range |
|------|-------------|------|-------|
| `i32` | 32-bit signed integer | 4 bytes | -2,147,483,648 to 2,147,483,647 |
| `i64` | 64-bit signed integer | 8 bytes | -9,223,372,036,854,775,808 to 9,223,372,036,854,775,807 |
| `f32` | 32-bit floating point | 4 bytes | IEEE 754 single precision |
| `f64` | 64-bit floating point | 8 bytes | IEEE 754 double precision |
| `bool` | Boolean | 1 byte | `true` or `false` |

### Type Promotion in Contracts

In contract expressions, literals are automatically promoted to match parameter types:
- Integer literals in `i64` contexts are promoted to `i64`
- Float literals in `f64` contexts are promoted to `f64`

---

## Instructions

### Arithmetic Operations

| Opcode | Syntax | Description |
|--------|--------|-------------|
| `add` | `add %dest op1 op2` | Addition: dest = op1 + op2 |
| `sub` | `sub %dest op1 op2` | Subtraction: dest = op1 - op2 |
| `mul` | `mul %dest op1 op2` | Multiplication: dest = op1 * op2 |
| `div` | `div %dest op1 op2` | Division: dest = op1 / op2 |
| `mod` | `mod %dest op1 op2` | Modulo: dest = op1 % op2 |

### Comparison Operations

| Opcode | Syntax | Description |
|--------|--------|-------------|
| `eq` | `eq %dest op1 op2` | Equal: dest = (op1 == op2) |
| `ne` | `ne %dest op1 op2` | Not equal: dest = (op1 != op2) |
| `lt` | `lt %dest op1 op2` | Less than: dest = (op1 < op2) |
| `le` | `le %dest op1 op2` | Less or equal: dest = (op1 <= op2) |
| `gt` | `gt %dest op1 op2` | Greater than: dest = (op1 > op2) |
| `ge` | `ge %dest op1 op2` | Greater or equal: dest = (op1 >= op2) |

### Control Flow

| Opcode | Syntax | Description |
|--------|--------|-------------|
| `jmp` | `jmp _label` | Unconditional jump to label |
| `jif` | `jif cond _label` | Jump to label if cond is true |
| `ret` | `ret value` | Return value from function |
| `call` | `call %dest func args...` | Call another function |

### Data Movement

| Opcode | Syntax | Description |
|--------|--------|-------------|
| `mov` | `mov %dest source` | Move/copy value to register |
| `load` | `load %dest source` | Load value (future: memory access) |
| `store` | `store dest source` | Store value (future: memory access) |

### Labels

Labels mark positions for jump targets:

```bmb
_loop:
  # loop body
  jmp _loop
```

- Labels must start with underscore `_`
- Labels are followed by a colon `:`

### Registers

Registers are local variables prefixed with `%`:

```bmb
mov %counter 0
add %counter %counter 1
```

---

## Contracts

Contracts specify function invariants that must hold.

### Preconditions (`@pre`)

Preconditions specify requirements that must be true before function execution:

```bmb
@pre b != 0  # Division requires non-zero divisor
```

### Postconditions (`@post`)

Postconditions specify guarantees after function execution:

```bmb
@post ret >= 0  # Result is non-negative
```

### The `ret` Keyword

In postconditions, `ret` refers to the function's return value:

```bmb
@post ret == a + b  # Return value equals sum of inputs
```

### Contract Examples

```bmb
# Division with safety guarantee
@node safe_divide
@params a:i32 b:i32
@returns i32
@pre b != 0
@post true

  div %r a b
  ret %r

# Absolute value with guarantee
@node abs
@params x:i32
@returns i32
@pre true
@post ret >= 0

  lt %neg x 0
  jif %neg _negate
  ret x
_negate:
  sub %r 0 x
  ret %r
```

---

## Expressions

Expressions are used in contracts and have the following operators:

### Arithmetic Operators

| Operator | Description |
|----------|-------------|
| `+` | Addition |
| `-` | Subtraction |
| `*` | Multiplication |
| `/` | Division |
| `%` | Modulo |

### Comparison Operators

| Operator | Description |
|----------|-------------|
| `==` | Equal |
| `!=` | Not equal |
| `<` | Less than |
| `<=` | Less or equal |
| `>` | Greater than |
| `>=` | Greater or equal |

### Logical Operators

| Operator | Description |
|----------|-------------|
| `&&` | Logical AND |
| `\|\|` | Logical OR |
| `!` | Logical NOT |

### Operator Precedence (highest to lowest)

1. `!`, `-` (unary)
2. `*`, `/`, `%`
3. `+`, `-`
4. `<`, `<=`, `>`, `>=`
5. `==`, `!=`
6. `&&`
7. `\|\|`

---

## Verification Levels

BMB provides multiple verification levels:

| Level | Name | Guarantee | Badge |
|-------|------|-----------|-------|
| 0 | Stone | Parsing success | 🪨 |
| 1 | Bronze | Type safety | 🥉 |
| 2 | Silver | Contract verification (runtime) | 🥈 |

### Using Verification Levels

```bash
# Check to specified level
bmbc check --level silver example.bmb

# Compile with level verification
bmbc compile --level bronze example.bmb
```

---

## Comments

Comments start with `#` and extend to end of line:

```bmb
# This is a comment
@node example  # Inline comment
```

---

## Reserved Keywords

The following identifiers are reserved:

- **Opcodes**: `add`, `sub`, `mul`, `div`, `mod`, `eq`, `ne`, `lt`, `le`, `gt`, `ge`, `ret`, `jmp`, `jif`, `call`, `mov`, `load`, `store`
- **Types**: `i32`, `i64`, `f32`, `f64`, `bool`
- **Literals**: `true`, `false`
- **Directives**: `@node`, `@params`, `@returns`, `@pre`, `@post`

---

## Appendix: Full Grammar (EBNF)

```ebnf
program = node* ;
node = '@node' IDENT params returns contracts body ;
params = '@params' param* ;
param = IDENT ':' type_name ;
returns = '@returns' type_name ;
contracts = (pre | post)* ;
pre = '@pre' expr ;
post = '@post' expr ;
body = (label | stmt)+ ;
label = '_' (ALPHA | DIGIT | '_')+ ':' ;
stmt = opcode operand* ;
opcode = 'add' | 'sub' | 'mul' | 'div' | 'mod' | 'eq' | 'ne' | 'lt' | 'le' | 'gt' | 'ge' | 'ret' | 'jmp' | 'jif' | 'call' | 'mov' | 'load' | 'store' ;
operand = register | label_ref | float_literal | int_literal | IDENT ;
register = '%' (ALPHA | DIGIT | '_')+ ;
label_ref = '_' (ALPHA | DIGIT | '_')+ ;
type_name = 'i32' | 'i64' | 'f32' | 'f64' | 'bool' ;
expr = or_expr ;
or_expr = and_expr ('||' and_expr)* ;
and_expr = comparison ('&&' comparison)* ;
comparison = term (comp_op term)? ;
comp_op = '==' | '!=' | '<=' | '>=' | '<' | '>' ;
term = factor (('+' | '-') factor)* ;
factor = unary (('*' | '/' | '%') unary)* ;
unary = ('!' | '-')? primary ;
primary = '(' expr ')' | float_literal | int_literal | bool_literal | 'ret' | IDENT ;
```
