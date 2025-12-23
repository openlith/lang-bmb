# BMB - Bare-Metal-Banter Specification

**Version:** 0.7.0-draft

---

## 1. Philosophy

### 1.1 Slogan

> **"Omission is guessing, and guessing is error."**

### 1.2 What BMB Is

BMB is not merely a programming language—it is a **proof certificate**.

Traditional languages teach "how to reduce mistakes." BMB **makes mistakes impossible** by construction. The compiled output is not just an executable; it is mathematical evidence that the software conforms to its specification.

### 1.3 Core Principles

| Principle | Technical Implication | Decision Criterion |
| --- | --- | --- |
| **Omission is Guessing** | Implicit behavior is prohibited. Every state change must be declared. | **Enforce Explicit** over Allow Omission |
| **Explicit is Mandatory** | Clarity is a grammatical requirement, not a stylistic choice. | **Required** over Optional |
| **Compile-time over Runtime** | Logic must be mathematically verifiable before execution. | **Static Verification** over Runtime Checks |
| **Contracts are Code** | Formal specifications replace prose documentation. | **Executable Contract** over Text Doc |
| **Precision over Convenience** | The language optimizes for correctness, not ergonomics. Verbosity is acceptable; ambiguity is not. | **Precision** over Convenience |
| **Paradigm Independence** | Traditional patterns (OOP, design patterns) exist for human cognitive limits. BMB does not inherit these constraints. | **Logic** over Convention |

### 1.4 Comments and Documentation are Human Limitations

Traditional programming requires comments and documentation because:
- **Comments**: Compensate for human memory limitations (forgets intent between reads)
- **Documentation**: Compensate for human system-view limitations (can't hold entire codebase)

BMB replaces them with machine-verifiable alternatives:

| Human Limitation Device | BMB Replacement | Property |
| --- | --- | --- |
| Comments | **Contracts** | Verifiable at compile/runtime |
| Documentation | **Index** | Searchable, queryable metadata |

### 1.5 The Two Replacement Systems

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

### 1.6 Self-Describing Syntax

Any reader (human or AI) unfamiliar with BMB should understand it through pattern recognition:

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

### 1.7 Decision Framework

When evaluating language features:

1. **Does this feature allow omission?** → If yes, redesign to make omission impossible.
2. **Is the error discovered at runtime or compile-time?** → Move to compile/verification stage.
3. **Is this for human convenience or precision?** → If convenience (sugar), remove or redesign.
4. **Is this in separate documentation?** → Integrate as verifiable contract or queryable index.
5. **Can an unfamiliar AI understand this from pattern?** → If no, make syntax self-describing.

### 1.8 Terminology

* **Writer**: The entity generating BMB code—human developer, automated tool, or AI assistant.
* **Tool**: The BMB ecosystem (Parser, Type Checker, SMT Solver, Codegen).
* **Proof Certificate**: A compiled BMB binary that serves as mathematical evidence of specification conformance.

---

## 2. Contract System (Replaces Comments)

### 2.1 Contract Types

| Contract | Purpose | Verification | Compact |
| --- | --- | --- | --- |
| `@pre` | Precondition - caller's obligation | Runtime or SMT | `@<` |
| `@post` | Postcondition - function's guarantee | Runtime or SMT | `@>` |
| `@invariant` | Loop invariant - maintained each iteration | SMT proof | `@~` |
| `@variant` | Termination proof - decreasing measure | SMT proof | `@%` |
| `@pure` | No side effects - referentially transparent | Static analysis | `@!` |
| `@requires` | Contract reference - reuse existing contract | Static | `@&` |
| `@assert` | Inline assertion - point-in-time truth | Runtime check | `@!!` |
| `@test` | Executable test case - expected behavior | Test runner | `@?` |

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

### 2.3 Advanced Contract Examples

#### Termination Proof with @variant

```bmb
@node gcd
@params a:i32 b:i32
@returns i32
@pre a >= 0 && b >= 0
@variant a + b                    # Must decrease each recursive call
@post ret >= 1 || (a == 0 && b == 0)

  eq %b_zero b 0
  jif %b_zero _done
  mod %r a b
  call %result gcd b %r
  ret %result
_done:
  ret a
```

#### Pure Functions with @pure

```bmb
@node square
@params x:i32
@returns i32
@pure                             # No side effects, safe to memoize/parallelize
@pre true
@post ret == x * x

  mul %r x x
  ret %r
```

#### Contract Reuse with @requires

```bmb
# Define a reusable contract
@contract valid_index
@params idx:i32 len:i32
@expr idx >= 0 && idx < len

@node array_get
@params arr:[i32;N] idx:i32
@returns i32
@requires valid_index(idx, N)     # Reuse existing contract
@post true

  load %r arr idx
  ret %r
```

### 2.4 Contract Semantics

- **@pre failure**: Caller violated obligation → trap before execution
- **@post failure**: Function violated guarantee → trap after execution
- **@invariant failure**: Loop logic error → verification failure
- **@variant failure**: Termination not proven → compilation failure (Gold level)
- **@pure violation**: Side effect detected → compilation failure
- **@requires failure**: Referenced contract not satisfied → trap or verification failure
- **@assert failure**: Unexpected state → trap at assertion point
- **@test failure**: Behavior mismatch → test report

### 2.5 Writing Loop Invariants (SMT Guide)

Loop invariants are essential for Gold-level verification. An invariant must:

1. **Hold initially**: True before the first iteration
2. **Be preserved**: If true before an iteration, true after
3. **Imply postcondition**: Combined with loop exit condition, proves @post

```bmb
@node sum_to_n
@params n:i32
@returns i32
@pre n >= 0
@post ret == n * (n + 1) / 2

  mov %i 0
  mov %sum 0
_loop:
  @invariant sum == i * (i - 1) / 2    # Partial sum formula
  @invariant i <= n + 1                 # Bounds
  @variant n - i + 1                    # Decreasing measure

  gt %done %i n
  jif %done _exit
  add %sum %sum %i
  add %i %i 1
  jmp _loop
_exit:
  ret %sum
```

**Common Invariant Patterns:**

| Pattern | Invariant Form | Use Case |
| --- | --- | --- |
| Accumulator | `acc == partial_result(i)` | Sum, product, fold |
| Bounds | `lo <= i && i <= hi` | Array traversal |
| Sorted prefix | `sorted(arr[0..i])` | Sorting algorithms |
| Search space | `target in arr[lo..hi]` | Binary search |

---

## 3. Index System (Replaces Documentation)

### 3.1 File Header Block

Every BMB file should begin with a `@file` block that provides machine-readable metadata:

```bmb
@file
@intent "Mathematical utilities with overflow safety guarantees"
@module math.safe
@version 1.0.0
@depends [core.types, core.contracts]
@verified gold
@tags [math, pure, overflow-safe]
@author "BMB Team"

# File content follows...
@node safe_add
...
```

| Directive | Purpose | Required |
| --- | --- | --- |
| `@file` | Marks file header block start | Yes |
| `@intent` | Human/AI-readable purpose description | Yes |
| `@module` | Namespace path | Yes |
| `@version` | File version (semver) | No |
| `@depends` | Explicit dependency list | No |
| `@verified` | Verification level achieved | No |
| `@tags` | Searchable labels | No |
| `@author` | Attribution | No |

### 3.2 Index Directives

| Directive | Purpose | Queryable | Compact |
| --- | --- | --- | --- |
| `@tags [...]` | Searchable labels | By category, purpose, domain | `@#` |
| `@module` | Namespace path | By hierarchy, dependency | `@.` |
| `@version` | Semantic version | By compatibility | - |
| `@author` | Attribution | By contributor | - |
| `@deprecated` | Lifecycle status | By migration needs | - |
| `@intent` | Purpose description | By semantic search | - |
| `@depends` | Dependencies | By dependency graph | - |
| `@verified` | Verification level | By assurance level | - |

### 3.3 Index Examples

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

### 3.4 Index Queries (Tool Support)

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

| Type | Description | WASM Mapping |
| --- | --- | --- |
| `i8`, `i16`, `i32`, `i64` | Signed integers | i32/i64 |
| `u8`, `u16`, `u32`, `u64` | Unsigned integers | i32/i64 (masked) |
| `f32`, `f64` | IEEE 754 Floating point | f32/f64 |
| `bool` | Boolean (`true`/`false`) | i32 |
| `char` | Unicode scalar value (U+0000..U+10FFFF) | i32 |

### 4.4 Composite Types

| Type | Description | Example |
| --- | --- | --- |
| `[T; N]` | Fixed-size array | `[u8; 256]` |
| `&T` | Immutable reference | `&i32` |
| `*T` | Raw pointer | `*u8` |

### 4.5 String Representation

BMB는 편의 문법 없이 문자열을 명시적으로 표현합니다:

```bmb
# 문자열 = 바이트 배열 + 길이
@struct Str
  ptr:*u8      # UTF-8 바이트 포인터
  len:u64      # 바이트 길이

# 문자 리터럴
mov %c 'A'           # char = 65 (ASCII)
mov %c '한'          # char = 54620 (Unicode)

# 바이트 문자열 (data segment)
@data hello "Hello"  # [u8; 5] in memory
```

### 4.6 Instruction Set Architecture (ISA)

| Category | Opcodes |
| --- | --- |
| Arithmetic | `add`, `sub`, `mul`, `div`, `mod` |
| Comparison | `eq`, `ne`, `lt`, `le`, `gt`, `ge` |
| Control Flow | `ret`, `jmp`, `jif`, `call` |
| Memory | `mov`, `load`, `store` |

### 4.7 Operand Syntax

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

## 6. Structural Clarity

> **Note**: The following properties are natural consequences of BMB's design philosophy, not primary design goals. BMB optimizes for precision and verifiability; the resulting structural clarity happens to benefit automated tooling.

### 6.1 Grammar-Constrained Generation

BMB's strict grammar enables constrained decoding for any code generator:

```
Parser State + Grammar Rules → Valid Next Tokens → Syntactically Correct Output
```

This eliminates syntax errors by construction—a side effect of the language's precision requirements.

### 6.2 Pattern Recognition

BMB's consistent syntax allows pattern-based comprehension:

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

The absence of comments and documentation (replaced by contracts and index) naturally reduces token overhead:

| Feature | Reduction | Mechanism |
| --- | --- | --- |
| Compact syntax | 30-40% | `@n` vs `@node` |
| No comments needed | 15-25% | Contracts are self-documenting |
| No documentation | 20-30% | Index replaces prose |
| Consistent prefixes | 10-15% | Pattern-based inference |

---

## 7. Data Modeling (Replaces OOP)

Traditional Object-Oriented Programming exists to help humans manage complexity through abstraction layers. BMB takes a different approach: **constraint-based data modeling** where correctness is enforced through contracts, not encapsulation.

### 7.1 Philosophy: Logic over Abstraction

| OOP Concept | Human Purpose | BMB Alternative |
| --- | --- | --- |
| Class | Bundle data + behavior | `@struct` + Contract-bound functions |
| Encapsulation | Hide implementation | Contracts define interface, not visibility |
| Inheritance | Code reuse | Contract chaining with `@requires` |
| Polymorphism | Runtime dispatch | `@tags` + compile-time dispatch |
| Exceptions | Error handling | Total functions with `@pre` constraints |

### 7.2 Structures with Embedded Constraints

```bmb
@struct User
  id:u64
  age:u8
  @constraint age <= 150           # Structural invariant
  @constraint id > 0               # Never zero

@struct BankAccount
  balance:i64
  @constraint balance >= -1000     # Overdraft limit embedded in type
```

Any function receiving a `User` or `BankAccount` can assume these constraints hold—they are enforced at construction time.

### 7.3 Contract Chaining (Replaces Inheritance)

Instead of inheriting behavior, BMB chains contracts:

```bmb
# Base contract (like an interface)
@contract valid_user
@params u:User
@expr u.age >= 18 && u.id > 0

# Extended contract (like inheritance)
@contract premium_user
@params u:User
@requires valid_user(u)            # Must satisfy base first
@expr u.balance >= 10000

@node grant_premium_access
@params user:User
@returns bool
@requires premium_user(user)       # Full contract chain enforced
@post true

  ret true
```

### 7.4 Tag-Based Dispatch (Replaces Polymorphism)

```bmb
@struct Shape
  tag:u8                           # 0=Circle, 1=Rectangle, 2=Triangle
  data:[f64;4]                     # Uniform storage

@node area
@params s:Shape
@returns f64
@pure
@pre s.tag <= 2

  eq %is_circle s.tag 0
  jif %is_circle _circle
  eq %is_rect s.tag 1
  jif %is_rect _rect
  jmp _triangle

_circle:
  # data[0] = radius
  load %r s.data 0
  mul %r2 %r %r
  mul %area %r2 3.14159
  ret %area

_rect:
  # data[0] = width, data[1] = height
  load %w s.data 0
  load %h s.data 1
  mul %area %w %h
  ret %area

_triangle:
  # data[0] = base, data[1] = height
  load %b s.data 0
  load %h s.data 1
  mul %bh %b %h
  div %area %bh 2.0
  ret %area
```

### 7.5 Total Functions (Replaces Exceptions)

BMB functions must handle all valid inputs. Invalid inputs are rejected at the caller via `@pre`:

```bmb
# WRONG: Partial function with implicit error
@node divide_wrong
@params a:i32 b:i32
@returns i32
  div %r a b          # Crashes on b=0
  ret %r

# CORRECT: Total function with explicit constraint
@node divide
@params a:i32 b:i32
@returns i32
@pre b != 0            # Caller's responsibility
@post ret * b == a     # Mathematical guarantee

  div %r a b
  ret %r
```

### 7.6 When to Use What

| Scenario | OOP Would Use | BMB Uses |
| --- | --- | --- |
| Group related data | Class | `@struct` with `@constraint` |
| Ensure valid state | Constructor validation | Structural `@constraint` |
| Share behavior | Inheritance | `@requires` contract chain |
| Multiple implementations | Interface + polymorphism | `@tags` + static dispatch |
| Handle errors | Try-catch | `@pre` to reject, or Result-like structs |
| Protect invariants | Private fields | `@invariant` in contracts |

---

## 8. Safety Guarantees

BMB is designed to eliminate entire categories of software defects by construction. This section maps common programming errors to BMB's prevention mechanisms.

### 8.1 Defect Categories and Prevention

#### Category 1: Structural Redundancy

| Defect | Description | BMB Prevention |
| --- | --- | --- |
| Code duplication | Same logic in multiple places | `@requires` contract reuse |
| Multiple truth sources | Same data in multiple variables | Single source + contracts |
| Boilerplate bloat | Setup code obscures intent | Contracts ARE the specification |

#### Category 2: Data Integrity

| Defect | Description | BMB Prevention |
| --- | --- | --- |
| Null reference | Access to non-existent value | No null in type system |
| Shared mutable state | Concurrent modification | `@pure` + ownership (future) |
| Implicit coercion | Unintended type conversion | Explicit casts only |
| Uninitialized memory | Reading garbage values | All variables must be initialized |

#### Category 3: Contract Violations

| Defect | Description | BMB Prevention |
| --- | --- | --- |
| Out-of-bounds access | Array index overflow | `@pre idx < len` |
| Division by zero | Arithmetic exception | `@pre divisor != 0` |
| Invalid input | Unvalidated user data | `@pre` at system boundary |
| Broken postcondition | Result doesn't match spec | `@post` verification |

#### Category 4: Resource & Control Flow

| Defect | Description | BMB Prevention |
| --- | --- | --- |
| Resource leak | Memory/handle not freed | Region-based contracts (future) |
| Dead code | Unreachable statements | Optimizer + static analysis |
| Infinite loop | Non-terminating execution | `@variant` termination proof |
| Race condition | Non-deterministic execution | Ownership model (future) |

#### Category 5: Intent Gap

| Defect | Description | BMB Prevention |
| --- | --- | --- |
| Hidden side effects | Undocumented state changes | `@pure` annotation |
| Swallowed exceptions | Silent error handling | Total functions, no exceptions |
| Undocumented assumptions | Implicit developer beliefs | Contracts make assumptions explicit |

### 8.2 Verification Level Coverage

| Defect Category | Stone (0) | Bronze (1) | Silver (2) | Gold (3) |
| --- | --- | --- | --- | --- |
| Syntax errors | ✅ | ✅ | ✅ | ✅ |
| Type mismatches | ❌ | ✅ | ✅ | ✅ |
| Null references | ❌ | ✅ | ✅ | ✅ |
| Contract violations | ❌ | ❌ | Runtime | Static |
| Termination | ❌ | ❌ | ❌ | ✅ |
| Purity violations | ❌ | ❌ | ❌ | ✅ |

---

## 9. Diagnostics

BMB error messages are designed to be **actionable**—each error includes not just what went wrong, but how to fix it.

### 9.1 Error Categories

| Category | Example | Diagnostic Format |
| --- | --- | --- |
| Parse Error | Missing `@returns` | `error[E001]: Expected @returns after @params` |
| Type Error | `i32` ← `f64` | `error[E101]: Type mismatch. Found f64, expected i32. Use to_i32(x) for explicit cast.` |
| Contract Error | `@pre b != 0` | `error[E201]: Precondition may fail. Counterexample: b = 0` |
| Termination Error | Missing `@variant` | `error[E301]: Cannot prove termination. Add @variant with decreasing expression.` |

### 9.2 SMT Counterexamples

When Gold-level verification fails, BMB provides concrete counterexamples:

```
error[E202]: Postcondition violation detected
  --> src/math.bmb:15:1
   |
15 | @post ret >= 0
   |       ^^^^^^^^ This condition can be false
   |
   = Counterexample found:
     Input:  x = -5
     Output: ret = -5

   = Suggestion: Add @pre x >= 0 or modify postcondition
```

### 9.3 Diagnostic Levels

| Level | When | Action |
| --- | --- | --- |
| `error` | Compilation cannot proceed | Must fix |
| `warning` | Potential issue detected | Should review |
| `note` | Additional context | Informational |
| `help` | Suggested fix | Apply or ignore |

---

## 10. Examples

### 10.1 Standard Form

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

### 10.2 Compact Form (Token-Efficient)

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

### 10.3 Division with Full Contracts

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

## 11. Roadmap

See [ROADMAP.md](./ROADMAP.md) for detailed development phases.

| Version | Focus | Status |
| --- | --- | --- |
| 0.1 - 0.6 | Foundation, types, codegen, SMT, Gotgan | ✅ Complete |
| 0.7 | Contract system completion (@variant, @pure) | 🔄 Current |
| 0.8 | Standard library - Collections | Planned |
| 0.9 | Standard library - Strings & Text | Planned |
| 0.10 | Memory management patterns | Planned |
| 0.11 | Diagnostics & actionable errors | Planned |
| 0.12 | FFI & Rust interoperability | Planned |
| 0.13 | Self-hosting preparation | Planned |
| 0.14 | Compiler components in BMB | Planned |
| 0.15 | Bootstrapping | Planned |
| 1.0 | **Self-hosted compiler** | 🎯 Target |

---

## Appendix: Quick Reference Card

```
DIRECTIVES (@)           CONTRACTS               VERIFICATION
─────────────────       ─────────────────       ─────────────────
@node / @n              @pre / @<               Stone (0): Parse
@params / @p            @post / @>              Bronze (1): Types
@returns / @r           @invariant / @~         Silver (2): Runtime
@module / @.            @variant / @%           Gold (3): SMT proof
@tags / @#              @pure / @!
@test / @?              @requires / @&
@file                   @assert / @!!

REGISTERS (%)           TYPES                   OPCODES
─────────────────       ─────────────────       ─────────────────
%name                   i8-i64, u8-u64          add sub mul div mod
%result                 f32, f64                eq ne lt le gt ge
%temp                   bool, char              ret jmp jif call
                        [T; N], &T, *T          mov load store

LABELS (_)
─────────────────
_name:
_loop:
_exit:
```
