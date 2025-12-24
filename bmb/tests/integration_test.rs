//! Integration tests for BMB compiler
//!
//! Tests the full pipeline: Source → Parse → Type Check → Codegen → Execute

use bmb::{codegen, contracts, parser, types};
use wasmtime::*;

/// Compile BMB source to WebAssembly and return the binary
fn compile_bmb(source: &str) -> Vec<u8> {
    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    codegen::generate(&verified).expect("code generation failed")
}

#[test]
fn test_execute_simple_add() {
    let source = r#"
# Simple addition function
@node sum
@params a:i32 b:i32
@returns i32

  add %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    // Execute with wasmtime
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let sum = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "sum")
        .expect("sum function not found");

    // Test: 3 + 5 = 8
    let result = sum.call(&mut store, (3, 5)).expect("call failed");
    assert_eq!(result, 8);

    // Test: -10 + 25 = 15
    let result = sum.call(&mut store, (-10, 25)).expect("call failed");
    assert_eq!(result, 15);

    // Test: 0 + 0 = 0
    let result = sum.call(&mut store, (0, 0)).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_f64_operations() {
    let source = r#"
# Float division
@node divide
@params a:f64 b:f64
@returns f64

  div %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let divide = instance
        .get_typed_func::<(f64, f64), f64>(&mut store, "divide")
        .expect("divide function not found");

    // Test: 10.0 / 2.0 = 5.0
    let result = divide.call(&mut store, (10.0, 2.0)).expect("call failed");
    assert!((result - 5.0).abs() < 1e-10);

    // Test: 7.0 / 3.0 ≈ 2.333...
    let result = divide.call(&mut store, (7.0, 3.0)).expect("call failed");
    assert!((result - 2.333333333333333).abs() < 1e-10);
}

#[test]
fn test_execute_multiplication() {
    let source = r#"
# Multiplication
@node multiply
@params x:i32 y:i32
@returns i32

  mul %result x y
  ret %result
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let multiply = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "multiply")
        .expect("multiply function not found");

    // Test: 6 * 7 = 42
    let result = multiply.call(&mut store, (6, 7)).expect("call failed");
    assert_eq!(result, 42);

    // Test: -3 * 4 = -12
    let result = multiply.call(&mut store, (-3, 4)).expect("call failed");
    assert_eq!(result, -12);
}

#[test]
fn test_execute_subtraction() {
    let source = r#"
@node subtract
@params a:i32 b:i32
@returns i32

  sub %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let subtract = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "subtract")
        .expect("subtract function not found");

    // Test: 10 - 3 = 7
    let result = subtract.call(&mut store, (10, 3)).expect("call failed");
    assert_eq!(result, 7);
}

#[test]
fn test_execute_comparison() {
    let source = r#"
# Returns true if a < b, false otherwise
@node less_than
@params a:i32 b:i32
@returns bool

  lt %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let less_than = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "less_than")
        .expect("less_than function not found");

    // Test: 3 < 5 = true (1)
    let result = less_than.call(&mut store, (3, 5)).expect("call failed");
    assert_eq!(result, 1);

    // Test: 5 < 3 = false (0)
    let result = less_than.call(&mut store, (5, 3)).expect("call failed");
    assert_eq!(result, 0);

    // Test: 3 < 3 = false (0)
    let result = less_than.call(&mut store, (3, 3)).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_mov_identity() {
    let source = r#"
# Identity function using mov
@node identity
@params x:i32
@returns i32

  mov %r x
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let identity = instance
        .get_typed_func::<i32, i32>(&mut store, "identity")
        .expect("identity function not found");

    // Test: identity(42) = 42
    let result = identity.call(&mut store, 42).expect("call failed");
    assert_eq!(result, 42);

    // Test: identity(-100) = -100
    let result = identity.call(&mut store, -100).expect("call failed");
    assert_eq!(result, -100);
}

#[test]
fn test_execute_chained_operations() {
    let source = r#"
# Compute (a + b) * c
@node expr
@params a:i32 b:i32 c:i32
@returns i32

  add %temp a b
  mul %result %temp c
  ret %result
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let expr = instance
        .get_typed_func::<(i32, i32, i32), i32>(&mut store, "expr")
        .expect("expr function not found");

    // Test: (2 + 3) * 4 = 20
    let result = expr.call(&mut store, (2, 3, 4)).expect("call failed");
    assert_eq!(result, 20);

    // Test: (10 + -5) * 6 = 30
    let result = expr.call(&mut store, (10, -5, 6)).expect("call failed");
    assert_eq!(result, 30);
}

#[test]
fn test_execute_modulo() {
    let source = r#"
@node modulo
@params a:i32 b:i32
@returns i32

  mod %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let modulo = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "modulo")
        .expect("modulo function not found");

    // Test: 10 % 3 = 1
    let result = modulo.call(&mut store, (10, 3)).expect("call failed");
    assert_eq!(result, 1);

    // Test: 15 % 5 = 0
    let result = modulo.call(&mut store, (15, 5)).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_multiple_functions() {
    let source = r#"
# Two functions in one module

@node square
@params x:i32
@returns i32

  mul %r x x
  ret %r

@node cube
@params x:i32
@returns i32

  mul %temp x x
  mul %r %temp x
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let square = instance
        .get_typed_func::<i32, i32>(&mut store, "square")
        .expect("square function not found");

    let cube = instance
        .get_typed_func::<i32, i32>(&mut store, "cube")
        .expect("cube function not found");

    // Test: square(5) = 25
    let result = square.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 25);

    // Test: cube(3) = 27
    let result = cube.call(&mut store, 3).expect("call failed");
    assert_eq!(result, 27);
}

// ========== Contract Checking Tests ==========

#[test]
fn test_precondition_satisfied() {
    let source = r#"
# Division with precondition: divisor cannot be zero
@node safe_divide
@params a:i32 b:i32
@returns i32
@pre b != 0

  div %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let safe_divide = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "safe_divide")
        .expect("safe_divide function not found");

    // Test: 10 / 2 = 5 (precondition satisfied)
    let result = safe_divide.call(&mut store, (10, 2)).expect("call failed");
    assert_eq!(result, 5);
}

#[test]
fn test_precondition_violated_traps() {
    let source = r#"
# Division with precondition: divisor cannot be zero
@node safe_divide
@params a:i32 b:i32
@returns i32
@pre b != 0

  div %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let safe_divide = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "safe_divide")
        .expect("safe_divide function not found");

    // Test: 10 / 0 should trap (precondition violated)
    let result = safe_divide.call(&mut store, (10, 0));
    assert!(result.is_err(), "should trap on precondition violation");
}

#[test]
fn test_postcondition_satisfied() {
    let source = r#"
# Function that always returns positive
@node positive_square
@params x:i32
@returns i32
@post ret >= 0

  mul %r x x
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let positive_square = instance
        .get_typed_func::<i32, i32>(&mut store, "positive_square")
        .expect("positive_square function not found");

    // Test: square(5) = 25 >= 0 (postcondition satisfied)
    let result = positive_square.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 25);

    // Test: square(-3) = 9 >= 0 (postcondition satisfied)
    let result = positive_square.call(&mut store, -3).expect("call failed");
    assert_eq!(result, 9);
}

#[test]
fn test_f64_precondition() {
    let source = r#"
# Float division with precondition
@node divide_f64
@params a:f64 b:f64
@returns f64
@pre b != 0.0

  div %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let divide_f64 = instance
        .get_typed_func::<(f64, f64), f64>(&mut store, "divide_f64")
        .expect("divide_f64 function not found");

    // Test: 10.0 / 2.0 = 5.0 (precondition satisfied)
    let result = divide_f64
        .call(&mut store, (10.0, 2.0))
        .expect("call failed");
    assert!((result - 5.0).abs() < 1e-10);

    // Test: 10.0 / 0.0 should trap (precondition violated)
    let result = divide_f64.call(&mut store, (10.0, 0.0));
    assert!(result.is_err(), "should trap on precondition violation");
}

#[test]
fn test_combined_pre_and_post() {
    let source = r#"
# Function with both precondition and postcondition
@node bounded_increment
@params x:i32
@returns i32
@pre x >= 0
@post ret > x

  add %r x 1
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bounded_increment = instance
        .get_typed_func::<i32, i32>(&mut store, "bounded_increment")
        .expect("bounded_increment function not found");

    // Test: 5 + 1 = 6 > 5 (both conditions satisfied)
    let result = bounded_increment.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 6);

    // Test: -1 should trap (precondition violated)
    let result = bounded_increment.call(&mut store, -1);
    assert!(result.is_err(), "should trap on precondition violation");
}

// ========== Assertion Tests ==========

#[test]
fn test_assertion_satisfied() {
    let source = r#"
# Function with assertion for non-negative input
@node safe_increment
@params x:i32
@returns i32
@assert x >= 0

  add %r x 1
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let safe_increment = instance
        .get_typed_func::<i32, i32>(&mut store, "safe_increment")
        .expect("safe_increment function not found");

    // Test: 5 + 1 = 6 (assertion satisfied)
    let result = safe_increment.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 6);

    // Test: 0 + 1 = 1 (assertion satisfied on boundary)
    let result = safe_increment.call(&mut store, 0).expect("call failed");
    assert_eq!(result, 1);
}

#[test]
fn test_assertion_violated_traps() {
    let source = r#"
# Function with assertion for non-negative input
@node safe_increment
@params x:i32
@returns i32
@assert x >= 0

  add %r x 1
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let safe_increment = instance
        .get_typed_func::<i32, i32>(&mut store, "safe_increment")
        .expect("safe_increment function not found");

    // Test: -1 should trap (assertion violated)
    let result = safe_increment.call(&mut store, -1);
    assert!(result.is_err(), "should trap on assertion violation");
}

#[test]
fn test_multiple_assertions() {
    let source = r#"
# Function with multiple assertions
@node bounded_value
@params n:i32
@returns i32
@assert n >= 0
@assert n <= 100

  mov %r n
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bounded_value = instance
        .get_typed_func::<i32, i32>(&mut store, "bounded_value")
        .expect("bounded_value function not found");

    // Test: 50 is in range (both assertions satisfied)
    let result = bounded_value.call(&mut store, 50).expect("call failed");
    assert_eq!(result, 50);

    // Test: 0 is on lower boundary (both assertions satisfied)
    let result = bounded_value.call(&mut store, 0).expect("call failed");
    assert_eq!(result, 0);

    // Test: 100 is on upper boundary (both assertions satisfied)
    let result = bounded_value.call(&mut store, 100).expect("call failed");
    assert_eq!(result, 100);

    // Test: -1 should trap (first assertion violated)
    let result = bounded_value.call(&mut store, -1);
    assert!(result.is_err(), "should trap on assertion violation");

    // Test: 101 should trap (second assertion violated)
    let result = bounded_value.call(&mut store, 101);
    assert!(result.is_err(), "should trap on assertion violation");
}

#[test]
fn test_assertion_with_precondition() {
    let source = r#"
# Function with both precondition and assertion
@node safe_divide
@params a:i32 b:i32
@returns i32
@pre b != 0
@assert b != 0

  div %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let safe_divide = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "safe_divide")
        .expect("safe_divide function not found");

    // Test: 10 / 2 = 5 (both precondition and assertion satisfied)
    let result = safe_divide.call(&mut store, (10, 2)).expect("call failed");
    assert_eq!(result, 5);

    // Test: 10 / 0 should trap (both precondition and assertion violated)
    let result = safe_divide.call(&mut store, (10, 0));
    assert!(result.is_err(), "should trap on contract violation");
}

#[test]
fn test_execute_loop_with_jmp() {
    let source = r#"
# Loop using jmp for backward jump
@node loop_demo
@params
@returns i32
@pre true
@post ret == 10

  mov %count 0
_loop:
  add %count %count 1
  lt %continue %count 10
  jif %continue _loop
  ret %count
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let loop_demo = instance
        .get_typed_func::<(), i32>(&mut store, "loop_demo")
        .expect("loop_demo function not found");

    // Test: loop increments until count == 10
    let result = loop_demo.call(&mut store, ()).expect("call failed");
    assert_eq!(result, 10);
}

#[test]
fn test_execute_nested_loops() {
    // Nested loops using only backward jumps (no forward jumps yet)
    // Pattern: outer loop runs inner loop completely each iteration
    // Total iterations = outer * inner
    let source = r#"
# Nested loops: multiply via counting
# Uses only backward jumps - no forward jump blocks needed
@node nested_loop
@params outer:i32 inner:i32
@returns i32
@pre outer >= 0
@pre inner >= 0

  mov %total 0
  mov %i 0
_outer_loop:
  mov %j 0
_inner_loop:
  add %total %total 1
  add %j %j 1
  lt %inner_continue %j inner
  jif %inner_continue _inner_loop
  add %i %i 1
  lt %outer_continue %i outer
  jif %outer_continue _outer_loop
  ret %total
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let nested_loop = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "nested_loop")
        .expect("nested_loop function not found");

    // Test: 3 * 4 = 12 total iterations
    let result = nested_loop.call(&mut store, (3, 4)).expect("call failed");
    assert_eq!(result, 12);

    // Test: 5 * 5 = 25 total iterations
    let result = nested_loop.call(&mut store, (5, 5)).expect("call failed");
    assert_eq!(result, 25);
}

#[test]
fn test_execute_forward_jump() {
    // Forward jump using jif - jumps ahead to a label
    let source = r#"
# Forward jump test - conditional early return
@node abs_value
@params n:i32
@returns i32
@pre true
@post ret >= 0

  ge %is_positive n 0
  jif %is_positive _positive
  sub %r 0 n
  ret %r
_positive:
  ret n
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let abs_value = instance
        .get_typed_func::<i32, i32>(&mut store, "abs_value")
        .expect("abs_value function not found");

    // Test positive: 5 -> 5
    let result = abs_value.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 5);

    // Test negative: -7 -> 7
    let result = abs_value.call(&mut store, -7).expect("call failed");
    assert_eq!(result, 7);

    // Test zero: 0 -> 0
    let result = abs_value.call(&mut store, 0).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_factorial_recursive() {
    // Recursive factorial with forward jump
    let source = r#"
# Factorial function - recursive with forward jump
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
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let factorial = instance
        .get_typed_func::<i32, i32>(&mut store, "factorial")
        .expect("factorial function not found");

    // Test: 0! = 1
    let result = factorial.call(&mut store, 0).expect("call failed");
    assert_eq!(result, 1);

    // Test: 5! = 120
    let result = factorial.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 120);

    // Test: 7! = 5040
    let result = factorial.call(&mut store, 7).expect("call failed");
    assert_eq!(result, 5040);
}

// ========== Advanced Type Tests (i64, f32, f64) ==========

#[test]
fn test_execute_i64_operations() {
    let source = r#"
# i64 addition with large values
@node sum64
@params a:i64 b:i64
@returns i64
@pre true
@post ret == a + b

  add %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let sum64 = instance
        .get_typed_func::<(i64, i64), i64>(&mut store, "sum64")
        .expect("sum64 function not found");

    // Test: basic addition
    let result = sum64.call(&mut store, (100, 200)).expect("call failed");
    assert_eq!(result, 300);

    // Test: large values beyond i32 range
    let result = sum64
        .call(&mut store, (5_000_000_000, 3_000_000_000))
        .expect("call failed");
    assert_eq!(result, 8_000_000_000);

    // Test: negative values
    let result = sum64
        .call(&mut store, (-1_000_000_000_000, 500_000_000_000))
        .expect("call failed");
    assert_eq!(result, -500_000_000_000);
}

#[test]
fn test_execute_f32_operations() {
    let source = r#"
# f32 multiplication
@node product32
@params x:f32 y:f32
@returns f32
@pre true
@post true

  mul %r x y
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let product32 = instance
        .get_typed_func::<(f32, f32), f32>(&mut store, "product32")
        .expect("product32 function not found");

    // Test: basic multiplication
    let result = product32.call(&mut store, (2.5, 4.0)).expect("call failed");
    assert!((result - 10.0).abs() < 1e-5);

    // Test: small values
    let result = product32
        .call(&mut store, (0.001, 1000.0))
        .expect("call failed");
    assert!((result - 1.0).abs() < 1e-5);

    // Test: negative values
    let result = product32
        .call(&mut store, (-3.0, 5.0))
        .expect("call failed");
    assert!((result - (-15.0)).abs() < 1e-5);
}

#[test]
fn test_execute_i64_with_contract() {
    let source = r#"
# i64 multiplication with precondition and postcondition
# Type promotion allows comparing i64 with i32 literals
@node safe_mul64
@params a:i64 b:i64
@returns i64
@pre a >= 0
@pre b >= 0
@post ret >= 0
@post ret == a * b

  mul %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let safe_mul64 = instance
        .get_typed_func::<(i64, i64), i64>(&mut store, "safe_mul64")
        .expect("safe_mul64 function not found");

    // Test: valid multiplication
    let result = safe_mul64
        .call(&mut store, (1000, 2000))
        .expect("call failed");
    assert_eq!(result, 2_000_000);

    // Test: large values
    let result = safe_mul64
        .call(&mut store, (1_000_000, 1_000_000))
        .expect("call failed");
    assert_eq!(result, 1_000_000_000_000);

    // Test: precondition violation (negative value) should trap
    let result = safe_mul64.call(&mut store, (-1, 100));
    assert!(result.is_err(), "should trap on precondition violation");
}

#[test]
fn test_execute_f32_division() {
    let source = r#"
# f32 division with precondition
# Type promotion allows comparing f32 with f64 literal (0.0)
@node divide32
@params a:f32 b:f32
@returns f32
@pre b != 0.0

  div %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let divide32 = instance
        .get_typed_func::<(f32, f32), f32>(&mut store, "divide32")
        .expect("divide32 function not found");

    // Test: valid division
    let result = divide32.call(&mut store, (10.0, 4.0)).expect("call failed");
    assert!((result - 2.5).abs() < 1e-5);

    // Test: negative result
    let result = divide32
        .call(&mut store, (-15.0, 3.0))
        .expect("call failed");
    assert!((result - (-5.0)).abs() < 1e-5);

    // Test: precondition violation (divide by zero) should trap
    let result = divide32.call(&mut store, (10.0, 0.0));
    assert!(result.is_err(), "should trap on precondition violation");
}

// ========== Bitwise Operation Tests ==========

#[test]
fn test_execute_bitwise_and() {
    let source = r#"
# Bitwise AND operation
@node bitwise_and
@params a:i32 b:i32
@returns i32

  and %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bitwise_and = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "bitwise_and")
        .expect("bitwise_and function not found");

    // Test: 0xFF00 & 0x0F0F = 0x0F00
    let result = bitwise_and.call(&mut store, (0xFF00, 0x0F0F)).expect("call failed");
    assert_eq!(result, 0x0F00);

    // Test: 0b1010 & 0b1100 = 0b1000 (10 & 12 = 8)
    let result = bitwise_and.call(&mut store, (10, 12)).expect("call failed");
    assert_eq!(result, 8);

    // Test: any & 0 = 0
    let result = bitwise_and.call(&mut store, (0xFFFFFFFF_u32 as i32, 0)).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_bitwise_or() {
    let source = r#"
# Bitwise OR operation
@node bitwise_or
@params a:i32 b:i32
@returns i32

  or %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bitwise_or = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "bitwise_or")
        .expect("bitwise_or function not found");

    // Test: 0xFF00 | 0x00FF = 0xFFFF
    let result = bitwise_or.call(&mut store, (0xFF00, 0x00FF)).expect("call failed");
    assert_eq!(result, 0xFFFF);

    // Test: 0b1010 | 0b1100 = 0b1110 (10 | 12 = 14)
    let result = bitwise_or.call(&mut store, (10, 12)).expect("call failed");
    assert_eq!(result, 14);

    // Test: any | 0 = any
    let result = bitwise_or.call(&mut store, (42, 0)).expect("call failed");
    assert_eq!(result, 42);
}

#[test]
fn test_execute_bitwise_xor() {
    let source = r#"
# Bitwise XOR operation
@node bitwise_xor
@params a:i32 b:i32
@returns i32

  xor %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bitwise_xor = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "bitwise_xor")
        .expect("bitwise_xor function not found");

    // Test: 0xFF00 ^ 0x0FF0 = 0xF0F0
    let result = bitwise_xor.call(&mut store, (0xFF00, 0x0FF0)).expect("call failed");
    assert_eq!(result, 0xF0F0);

    // Test: 0b1010 ^ 0b1100 = 0b0110 (10 ^ 12 = 6)
    let result = bitwise_xor.call(&mut store, (10, 12)).expect("call failed");
    assert_eq!(result, 6);

    // Test: XOR self = 0 (self-inverse property)
    let result = bitwise_xor.call(&mut store, (12345, 12345)).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_bitwise_shl() {
    let source = r#"
# Bitwise shift left
@node shift_left
@params a:i32 n:i32
@returns i32

  shl %r a n
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let shift_left = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "shift_left")
        .expect("shift_left function not found");

    // Test: 1 << 4 = 16
    let result = shift_left.call(&mut store, (1, 4)).expect("call failed");
    assert_eq!(result, 16);

    // Test: 3 << 2 = 12
    let result = shift_left.call(&mut store, (3, 2)).expect("call failed");
    assert_eq!(result, 12);

    // Test: 0xFF << 8 = 0xFF00
    let result = shift_left.call(&mut store, (0xFF, 8)).expect("call failed");
    assert_eq!(result, 0xFF00);
}

#[test]
fn test_execute_bitwise_shr() {
    let source = r#"
# Bitwise shift right (arithmetic)
@node shift_right
@params a:i32 n:i32
@returns i32

  shr %r a n
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let shift_right = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "shift_right")
        .expect("shift_right function not found");

    // Test: 16 >> 4 = 1
    let result = shift_right.call(&mut store, (16, 4)).expect("call failed");
    assert_eq!(result, 1);

    // Test: 0xFF00 >> 8 = 0xFF
    let result = shift_right.call(&mut store, (0xFF00, 8)).expect("call failed");
    assert_eq!(result, 0xFF);

    // Test: Arithmetic shift preserves sign: -8 >> 2 = -2
    let result = shift_right.call(&mut store, (-8, 2)).expect("call failed");
    assert_eq!(result, -2);
}

#[test]
fn test_execute_bitwise_not() {
    let source = r#"
# Bitwise NOT operation
@node bitwise_not
@params a:i32
@returns i32

  not %r a
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bitwise_not = instance
        .get_typed_func::<i32, i32>(&mut store, "bitwise_not")
        .expect("bitwise_not function not found");

    // Test: ~0 = -1 (all bits set)
    let result = bitwise_not.call(&mut store, 0).expect("call failed");
    assert_eq!(result, -1);

    // Test: ~(-1) = 0
    let result = bitwise_not.call(&mut store, -1).expect("call failed");
    assert_eq!(result, 0);

    // Test: ~1 = -2 (binary: ...11111110)
    let result = bitwise_not.call(&mut store, 1).expect("call failed");
    assert_eq!(result, -2);
}

#[test]
fn test_execute_bitwise_combined() {
    let source = r#"
# Combined bitwise operations: extract bits
# Extract bits 4-7 from input: (a >> 4) & 0xF
@node extract_nibble
@params a:i32
@returns i32

  shr %shifted a 4
  and %r %shifted 15
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let extract_nibble = instance
        .get_typed_func::<i32, i32>(&mut store, "extract_nibble")
        .expect("extract_nibble function not found");

    // Test: 0xAB -> second nibble = 0xA = 10
    let result = extract_nibble.call(&mut store, 0xAB).expect("call failed");
    assert_eq!(result, 0xA);

    // Test: 0x1234 -> nibble at position 1 = 0x3
    let result = extract_nibble.call(&mut store, 0x1234).expect("call failed");
    assert_eq!(result, 0x3);
}

#[test]
fn test_execute_bitwise_i64() {
    let source = r#"
# i64 bitwise operations
@node bitwise_and64
@params a:i64 b:i64
@returns i64

  and %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bitwise_and64 = instance
        .get_typed_func::<(i64, i64), i64>(&mut store, "bitwise_and64")
        .expect("bitwise_and64 function not found");

    // Test: Large 64-bit values
    let result = bitwise_and64
        .call(&mut store, (0xFF00FF00FF00FF00_u64 as i64, 0x0F0F0F0F0F0F0F0F_u64 as i64))
        .expect("call failed");
    assert_eq!(result, 0x0F000F000F000F00_u64 as i64);
}

#[test]
fn test_requires_contract_expansion() {
    // Test @requires contract chaining
    // The @contract defines reusable preconditions
    // @requires expands them into the function
    let source = r#"
# Define a reusable contract
@contract positive(n:i32)
@pre n > 0

@node double
@params x:i32
@returns i32
@requires positive(x)  # Expands to @pre x > 0

  add %r x x
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let double = instance
        .get_typed_func::<i32, i32>(&mut store, "double")
        .expect("double function not found");

    // Test: Valid input (x > 0)
    let result = double.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 10);

    // Test: Another valid input
    let result = double.call(&mut store, 100).expect("call failed");
    assert_eq!(result, 200);
}

#[test]
fn test_requires_contract_violation_traps() {
    // Test that @requires expanded preconditions trap on violation
    let source = r#"
@contract positive(n:i32)
@pre n > 0

@node double
@params x:i32
@returns i32
@requires positive(x)

  add %r x x
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let double = instance
        .get_typed_func::<i32, i32>(&mut store, "double")
        .expect("double function not found");

    // Test: Invalid input (x = 0, violates x > 0)
    let result = double.call(&mut store, 0);
    assert!(
        result.is_err(),
        "Should trap when precondition is violated"
    );

    // Test: Invalid input (x = -5, violates x > 0)
    let result = double.call(&mut store, -5);
    assert!(
        result.is_err(),
        "Should trap when precondition is violated"
    );
}

#[test]
fn test_requires_multiple_contracts() {
    // Test @requires with multiple contracts and multiple parameters
    let source = r#"
@contract bounded(n:i32, max:i32)
@pre n > 0
@pre n < max

@node safe_add
@params a:i32 b:i32
@returns i32
@requires bounded(a, 100)
@requires bounded(b, 100)

  add %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let safe_add = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "safe_add")
        .expect("safe_add function not found");

    // Test: Valid inputs (both a, b > 0 and < 100)
    let result = safe_add.call(&mut store, (10, 20)).expect("call failed");
    assert_eq!(result, 30);

    // Test: Invalid input (a = 0, violates a > 0)
    let result = safe_add.call(&mut store, (0, 50));
    assert!(result.is_err(), "Should trap when a <= 0");

    // Test: Invalid input (a = 100, violates a < 100)
    let result = safe_add.call(&mut store, (100, 50));
    assert!(result.is_err(), "Should trap when a >= 100");
}

// ============================================================================
// @pure Purity Verification Tests
// ============================================================================

#[test]
fn test_pure_function_valid() {
    // A valid @pure function with only pure operations
    let source = r#"
@node double
@params x:i32
@returns i32
@pure

  add %r x x
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let double = instance
        .get_typed_func::<i32, i32>(&mut store, "double")
        .expect("double function not found");

    let result = double.call(&mut store, 21).expect("call failed");
    assert_eq!(result, 42);
}

#[test]
fn test_pure_calling_pure_valid() {
    // A @pure function can call another @pure function
    let source = r#"
@node double
@params x:i32
@returns i32
@pure

  add %r x x
  ret %r

@node quadruple
@params x:i32
@returns i32
@pure

  call %tmp double x
  call %r double %tmp
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let quadruple = instance
        .get_typed_func::<i32, i32>(&mut store, "quadruple")
        .expect("quadruple function not found");

    let result = quadruple.call(&mut store, 10).expect("call failed");
    assert_eq!(result, 40);
}

#[test]
fn test_pure_calling_impure_fails() {
    // A @pure function cannot call a non-@pure function
    let source = r#"
@node impure_double
@params x:i32
@returns i32

  add %r x x
  ret %r

@node pure_caller
@params x:i32
@returns i32
@pure

  call %r impure_double x
  ret %r
"#;

    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let result = contracts::verify(&typed);

    assert!(result.is_err(), "Should fail: @pure calls impure function");
    let err = result.unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("Purity violation") && msg.contains("impure_double"),
        "Error should mention purity violation and impure function: {}",
        msg
    );
}

#[test]
fn test_pure_with_print_fails() {
    // A @pure function cannot use print (I/O)
    let source = r#"
@node log_and_double
@params x:i32
@returns i32
@pure

  print "doubling"
  add %r x x
  ret %r
"#;

    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let result = contracts::verify(&typed);

    assert!(result.is_err(), "Should fail: @pure uses print");
    let err = result.unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("Purity violation") && msg.contains("print"),
        "Error should mention purity violation and print: {}",
        msg
    );
}

// ============================================================================
// @invariant Loop Invariant Verification Tests
// ============================================================================

#[test]
fn test_invariant_loop_valid() {
    // A loop with a valid invariant that holds throughout execution
    // Pattern: do work, check condition, jump back if true
    let source = r#"
@node count_up
@params limit:i32
@returns i32
@invariant _loop count >= 0

  mov %count 0
_loop:
  add %count %count 1
  lt %continue %count limit
  jif %continue _loop
  ret %count
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let count_up = instance
        .get_typed_func::<i32, i32>(&mut store, "count_up")
        .expect("count_up function not found");

    // count from 0 to 10
    let result = count_up.call(&mut store, 10).expect("call failed");
    assert_eq!(result, 10);
}

#[test]
fn test_invariant_violation_traps() {
    // A loop where invariant is violated at entry when start < 0
    let source = r#"
@node count_from
@params start:i32 limit:i32
@returns i32
@invariant _loop count >= 0

  mov %count start
_loop:
  add %count %count 1
  lt %continue %count limit
  jif %continue _loop
  ret %count
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let count_from = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "count_from")
        .expect("count_from function not found");

    // Valid: start=0, invariant count >= 0 holds
    let result = count_from.call(&mut store, (0, 5)).expect("call failed");
    assert_eq!(result, 5);

    // Invalid: start=-5, invariant count >= 0 violated at loop entry
    let result = count_from.call(&mut store, (-5, 5));
    assert!(result.is_err(), "Should trap when invariant is violated");
}

// ============================================================================
// New Type System Tests (v0.7.5)
// ============================================================================

#[test]
fn test_execute_u8_addition() {
    let source = r#"
# Unsigned 8-bit addition (maps to i32 in WASM)
@node sum_u8
@params a:u8 b:u8
@returns u8

  add %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    // u8 is represented as i32 in WASM
    let sum_u8 = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "sum_u8")
        .expect("sum_u8 function not found");

    // Test: 100 + 50 = 150
    let result = sum_u8.call(&mut store, (100, 50)).expect("call failed");
    assert_eq!(result, 150);

    // Test: 0 + 0 = 0
    let result = sum_u8.call(&mut store, (0, 0)).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_i16_subtraction() {
    let source = r#"
# Signed 16-bit subtraction (maps to i32 in WASM)
@node diff_i16
@params a:i16 b:i16
@returns i16

  sub %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    // i16 is represented as i32 in WASM
    let diff_i16 = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "diff_i16")
        .expect("diff_i16 function not found");

    // Test: 1000 - 500 = 500
    let result = diff_i16.call(&mut store, (1000, 500)).expect("call failed");
    assert_eq!(result, 500);

    // Test: -100 - 100 = -200
    let result = diff_i16.call(&mut store, (-100, 100)).expect("call failed");
    assert_eq!(result, -200);
}

#[test]
fn test_execute_u32_multiplication() {
    let source = r#"
# Unsigned 32-bit multiplication
@node product_u32
@params a:u32 b:u32
@returns u32

  mul %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    // u32 is represented as i32 in WASM
    let product_u32 = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "product_u32")
        .expect("product_u32 function not found");

    // Test: 100 * 50 = 5000
    let result = product_u32.call(&mut store, (100, 50)).expect("call failed");
    assert_eq!(result, 5000);

    // Test: 0 * 999 = 0
    let result = product_u32.call(&mut store, (0, 999)).expect("call failed");
    assert_eq!(result, 0);
}

#[test]
fn test_execute_u64_operations() {
    let source = r#"
# Unsigned 64-bit addition
@node sum_u64
@params a:u64 b:u64
@returns u64

  add %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    // u64 is represented as i64 in WASM
    let sum_u64 = instance
        .get_typed_func::<(i64, i64), i64>(&mut store, "sum_u64")
        .expect("sum_u64 function not found");

    // Test: 10000000000 + 20000000000 = 30000000000
    let result = sum_u64
        .call(&mut store, (10_000_000_000i64, 20_000_000_000i64))
        .expect("call failed");
    assert_eq!(result, 30_000_000_000i64);
}

#[test]
fn test_execute_char_identity() {
    let source = r#"
# Char identity function (char is UTF-32 codepoint, stored as i32)
@node char_id
@params c:char
@returns char

  mov %r c
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    // char is represented as i32 in WASM (UTF-32 codepoint)
    let char_id = instance
        .get_typed_func::<i32, i32>(&mut store, "char_id")
        .expect("char_id function not found");

    // Test: 'A' (65) -> 'A' (65)
    let result = char_id.call(&mut store, 65).expect("call failed");
    assert_eq!(result, 65);

    // Test: '한' (U+D55C = 54620) -> '한' (54620)
    let result = char_id.call(&mut store, 54620).expect("call failed");
    assert_eq!(result, 54620);
}

#[test]
fn test_execute_i8_arithmetic() {
    // Test i8 addition operation (same-type operands)
    let source = r#"
# i8 addition
@node calc_i8
@params a:i8 b:i8
@returns i8

  add %r a b
  ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    // i8 is represented as i32 in WASM
    let calc_i8 = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "calc_i8")
        .expect("calc_i8 function not found");

    // Test: 50 + 30 = 80
    let result = calc_i8.call(&mut store, (50, 30)).expect("call failed");
    assert_eq!(result, 80);

    // Test: 10 + 5 = 15
    let result = calc_i8.call(&mut store, (10, 5)).expect("call failed");
    assert_eq!(result, 15);
}

#[test]
fn test_extern_parsing() {
    // Test @extern FFI declaration parsing (v0.12+)
    // Extern functions with various calling conventions
    let source = r#"
# External C function declaration
@extern "C" from "libc"
@node puts
@params s:*i8
@returns i32
@pre s != 0

# External function without source module
@extern "C"
@node exit
@params code:i32
@returns void

# System calling convention
@extern "system"
@node syscall
@params num:i64 a:i64 b:i64
@returns i64

# Main function that doesn't call externs (just parsing test)
@node main
@params
@returns i32
  mov %result 0
  ret %result
"#;

    // Parse and typecheck (don't generate code since externs aren't linked)
    let ast = parser::parse(source).expect("parsing failed");

    // Verify extern functions are parsed correctly
    assert_eq!(ast.extern_defs.len(), 3);

    // Check first extern (puts)
    let puts = &ast.extern_defs[0];
    assert_eq!(puts.name.name, "puts");
    assert_eq!(puts.source_module, Some("libc".to_string()));
    assert_eq!(puts.params.len(), 1);
    assert_eq!(puts.preconditions.len(), 1);

    // Check second extern (exit)
    let exit = &ast.extern_defs[1];
    assert_eq!(exit.name.name, "exit");
    assert_eq!(exit.source_module, None);
    assert_eq!(exit.params.len(), 1);

    // Check third extern (syscall)
    let syscall = &ast.extern_defs[2];
    assert_eq!(syscall.name.name, "syscall");
    assert_eq!(syscall.params.len(), 3);

    // Typecheck should succeed
    let typed = types::typecheck(&ast).expect("type checking failed");
    assert_eq!(typed.extern_defs.len(), 3);
}

#[test]
fn test_extern_wasm_import_module_names() {
    // Test that @extern declarations generate proper WASM imports with module names (v0.12+)
    // WASM uses two-level namespace: (import "module" "function" ...)
    let source = r#"
# External C function with explicit source module
@extern "C" from "custom_lib"
@node my_print
@params value:i32
@returns void

# External function without module (defaults to "env")
@extern "C"
@node default_func
@params x:i32
@returns i32

# Main function (required for valid program)
@node main
@params
@returns i32
  mov %result 0
  ret %result
"#;

    // Compile to WASM
    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    let wasm = codegen::generate(&verified).expect("code generation failed");

    // Create wasmtime module and inspect imports
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");

    // Collect imports for verification
    let imports: Vec<_> = module.imports().collect();

    // Should have 2 imports from extern definitions
    assert!(imports.len() >= 2, "Expected at least 2 imports, got {}", imports.len());

    // Find the custom_lib::my_print import
    let custom_import = imports.iter()
        .find(|i| i.module() == "custom_lib" && i.name() == "my_print");
    assert!(custom_import.is_some(), "Expected import from 'custom_lib' module with name 'my_print'");

    // Find the env::default_func import (default module name)
    let env_import = imports.iter()
        .find(|i| i.module() == "env" && i.name() == "default_func");
    assert!(env_import.is_some(), "Expected import from 'env' module with name 'default_func'");
}

#[test]
fn test_xcall_to_extern_function() {
    // Test that xcall can call extern functions (v0.12+)
    // The generated WASM should have a call instruction to the imported function
    let source = r#"
# External logging function
@extern "C" from "logger"
@node log_value
@params value:i32
@returns void

# Main function that calls the extern
@node main
@params
@returns i32
  mov %x 42
  xcall log_value %x
  mov %result 0
  ret %result
"#;

    // Compile to WASM
    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    let wasm = codegen::generate(&verified).expect("code generation failed");

    // Create wasmtime module and verify it's valid
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");

    // Verify the logger import exists
    let imports: Vec<_> = module.imports().collect();
    let logger_import = imports.iter()
        .find(|i| i.module() == "logger" && i.name() == "log_value");
    assert!(logger_import.is_some(), "Expected import from 'logger' module with name 'log_value'");

    // Verify main function is exported
    let exports: Vec<_> = module.exports().collect();
    let main_export = exports.iter().find(|e| e.name() == "main");
    assert!(main_export.is_some(), "Expected export 'main'");
}

#[test]
fn test_pub_visibility_annotation() {
    // v0.12+: @pub marks functions for export
    // Non-@pub functions should NOT be exported when @pub exists
    let source = r#"
# Public function - should be exported
@pub
@node public_add
@params a:i32 b:i32
@returns i32
  add %r a b
  ret %r

# Private function - should NOT be exported
@node private_helper
@params x:i32
@returns i32
  mul %r x 2
  ret %r
"#;

    // Compile to WASM
    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    let wasm = codegen::generate(&verified).expect("code generation failed");

    // Create wasmtime module
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");

    // Verify exports
    let exports: Vec<_> = module.exports().collect();
    let export_names: Vec<&str> = exports.iter().map(|e| e.name()).collect();

    // public_add should be exported
    assert!(export_names.contains(&"public_add"), "Expected @pub function 'public_add' to be exported");
    
    // private_helper should NOT be exported (because we have @pub functions)
    assert!(!export_names.contains(&"private_helper"), 
            "Non-@pub function 'private_helper' should NOT be exported when @pub exists");
}

#[test]
fn test_pub_visibility_backwards_compatibility() {
    // v0.12+: If NO @pub exists, all functions are exported (backwards compatibility)
    let source = r#"
# Legacy code without @pub - all should be exported
@node func_a
@params x:i32
@returns i32
  ret x

@node func_b
@params y:i32
@returns i32
  mul %r y 2
  ret %r
"#;

    // Compile to WASM
    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    let wasm = codegen::generate(&verified).expect("code generation failed");

    // Create wasmtime module
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");

    // Verify exports - both should be exported (backwards compatibility)
    let exports: Vec<_> = module.exports().collect();
    let export_names: Vec<&str> = exports.iter().map(|e| e.name()).collect();

    assert!(export_names.contains(&"func_a"), "Legacy function 'func_a' should be exported");
    assert!(export_names.contains(&"func_b"), "Legacy function 'func_b' should be exported");
}

// =============================================================================
// Pattern Matching Tests (@match) - v0.13+
// =============================================================================

#[test]
fn test_match_literal_patterns() {
    // Test @match with literal integer patterns
    let source = r#"
# Pattern matching with literal patterns
@node classify
@params x:i32
@returns i32

  @match %x
    @case 0:
      ret 100
    @case 1:
      ret 200
    @case 42:
      ret 999
    @default:
      ret 0
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let classify = instance
        .get_typed_func::<i32, i32>(&mut store, "classify")
        .expect("classify function not found");

    // Test pattern matches
    assert_eq!(classify.call(&mut store, 0).unwrap(), 100);
    assert_eq!(classify.call(&mut store, 1).unwrap(), 200);
    assert_eq!(classify.call(&mut store, 42).unwrap(), 999);

    // Test default case
    assert_eq!(classify.call(&mut store, 2).unwrap(), 0);
    assert_eq!(classify.call(&mut store, 100).unwrap(), 0);
    assert_eq!(classify.call(&mut store, -1).unwrap(), 0);
}

#[test]
fn test_match_bool_patterns() {
    // Test @match with boolean literal patterns
    let source = r#"
# Pattern matching with boolean patterns
@node bool_to_int
@params b:bool
@returns i32

  @match %b
    @case true:
      ret 1
    @case false:
      ret 0
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let bool_to_int = instance
        .get_typed_func::<i32, i32>(&mut store, "bool_to_int")
        .expect("bool_to_int function not found");

    // In WASM, bool is i32 (0 = false, non-zero = true)
    assert_eq!(bool_to_int.call(&mut store, 1).unwrap(), 1);  // true
    assert_eq!(bool_to_int.call(&mut store, 0).unwrap(), 0);  // false
}

#[test]
fn test_match_with_computation() {
    // Test @match arms that do computation before returning
    let source = r#"
# Pattern matching with computation in arms
@node double_if_small
@params x:i32
@returns i32

  @match %x
    @case 0:
      ret 0
    @case 1:
      mov %r 2
      ret %r
    @case 2:
      mov %r 4
      ret %r
    @default:
      mul %r %x 2
      ret %r
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let double_if_small = instance
        .get_typed_func::<i32, i32>(&mut store, "double_if_small")
        .expect("double_if_small function not found");

    assert_eq!(double_if_small.call(&mut store, 0).unwrap(), 0);
    assert_eq!(double_if_small.call(&mut store, 1).unwrap(), 2);
    assert_eq!(double_if_small.call(&mut store, 2).unwrap(), 4);
    assert_eq!(double_if_small.call(&mut store, 10).unwrap(), 20);
    assert_eq!(double_if_small.call(&mut store, 50).unwrap(), 100);
}

#[test]
fn test_match_enum_variants() {
    // Test @match with enum variant patterns
    let source = r#"
# Simple enum for testing
@enum Color
  Red
  Green
  Blue

# Pattern matching with enum variants
@node color_value
@params c:Color
@returns i32

  @match %c
    @case Color::Red:
      ret 1
    @case Color::Green:
      ret 2
    @case Color::Blue:
      ret 3
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let color_value = instance
        .get_typed_func::<i32, i32>(&mut store, "color_value")
        .expect("color_value function not found");

    // Enum variants are represented as i32 discriminants (0, 1, 2)
    assert_eq!(color_value.call(&mut store, 0).unwrap(), 1);  // Red
    assert_eq!(color_value.call(&mut store, 1).unwrap(), 2);  // Green
    assert_eq!(color_value.call(&mut store, 2).unwrap(), 3);  // Blue
}

// =============================================================================
// Box<T> Heap Allocation Tests (v0.13+)
// =============================================================================

#[test]
fn test_box_simple_i32() {
    // Test basic box/unbox cycle with i32
    let source = r#"
@node box_test
@params value:i32
@returns i32

  box %boxed %value
  unbox %result %boxed
  ret %result
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let box_test = instance
        .get_typed_func::<i32, i32>(&mut store, "box_test")
        .expect("box_test function not found");

    // Test with various values
    assert_eq!(box_test.call(&mut store, 42).unwrap(), 42);
    assert_eq!(box_test.call(&mut store, -100).unwrap(), -100);
    assert_eq!(box_test.call(&mut store, 0).unwrap(), 0);
    assert_eq!(box_test.call(&mut store, i32::MAX).unwrap(), i32::MAX);
    assert_eq!(box_test.call(&mut store, i32::MIN).unwrap(), i32::MIN);
}

#[test]
fn test_box_multiple_allocations() {
    // Test multiple box allocations to verify heap pointer advances correctly
    let source = r#"
@node multi_box
@params a:i32 b:i32
@returns i32

  box %box_a %a
  box %box_b %b
  unbox %val_a %box_a
  unbox %val_b %box_b
  add %result %val_a %val_b
  ret %result
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let multi_box = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "multi_box")
        .expect("multi_box function not found");

    // Test that both values are preserved correctly
    assert_eq!(multi_box.call(&mut store, (10, 20)).unwrap(), 30);
    assert_eq!(multi_box.call(&mut store, (100, -50)).unwrap(), 50);
}

#[test]
fn test_box_with_drop() {
    // Test that drop opcode doesn't break anything (no-op with bump allocator)
    let source = r#"
@node box_drop_test
@params value:i32
@returns i32

  box %boxed %value
  unbox %result %boxed
  drop %boxed
  ret %result
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let box_drop_test = instance
        .get_typed_func::<i32, i32>(&mut store, "box_drop_test")
        .expect("box_drop_test function not found");

    // Value should still be retrievable (drop is no-op with bump allocator)
    assert_eq!(box_drop_test.call(&mut store, 42).unwrap(), 42);
}

#[test]
fn test_box_returns_pointer() {
    // Test that box returns a valid heap pointer (should be >= 1024)
    let source = r#"
@node box_ptr
@params value:i32
@returns Box<i32>

  box %boxed %value
  ret %boxed
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let box_ptr = instance
        .get_typed_func::<i32, i32>(&mut store, "box_ptr")
        .expect("box_ptr function not found");

    // Box pointer should be at heap start (1024)
    let ptr = box_ptr.call(&mut store, 42).unwrap();
    assert!(ptr >= 1024, "Box pointer should be >= 1024, got {}", ptr);
}

// =============================================================================
// Load/Store Memory Operation Tests (v0.15.1+)
// Philosophy: "Omission is guessing" - explicit memory access with clear semantics
// =============================================================================

#[test]
fn test_load_store_basic_i32() {
    // Test basic load/store cycle: box -> store -> load
    // Note: Function name avoids reserved word prefix (load_, store_)
    let source = r#"
@node mem_rw_test
@params value:i32
@returns i32

  # Allocate memory on heap
  box %ptr %value

  # Store a different value (double the input)
  add %doubled %value %value
  store %ptr %doubled

  # Load it back
  load %result %ptr

  ret %result
"#;

    let wasm = compile_bmb(source);
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let mem_rw_test = instance
        .get_typed_func::<i32, i32>(&mut store, "mem_rw_test")
        .expect("mem_rw_test function not found");

    // Should return doubled value
    assert_eq!(mem_rw_test.call(&mut store, 21).unwrap(), 42);
    assert_eq!(mem_rw_test.call(&mut store, 50).unwrap(), 100);
    assert_eq!(mem_rw_test.call(&mut store, -10).unwrap(), -20);
}

#[test]
fn test_load_store_multiple_locations() {
    // Test store/load with multiple memory locations
    let source = r#"
@node multi_mem
@params a:i32 b:i32
@returns i32

  # Allocate two memory locations
  box %ptrA %a
  box %ptrB %b

  # Swap values via load/store
  load %valA %ptrA
  load %valB %ptrB
  store %ptrA %valB
  store %ptrB %valA

  # Return sum of swapped values (should equal original sum)
  load %resA %ptrA
  load %resB %ptrB
  add %sum %resA %resB

  ret %sum
"#;

    let wasm = compile_bmb(source);
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let multi_mem = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "multi_mem")
        .expect("multi_mem function not found");

    // Sum should be preserved after swap
    assert_eq!(multi_mem.call(&mut store, (10, 20)).unwrap(), 30);
    assert_eq!(multi_mem.call(&mut store, (100, 200)).unwrap(), 300);
}

#[test]
fn test_load_after_box() {
    // Test that load can read the value stored by box
    let source = r#"
@node read_boxed_value
@params value:i32
@returns i32

  # Box stores value at ptr
  box %ptr %value

  # Load should read the same value
  load %result %ptr

  ret %result
"#;

    let wasm = compile_bmb(source);
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let read_boxed_value = instance
        .get_typed_func::<i32, i32>(&mut store, "read_boxed_value")
        .expect("read_boxed_value function not found");

    assert_eq!(read_boxed_value.call(&mut store, 42).unwrap(), 42);
    assert_eq!(read_boxed_value.call(&mut store, -999).unwrap(), -999);
    assert_eq!(read_boxed_value.call(&mut store, 0).unwrap(), 0);
}

#[test]
fn test_store_overwrites_box_value() {
    // Verify that store properly overwrites the initial box value
    let source = r#"
@node overwrite_test
@params initial:i32 new_value:i32
@returns i32

  # Box the initial value
  box %ptr %initial

  # Overwrite with new value
  store %ptr %new_value

  # Load should return new value, not initial
  load %result %ptr

  ret %result
"#;

    let wasm = compile_bmb(source);
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let overwrite_test = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "overwrite_test")
        .expect("overwrite_test function not found");

    // Should return new_value, not initial
    assert_eq!(overwrite_test.call(&mut store, (100, 200)).unwrap(), 200);
    assert_eq!(overwrite_test.call(&mut store, (0, 42)).unwrap(), 42);
    assert_eq!(overwrite_test.call(&mut store, (999, -1)).unwrap(), -1);
}

// =============================================================================
// Exhaustiveness Checking Tests (v0.15+)
// "Omission is guessing, and guessing is error."
// =============================================================================

#[test]
fn test_exhaustiveness_enum_missing_variant() {
    // Test that missing enum variant causes compile error
    let source = r#"
@enum Status
  Ok
  Err
  Pending

@node process
@params s:Status
@returns i32

  @match %s
    @case Status::Ok:
      ret 1
    @case Status::Err:
      ret 0
"#;

    let ast = parser::parse(source).expect("parsing failed");
    let result = types::typecheck(&ast);

    assert!(result.is_err(), "Should fail: missing Status::Pending variant");
    let err = result.unwrap_err();
    let err_msg = format!("{}", err);
    assert!(
        err_msg.contains("Non-exhaustive") || err_msg.contains("Missing pattern"),
        "Error should mention non-exhaustive: {}",
        err_msg
    );
    assert!(
        err_msg.contains("Pending"),
        "Error should mention missing 'Pending' variant: {}",
        err_msg
    );
}

#[test]
fn test_exhaustiveness_bool_missing_false() {
    // Test that missing 'false' pattern causes compile error
    let source = r#"
@node only_true
@params b:bool
@returns i32

  @match %b
    @case true:
      ret 1
"#;

    let ast = parser::parse(source).expect("parsing failed");
    let result = types::typecheck(&ast);

    assert!(result.is_err(), "Should fail: missing 'false' pattern");
    let err = result.unwrap_err();
    let err_msg = format!("{}", err);
    assert!(
        err_msg.contains("Non-exhaustive") || err_msg.contains("Missing pattern"),
        "Error should mention non-exhaustive: {}",
        err_msg
    );
    assert!(
        err_msg.contains("false"),
        "Error should mention missing 'false': {}",
        err_msg
    );
}

#[test]
fn test_exhaustiveness_integer_requires_default() {
    // Test that integer match without @default causes compile error
    let source = r#"
@node classify
@params x:i32
@returns i32

  @match %x
    @case 0:
      ret 100
    @case 1:
      ret 200
"#;

    let ast = parser::parse(source).expect("parsing failed");
    let result = types::typecheck(&ast);

    assert!(result.is_err(), "Should fail: integer domain requires @default");
    let err = result.unwrap_err();
    let err_msg = format!("{}", err);
    assert!(
        err_msg.contains("Non-exhaustive") || err_msg.contains("Missing pattern"),
        "Error should mention non-exhaustive: {}",
        err_msg
    );
    assert!(
        err_msg.contains("@default"),
        "Error should mention missing '@default': {}",
        err_msg
    );
}

#[test]
fn test_exhaustiveness_enum_with_default_is_ok() {
    // Test that partial enum coverage with @default compiles
    let source = r#"
@enum Status
  Ok
  Err
  Pending

@node process
@params s:Status
@returns i32

  @match %s
    @case Status::Ok:
      ret 1
    @default:
      ret 0
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let process = instance
        .get_typed_func::<i32, i32>(&mut store, "process")
        .expect("process function not found");

    assert_eq!(process.call(&mut store, 0).unwrap(), 1);  // Ok
    assert_eq!(process.call(&mut store, 1).unwrap(), 0);  // Err -> default
    assert_eq!(process.call(&mut store, 2).unwrap(), 0);  // Pending -> default
}

#[test]
fn test_exhaustiveness_all_enum_variants_no_default() {
    // Test that covering all variants without @default compiles
    let source = r#"
@enum Direction
  North
  South
  East
  West

@node direction_code
@params d:Direction
@returns i32

  @match %d
    @case Direction::North:
      ret 0
    @case Direction::South:
      ret 1
    @case Direction::East:
      ret 2
    @case Direction::West:
      ret 3
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let direction_code = instance
        .get_typed_func::<i32, i32>(&mut store, "direction_code")
        .expect("direction_code function not found");

    assert_eq!(direction_code.call(&mut store, 0).unwrap(), 0);  // North
    assert_eq!(direction_code.call(&mut store, 1).unwrap(), 1);  // South
    assert_eq!(direction_code.call(&mut store, 2).unwrap(), 2);  // East
    assert_eq!(direction_code.call(&mut store, 3).unwrap(), 3);  // West
}

// =============================================================================
// Module & FFI Execution Tests (v0.15.2)
// =============================================================================

#[test]
fn test_xcall_executes_host_function() {
    // v0.15.2: Verify xcall actually invokes the host function at runtime
    // This test uses wasmtime's Linker to provide host functions
    use std::sync::{Arc, Mutex};

    let source = r#"
# External function declaration
@extern "C" from "test_host"
@node accumulate
@params value:i32
@returns void

# Main function that calls the extern
@node main
@params x:i32
@returns i32
  xcall accumulate %x
  xcall accumulate %x
  xcall accumulate %x
  ret %x
"#;

    // Compile to WASM
    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    let wasm = codegen::generate(&verified).expect("code generation failed");

    // Create engine and store with shared state
    let engine = Engine::default();
    let call_count = Arc::new(Mutex::new(0i32));
    let accumulated = Arc::new(Mutex::new(0i32));

    // Clone for closure
    let call_count_clone = call_count.clone();
    let accumulated_clone = accumulated.clone();

    // Create linker and register host function
    let mut linker = Linker::new(&engine);
    linker
        .func_wrap("test_host", "accumulate", move |value: i32| {
            *call_count_clone.lock().unwrap() += 1;
            *accumulated_clone.lock().unwrap() += value;
        })
        .expect("failed to register host function");

    // Create module and instantiate with linked functions
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &module).expect("instantiation failed");

    // Call main with value 10
    let main = instance
        .get_typed_func::<i32, i32>(&mut store, "main")
        .expect("main function not found");

    let result = main.call(&mut store, 10).expect("call failed");

    // Verify host function was called 3 times
    assert_eq!(*call_count.lock().unwrap(), 3, "xcall should invoke host function 3 times");

    // Verify accumulated value (10 + 10 + 10 = 30)
    assert_eq!(*accumulated.lock().unwrap(), 30, "accumulated value should be 30");

    // Return value should be the input unchanged
    assert_eq!(result, 10);
}

#[test]
fn test_xcall_with_multiple_extern_functions() {
    // v0.15.2: Test multiple extern functions from different modules
    use std::sync::{Arc, Mutex};

    let source = r#"
# Logger from logger module
@extern "C" from "logger"
@node log_info
@params code:i32
@returns void

# Metrics from metrics module
@extern "C" from "metrics"
@node record_metric
@params value:i32
@returns void

@node process
@params input:i32
@returns i32
  xcall log_info 100
  mul %doubled input 2
  xcall record_metric %doubled
  xcall log_info 200
  ret %doubled
"#;

    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    let wasm = codegen::generate(&verified).expect("code generation failed");

    let engine = Engine::default();
    let log_calls = Arc::new(Mutex::new(Vec::<i32>::new()));
    let metric_calls = Arc::new(Mutex::new(Vec::<i32>::new()));

    let log_calls_clone = log_calls.clone();
    let metric_calls_clone = metric_calls.clone();

    let mut linker = Linker::new(&engine);
    linker
        .func_wrap("logger", "log_info", move |code: i32| {
            log_calls_clone.lock().unwrap().push(code);
        })
        .expect("failed to register log_info");

    linker
        .func_wrap("metrics", "record_metric", move |value: i32| {
            metric_calls_clone.lock().unwrap().push(value);
        })
        .expect("failed to register record_metric");

    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &module).expect("instantiation failed");

    let process = instance
        .get_typed_func::<i32, i32>(&mut store, "process")
        .expect("process function not found");

    let result = process.call(&mut store, 5).expect("call failed");

    // Verify log calls: 100, 200
    assert_eq!(*log_calls.lock().unwrap(), vec![100, 200], "log_info should be called with 100 then 200");

    // Verify metric call: 10 (5 * 2)
    assert_eq!(*metric_calls.lock().unwrap(), vec![10], "record_metric should be called with 10");

    // Return value should be doubled
    assert_eq!(result, 10);
}

#[test]
fn test_call_with_extern_function_returning_value() {
    // v0.15.2: Test extern function that returns a value (using call, not xcall)
    // call is for functions that return values, xcall is for void functions

    let source = r#"
# External function that returns a value
@extern "C" from "math_host"
@node double_it
@params x:i32
@returns i32

@node compute
@params input:i32
@returns i32
  call %result double_it input
  add %final %result 1
  ret %final
"#;

    let ast = parser::parse(source).expect("parsing failed");
    let typed = types::typecheck(&ast).expect("type checking failed");
    let verified = contracts::verify(&typed).expect("contract verification failed");
    let wasm = codegen::generate(&verified).expect("code generation failed");

    let engine = Engine::default();

    let mut linker = Linker::new(&engine);
    linker
        .func_wrap("math_host", "double_it", |x: i32| -> i32 {
            x * 2
        })
        .expect("failed to register double_it");

    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &module).expect("instantiation failed");

    let compute = instance
        .get_typed_func::<i32, i32>(&mut store, "compute")
        .expect("compute function not found");

    // compute(5) = double_it(5) + 1 = 10 + 1 = 11
    let result = compute.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 11);

    // compute(10) = double_it(10) + 1 = 20 + 1 = 21
    let result = compute.call(&mut store, 10).expect("call failed");
    assert_eq!(result, 21);
}

#[test]
fn test_qualified_call_in_single_file() {
    // v0.15.2: Test that qualified call syntax parses correctly
    // This registers both the caller and target in the same file

    // Note: In single-file compilation, qualified calls require
    // the target function to be registered with that qualified name.
    // For now, we test the internal call path (same file).

    let source = r#"
# Helper function
@node helper
@params x:i32
@returns i32
  mul %r x 2
  ret %r

# Main function that calls helper (unqualified, same file)
@node main_caller
@params input:i32
@returns i32
  call %result helper input
  add %final %result 100
  ret %final
"#;

    let wasm = compile_bmb(source);

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm).expect("module creation failed");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiation failed");

    let main_caller = instance
        .get_typed_func::<i32, i32>(&mut store, "main_caller")
        .expect("main_caller function not found");

    // main_caller(5) = helper(5) + 100 = 10 + 100 = 110
    let result = main_caller.call(&mut store, 5).expect("call failed");
    assert_eq!(result, 110);
}

#[test]
fn test_modules_merged_program_qualified_lookup() {
    // v0.15.2: Test MergedProgram qualified node lookup
    use bmb::modules::{MergedProgram, ResolvedModule};
    use std::path::PathBuf;
    use bmb::ast::{Type, Program, Node, Identifier, Span, Parameter, ParamAnnotation};

    // Create main program
    let main = Program {
        module: None,
        imports: vec![],
        uses: vec![],
        extern_defs: vec![],
        type_defs: vec![],
        structs: vec![],
        enums: vec![],
        contracts: vec![],
        device_defs: vec![],
        nodes: vec![Node {
            is_public: false,
            name: Identifier::new("main", Span::default()),
            tags: vec![],
            params: vec![],
            returns: Type::I32,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body: vec![],
            span: Span::default(),
        }],
    };

    // Create math module with add function
    let math_module = ResolvedModule {
        path: PathBuf::from("math.bmb"),
        program: Program {
            module: None,
            imports: vec![],
            uses: vec![],
            extern_defs: vec![],
            type_defs: vec![],
            structs: vec![],
            enums: vec![],
            contracts: vec![],
            device_defs: vec![],
            nodes: vec![Node {
                is_public: false,
                name: Identifier::new("adder", Span::default()),
                tags: vec![],
                params: vec![
                    Parameter {
                        name: Identifier::new("a", Span::default()),
                        ty: Type::I32,
                        annotation: ParamAnnotation::None,
                        span: Span::default(),
                    },
                    Parameter {
                        name: Identifier::new("b", Span::default()),
                        ty: Type::I32,
                        annotation: ParamAnnotation::None,
                        span: Span::default(),
                    },
                ],
                returns: Type::I32,
                preconditions: vec![],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: Span::default(),
            }],
        },
        alias: None,
    };

    let mut modules = std::collections::HashMap::new();
    modules.insert("math".to_string(), math_module);

    let merged = MergedProgram::new(main, modules);

    // Test qualified lookup
    assert!(merged.get_node("main").is_some(), "main node should be found");
    assert!(merged.get_node("math::adder").is_some(), "math::adder should be found");
    assert!(merged.get_qualified_node("math", "adder").is_some(), "qualified lookup should work");

    // Test that wrong lookups return None
    assert!(merged.get_node("nonexistent").is_none());
    assert!(merged.get_node("other::adder").is_none());
}
