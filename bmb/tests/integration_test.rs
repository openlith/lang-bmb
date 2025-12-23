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
