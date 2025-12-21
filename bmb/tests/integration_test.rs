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
# i64 multiplication with postcondition
# Note: Literal type inference doesn't yet promote literals to match operand types
# So we use a postcondition that compares i64 values
@node safe_mul64
@params a:i64 b:i64
@returns i64
@pre true
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
}

#[test]
fn test_execute_f32_division() {
    let source = r#"
# f32 division
# Note: Literal type inference doesn't yet promote 0.0 (f64) to f32
@node divide32
@params a:f32 b:f32
@returns f32
@pre true
@post true

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
    let result = divide32
        .call(&mut store, (10.0, 4.0))
        .expect("call failed");
    assert!((result - 2.5).abs() < 1e-5);

    // Test: negative result
    let result = divide32
        .call(&mut store, (-15.0, 3.0))
        .expect("call failed");
    assert!((result - (-5.0)).abs() < 1e-5);
}
