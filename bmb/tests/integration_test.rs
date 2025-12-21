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
    let result = divide_f64.call(&mut store, (10.0, 2.0)).expect("call failed");
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
