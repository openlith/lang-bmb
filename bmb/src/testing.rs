//! BMB Test Execution Engine
//!
//! Executes @test declarations and reports results.
//!
//! ## Test Syntax
//!
//! @test declarations come AFTER contracts (@pre, @post) but BEFORE the body.
//!
//! ```bmb
//! @node factorial
//! @params n:i32
//! @returns i32
//! @pre n >= 0
//! @test expect(factorial(5), 120)
//! @test expect(factorial(0), 1)
//!
//!   eq %base n 0
//!   jif %base _one
//!   ; ... implementation ...
//! ```

use crate::ast::{Program, TestArg, TestCase};
use crate::codegen::generate as codegen_generate;
use crate::contracts::verify;
use crate::optimize::{optimize, OptLevel};
use crate::parser::parse;
use crate::types::typecheck;

/// Test result for a single test case
#[derive(Debug, Clone)]
pub struct TestResult {
    /// Node name containing the test
    pub node_name: String,
    /// Test case index within the node
    pub test_index: usize,
    /// Test function (e.g., "expect")
    pub function: String,
    /// Whether the test passed
    pub passed: bool,
    /// Expected value (if applicable)
    pub expected: Option<TestValue>,
    /// Actual value (if applicable)
    pub actual: Option<TestValue>,
    /// Error message if failed
    pub error: Option<String>,
}

/// Value types for test comparison
#[derive(Debug, Clone, PartialEq)]
pub enum TestValue {
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl std::fmt::Display for TestValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestValue::Int(v) => write!(f, "{}", v),
            TestValue::Float(v) => write!(f, "{}", v),
            TestValue::Bool(v) => write!(f, "{}", v),
        }
    }
}

/// Test suite containing all test results
#[derive(Debug, Default)]
pub struct TestSuite {
    pub results: Vec<TestResult>,
    pub passed: usize,
    pub failed: usize,
    pub total: usize,
}

impl TestSuite {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_result(&mut self, result: TestResult) {
        if result.passed {
            self.passed += 1;
        } else {
            self.failed += 1;
        }
        self.total += 1;
        self.results.push(result);
    }

    pub fn all_passed(&self) -> bool {
        self.failed == 0
    }

    /// Print test results to stdout
    pub fn print_results(&self) {
        for result in &self.results {
            let status = if result.passed { "✓" } else { "✗" };
            let color = if result.passed { "\x1b[32m" } else { "\x1b[31m" };
            let reset = "\x1b[0m";

            print!(
                "{}{}{} {}::test_{} - {}",
                color, status, reset, result.node_name, result.test_index, result.function
            );

            if !result.passed {
                if let (Some(expected), Some(actual)) = (&result.expected, &result.actual) {
                    println!(" (expected: {}, got: {})", expected, actual);
                } else if let Some(err) = &result.error {
                    println!(" ({})", err);
                } else {
                    println!();
                }
            } else {
                println!();
            }
        }

        println!();
        println!(
            "Tests: {} passed, {} failed, {} total",
            self.passed, self.failed, self.total
        );
    }
}

/// Test runner for BMB programs
pub struct TestRunner {
    /// Collected test cases with their node context
    tests: Vec<CollectedTest>,
}

/// A test case with its containing node context
#[derive(Debug, Clone)]
struct CollectedTest {
    node_name: String,
    test_index: usize,
    test_case: TestCase,
}

impl TestRunner {
    /// Create a new test runner from a program
    pub fn new(program: &Program) -> Self {
        let mut tests = Vec::new();

        for node in &program.nodes {
            for (index, test) in node.tests.iter().enumerate() {
                tests.push(CollectedTest {
                    node_name: node.name.name.clone(),
                    test_index: index,
                    test_case: test.clone(),
                });
            }
        }

        Self { tests }
    }

    /// Get the number of tests
    pub fn test_count(&self) -> usize {
        self.tests.len()
    }

    /// Run all tests using the WASM runtime
    pub fn run_with_wasm(&self, wasm_bytes: &[u8]) -> Result<TestSuite, String> {
        use wasmtime::*;

        let engine = Engine::default();
        let module = Module::new(&engine, wasm_bytes)
            .map_err(|e| format!("Failed to create WASM module: {}", e))?;

        let mut store = Store::new(&engine, ());
        let instance = Instance::new(&mut store, &module, &[])
            .map_err(|e| format!("Failed to instantiate WASM module: {}", e))?;

        let mut suite = TestSuite::new();

        for test in &self.tests {
            let result = self.run_single_test(&mut store, &instance, test);
            suite.add_result(result);
        }

        Ok(suite)
    }

    /// Run a single test case
    fn run_single_test<T>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        test: &CollectedTest,
    ) -> TestResult {
        let function_name = test.test_case.function.name.as_str();

        match function_name {
            "expect" => self.run_expect_test(store, instance, test),
            "assert" => self.run_assert_test(store, instance, test),
            "assert_eq" => self.run_assert_eq_test(store, instance, test),
            "assert_ne" => self.run_assert_ne_test(store, instance, test),
            _ => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: function_name.to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some(format!("Unknown test function: {}", function_name)),
            },
        }
    }

    /// Run expect(call, expected_value) test
    fn run_expect_test<T>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        test: &CollectedTest,
    ) -> TestResult {
        let args = &test.test_case.args;

        if args.len() != 2 {
            return TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "expect".to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some("expect() requires exactly 2 arguments".to_string()),
            };
        }

        // First arg should be a function call
        let call_result = match &args[0] {
            TestArg::Call { func, args } => {
                self.execute_function_call(store, instance, &func.name, args)
            }
            _ => Err("First argument to expect() must be a function call".to_string()),
        };

        // Second arg is the expected value
        let expected = self.eval_test_arg(&args[1]);

        match (call_result, expected) {
            (Ok(actual), Ok(expected)) => {
                let passed = actual == expected;
                TestResult {
                    node_name: test.node_name.clone(),
                    test_index: test.test_index,
                    function: "expect".to_string(),
                    passed,
                    expected: Some(expected),
                    actual: Some(actual),
                    error: None,
                }
            }
            (Err(e), _) => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "expect".to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some(e),
            },
            (_, Err(e)) => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "expect".to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some(e),
            },
        }
    }

    /// Run assert(condition) test
    fn run_assert_test<T>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        test: &CollectedTest,
    ) -> TestResult {
        let args = &test.test_case.args;

        if args.len() != 1 {
            return TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "assert".to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some("assert() requires exactly 1 argument".to_string()),
            };
        }

        let result = match &args[0] {
            TestArg::Bool(b) => Ok(TestValue::Bool(*b)),
            TestArg::Call { func, args } => {
                self.execute_function_call(store, instance, &func.name, args)
            }
            _ => Err("assert() argument must be a boolean or function call".to_string()),
        };

        match result {
            Ok(TestValue::Bool(true)) => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "assert".to_string(),
                passed: true,
                expected: Some(TestValue::Bool(true)),
                actual: Some(TestValue::Bool(true)),
                error: None,
            },
            Ok(TestValue::Bool(false)) => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "assert".to_string(),
                passed: false,
                expected: Some(TestValue::Bool(true)),
                actual: Some(TestValue::Bool(false)),
                error: None,
            },
            Ok(other) => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "assert".to_string(),
                passed: false,
                expected: Some(TestValue::Bool(true)),
                actual: Some(other),
                error: Some("assert() result is not a boolean".to_string()),
            },
            Err(e) => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: "assert".to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some(e),
            },
        }
    }

    /// Run assert_eq(a, b) test
    fn run_assert_eq_test<T>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        test: &CollectedTest,
    ) -> TestResult {
        self.run_comparison_test(store, instance, test, "assert_eq", |a, b| a == b)
    }

    /// Run assert_ne(a, b) test
    fn run_assert_ne_test<T>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        test: &CollectedTest,
    ) -> TestResult {
        self.run_comparison_test(store, instance, test, "assert_ne", |a, b| a != b)
    }

    /// Generic comparison test
    fn run_comparison_test<T, F>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        test: &CollectedTest,
        func_name: &str,
        compare: F,
    ) -> TestResult
    where
        F: Fn(&TestValue, &TestValue) -> bool,
    {
        let args = &test.test_case.args;

        if args.len() != 2 {
            return TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: func_name.to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some(format!("{}() requires exactly 2 arguments", func_name)),
            };
        }

        let left = self.eval_or_call(store, instance, &args[0]);
        let right = self.eval_or_call(store, instance, &args[1]);

        match (left, right) {
            (Ok(l), Ok(r)) => {
                let passed = compare(&l, &r);
                TestResult {
                    node_name: test.node_name.clone(),
                    test_index: test.test_index,
                    function: func_name.to_string(),
                    passed,
                    expected: Some(r),
                    actual: Some(l),
                    error: None,
                }
            }
            (Err(e), _) | (_, Err(e)) => TestResult {
                node_name: test.node_name.clone(),
                test_index: test.test_index,
                function: func_name.to_string(),
                passed: false,
                expected: None,
                actual: None,
                error: Some(e),
            },
        }
    }

    /// Evaluate a TestArg or execute if it's a function call
    fn eval_or_call<T>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        arg: &TestArg,
    ) -> Result<TestValue, String> {
        match arg {
            TestArg::Call { func, args } => {
                self.execute_function_call(store, instance, &func.name, args)
            }
            _ => self.eval_test_arg(arg),
        }
    }

    /// Evaluate a literal TestArg to a TestValue
    fn eval_test_arg(&self, arg: &TestArg) -> Result<TestValue, String> {
        match arg {
            TestArg::Int(v) => Ok(TestValue::Int(*v)),
            TestArg::Float(v) => Ok(TestValue::Float(*v)),
            TestArg::Bool(v) => Ok(TestValue::Bool(*v)),
            TestArg::Var(id) => Err(format!("Cannot evaluate variable '{}' at test time", id.name)),
            TestArg::Call { .. } => Err("Use execute_function_call for Call args".to_string()),
        }
    }

    /// Execute a WASM function and return its result
    fn execute_function_call<T>(
        &self,
        store: &mut wasmtime::Store<T>,
        instance: &wasmtime::Instance,
        func_name: &str,
        args: &[TestArg],
    ) -> Result<TestValue, String> {
        let func = instance
            .get_func(&mut *store, func_name)
            .ok_or_else(|| format!("Function '{}' not found", func_name))?;

        // Convert args to WASM values
        let mut wasm_args = Vec::new();
        for arg in args {
            let val = self.test_arg_to_wasm_val(arg)?;
            wasm_args.push(val);
        }

        // Prepare result storage
        let mut results = vec![wasmtime::Val::I32(0)];

        // Call the function
        func.call(&mut *store, &wasm_args, &mut results)
            .map_err(|e| format!("Function call failed: {}", e))?;

        // Convert result back
        self.wasm_val_to_test_value(&results[0])
    }

    /// Convert TestArg to WASM Val
    fn test_arg_to_wasm_val(&self, arg: &TestArg) -> Result<wasmtime::Val, String> {
        match arg {
            TestArg::Int(v) => {
                if *v >= i32::MIN as i64 && *v <= i32::MAX as i64 {
                    Ok(wasmtime::Val::I32(*v as i32))
                } else {
                    Ok(wasmtime::Val::I64(*v))
                }
            }
            TestArg::Float(v) => Ok(wasmtime::Val::F64(v.to_bits())),
            TestArg::Bool(v) => Ok(wasmtime::Val::I32(if *v { 1 } else { 0 })),
            TestArg::Var(id) => Err(format!("Cannot use variable '{}' in test", id.name)),
            TestArg::Call { .. } => Err("Nested function calls not supported".to_string()),
        }
    }

    /// Convert WASM Val to TestValue
    fn wasm_val_to_test_value(&self, val: &wasmtime::Val) -> Result<TestValue, String> {
        match val {
            wasmtime::Val::I32(v) => Ok(TestValue::Int(*v as i64)),
            wasmtime::Val::I64(v) => Ok(TestValue::Int(*v)),
            wasmtime::Val::F32(v) => Ok(TestValue::Float(f32::from_bits(*v) as f64)),
            wasmtime::Val::F64(v) => Ok(TestValue::Float(f64::from_bits(*v))),
            _ => Err("Unsupported WASM value type".to_string()),
        }
    }
}

/// Run tests from BMB source code
pub fn run_tests(source: &str) -> Result<TestSuite, String> {
    // Parse
    let program = parse(source).map_err(|e| format!("Parse error: {}", e))?;

    // Check if there are any tests
    let test_count: usize = program.nodes.iter().map(|n| n.tests.len()).sum();
    if test_count == 0 {
        return Ok(TestSuite::new());
    }

    // Type check
    let typed = typecheck(&program).map_err(|e| format!("Type error: {}", e))?;

    // Verify contracts
    let mut verified = verify(&typed).map_err(|e| format!("Contract error: {}", e))?;

    // Optimize
    optimize(&mut verified, OptLevel::Basic);

    // Generate WASM
    let wasm = codegen_generate(&verified).map_err(|e| format!("Codegen error: {}", e))?;

    // Run tests
    let runner = TestRunner::new(&program);
    runner.run_with_wasm(&wasm)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_collect_tests() {
        let source = r#"
@node factorial
@params n:i32
@returns i32
@pre n >= 0
@test expect(factorial(5), 120)
@test expect(factorial(0), 1)

  eq %base n 0
  jif %base _one
  sub %n1 n 1
  call %rec factorial %n1
  mul %result n %rec
  ret %result
_one:
  ret 1
"#;
        let program = parse(source).unwrap();
        let runner = TestRunner::new(&program);
        assert_eq!(runner.test_count(), 2);
    }

    #[test]
    fn test_run_simple_test() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32
@test expect(sum(2, 3), 5)
@test expect(sum(0, 0), 0)

  add %r a b
  ret %r
"#;
        let result = run_tests(source);
        if let Err(ref e) = result {
            eprintln!("Test runner error: {}", e);
        }
        assert!(result.is_ok(), "run_tests failed: {:?}", result);
        let suite = result.unwrap();
        assert_eq!(suite.total, 2);
        assert!(suite.all_passed(), "Some tests failed: {:?}", suite.results);
    }

    #[test]
    fn test_failing_test() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32
@test expect(sum(2, 3), 6)

  add %r a b
  ret %r
"#;
        let result = run_tests(source);
        if let Err(ref e) = result {
            eprintln!("Test runner error: {}", e);
        }
        assert!(result.is_ok(), "run_tests failed: {:?}", result);
        let suite = result.unwrap();
        assert_eq!(suite.total, 1);
        assert!(!suite.all_passed());
        assert_eq!(suite.failed, 1);
    }
}
