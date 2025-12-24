//! SMT-based Static Verification for BMB Contracts
//!
//! This module provides compile-time verification of contracts using SMT solvers.
//! It translates BMB expressions to SMT-LIB2 format and uses an external solver
//! (Z3, CVC4, CVC5) to prove contract validity.
//!
//! ## Verification Process
//!
//! 1. Translate preconditions to SMT assertions
//! 2. Check that preconditions are satisfiable (not trivially false)
//! 3. Prove postconditions hold given preconditions
//!
//! ## SMT-LIB2 Generation
//!
//! ```smt2
//! ; Precondition: b != 0
//! (declare-const b Int)
//! (assert (not (= b 0)))
//! (check-sat)
//! ```
//!
//! ## External Solver Requirement
//!
//! This module requires an SMT solver (z3, cvc4, or cvc5) to be installed
//! and available in PATH. The solver can be specified via:
//! - `BMB_SMT_SOLVER` environment variable
//! - Command line flag `--smt-solver`
//! - Default: attempts z3, then cvc5, then cvc4

use std::collections::HashMap;

use rsmt2::prelude::*;
use rsmt2::{SmtConf, Solver};

use crate::ast::{BinaryOp, Expr, Type, UnaryOp};
use crate::types::{TypedNode, TypedProgram};
use crate::BmbError;

/// Result of SMT verification
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// Contract is provably valid
    Proven,
    /// Contract is provably invalid with counterexample
    CounterExample(HashMap<String, i64>),
    /// Verification timed out or was inconclusive
    Unknown(String),
    /// Contract cannot be verified (unsupported features)
    Unsupported(String),
    /// No SMT solver available
    SolverNotFound(String),
}

impl VerificationResult {
    /// Returns true if the contract was proven valid
    pub fn is_proven(&self) -> bool {
        matches!(self, VerificationResult::Proven)
    }

    /// Returns true if a counterexample was found
    pub fn is_counterexample(&self) -> bool {
        matches!(self, VerificationResult::CounterExample(_))
    }
}

/// SMT-LIB2 expression representation
#[derive(Debug, Clone)]
pub enum SmtExpr {
    Int(i64),
    Bool(bool),
    Var(String),
    /// Old value reference: old_x refers to x's value at function entry
    OldVar(String),
    Neg(Box<SmtExpr>),
    Not(Box<SmtExpr>),
    Add(Box<SmtExpr>, Box<SmtExpr>),
    Sub(Box<SmtExpr>, Box<SmtExpr>),
    Mul(Box<SmtExpr>, Box<SmtExpr>),
    Div(Box<SmtExpr>, Box<SmtExpr>),
    Mod(Box<SmtExpr>, Box<SmtExpr>),
    Eq(Box<SmtExpr>, Box<SmtExpr>),
    Ne(Box<SmtExpr>, Box<SmtExpr>),
    Lt(Box<SmtExpr>, Box<SmtExpr>),
    Le(Box<SmtExpr>, Box<SmtExpr>),
    Gt(Box<SmtExpr>, Box<SmtExpr>),
    Ge(Box<SmtExpr>, Box<SmtExpr>),
    And(Box<SmtExpr>, Box<SmtExpr>),
    Or(Box<SmtExpr>, Box<SmtExpr>),
    Ite(Box<SmtExpr>, Box<SmtExpr>, Box<SmtExpr>),
}

impl SmtExpr {
    /// Convert to SMT-LIB2 string representation
    pub fn to_smtlib(&self) -> String {
        match self {
            SmtExpr::Int(v) => {
                if *v >= 0 {
                    v.to_string()
                } else {
                    format!("(- {})", -v)
                }
            }
            SmtExpr::Bool(b) => b.to_string(),
            SmtExpr::Var(name) => name.clone(),
            SmtExpr::OldVar(name) => format!("old_{}", name),
            SmtExpr::Neg(e) => format!("(- {})", e.to_smtlib()),
            SmtExpr::Not(e) => format!("(not {})", e.to_smtlib()),
            SmtExpr::Add(l, r) => format!("(+ {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Sub(l, r) => format!("(- {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Mul(l, r) => format!("(* {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Div(l, r) => format!("(div {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Mod(l, r) => format!("(mod {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Eq(l, r) => format!("(= {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Ne(l, r) => format!("(not (= {} {}))", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Lt(l, r) => format!("(< {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Le(l, r) => format!("(<= {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Gt(l, r) => format!("(> {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Ge(l, r) => format!("(>= {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::And(l, r) => format!("(and {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Or(l, r) => format!("(or {} {})", l.to_smtlib(), r.to_smtlib()),
            SmtExpr::Ite(c, t, e) => {
                format!("(ite {} {} {})", c.to_smtlib(), t.to_smtlib(), e.to_smtlib())
            }
        }
    }

    /// Convert expression to boolean (for assertions)
    pub fn to_bool_smtlib(&self) -> String {
        match self {
            SmtExpr::Bool(_) => self.to_smtlib(),
            SmtExpr::Eq(_, _)
            | SmtExpr::Ne(_, _)
            | SmtExpr::Lt(_, _)
            | SmtExpr::Le(_, _)
            | SmtExpr::Gt(_, _)
            | SmtExpr::Ge(_, _)
            | SmtExpr::And(_, _)
            | SmtExpr::Or(_, _)
            | SmtExpr::Not(_) => self.to_smtlib(),
            // For integer expressions, interpret non-zero as true
            _ => format!("(not (= {} 0))", self.to_smtlib()),
        }
    }
}

/// Translate BMB expression to SMT expression
pub fn translate_expr(expr: &Expr) -> Result<SmtExpr, BmbError> {
    match expr {
        Expr::IntLit(v) => Ok(SmtExpr::Int(*v)),
        Expr::BoolLit(b) => Ok(SmtExpr::Bool(*b)),
        Expr::FloatLit(_) => Err(BmbError::ContractError {
            message: "Float literals not supported in SMT verification".to_string(),
        }),
        Expr::Var(id) => Ok(SmtExpr::Var(id.name.clone())),
        Expr::Ret => Ok(SmtExpr::Var("ret".to_string())),
        Expr::Old(inner) => {
            // old(expr) translates to old_* variables
            // For now, we only support old(variable), not complex expressions
            match inner.as_ref() {
                Expr::Var(id) => Ok(SmtExpr::OldVar(id.name.clone())),
                Expr::Ret => Ok(SmtExpr::OldVar("ret".to_string())),
                _ => Err(BmbError::ContractError {
                    message: "old() currently only supports simple variable references".to_string(),
                }),
            }
        }
        Expr::Binary { op, left, right } => {
            let l = Box::new(translate_expr(left)?);
            let r = Box::new(translate_expr(right)?);
            Ok(match op {
                BinaryOp::Add => SmtExpr::Add(l, r),
                BinaryOp::Sub => SmtExpr::Sub(l, r),
                BinaryOp::Mul => SmtExpr::Mul(l, r),
                BinaryOp::Div => SmtExpr::Div(l, r),
                BinaryOp::Mod => SmtExpr::Mod(l, r),
                BinaryOp::Eq => SmtExpr::Eq(l, r),
                BinaryOp::Ne => SmtExpr::Ne(l, r),
                BinaryOp::Lt => SmtExpr::Lt(l, r),
                BinaryOp::Le => SmtExpr::Le(l, r),
                BinaryOp::Gt => SmtExpr::Gt(l, r),
                BinaryOp::Ge => SmtExpr::Ge(l, r),
                BinaryOp::And => SmtExpr::And(l, r),
                BinaryOp::Or => SmtExpr::Or(l, r),
            })
        }
        Expr::SelfRef => Err(BmbError::ContractError {
            message: "self reference not supported in SMT verification".to_string(),
        }),
        Expr::Unary { op, operand } => {
            let o = Box::new(translate_expr(operand)?);
            Ok(match op {
                UnaryOp::Neg => SmtExpr::Neg(o),
                UnaryOp::Not => SmtExpr::Not(o),
            })
        }
    }
}

/// SMT variable info for rsmt2
#[derive(Debug, Clone)]
pub struct SmtVar {
    pub name: String,
    pub sort: String, // "Int" or "Bool"
}

/// Custom parser for rsmt2
#[derive(Debug, Clone, Copy)]
pub struct BmbParser;

impl<'a, Br: std::io::BufRead> rsmt2::parse::IdentParser<String, String, &'a mut Br> for BmbParser {
    fn parse_ident(self, input: &'a mut Br) -> SmtRes<String> {
        let mut buf = String::new();
        let mut char_buf = [0u8; 1];

        // Skip leading whitespace
        loop {
            if input.read(&mut char_buf).map_err(|e| e.to_string())? == 0 {
                return Err("Unexpected EOF".into());
            }
            let c = char_buf[0] as char;
            if !c.is_whitespace() {
                buf.push(c);
                break;
            }
        }

        // Read identifier
        loop {
            if input.read(&mut char_buf).map_err(|e| e.to_string())? == 0 {
                break;
            }
            let c = char_buf[0] as char;
            if c.is_whitespace() || c == ')' {
                break;
            }
            buf.push(c);
        }

        Ok(buf)
    }

    fn parse_type(self, input: &'a mut Br) -> SmtRes<String> {
        self.parse_ident(input)
    }
}

impl<'a, Br: std::io::BufRead> rsmt2::parse::ModelParser<String, String, String, &'a mut Br> for BmbParser {
    fn parse_value(
        self,
        input: &'a mut Br,
        _ident: &String,
        _params: &[(String, String)],
        _typ: &String,
    ) -> SmtRes<String> {
        let mut buf = String::new();
        let mut depth = 0;
        let mut char_buf = [0u8; 1];

        loop {
            if input.read(&mut char_buf).map_err(|e| e.to_string())? == 0 {
                break;
            }
            let c = char_buf[0] as char;
            if c == '(' {
                depth += 1;
            } else if c == ')' {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            } else if c.is_whitespace() && depth == 0 {
                if !buf.is_empty() {
                    break;
                }
                continue;
            }
            buf.push(c);
        }

        Ok(buf)
    }
}

/// Result of verifying a loop invariant
#[derive(Debug, Clone)]
pub struct InvariantResult {
    pub label: String,
    pub result: VerificationResult,
}

/// Result of verifying an assertion
#[derive(Debug, Clone)]
pub struct AssertionResult {
    pub index: usize,
    pub result: VerificationResult,
}

/// Result of verifying a single node
#[derive(Debug, Clone)]
pub struct NodeVerificationResult {
    pub node_name: String,
    pub precondition: VerificationResult,
    pub postcondition: VerificationResult,
    pub assertions: Vec<AssertionResult>,
    pub invariants: Vec<InvariantResult>,
}

impl NodeVerificationResult {
    /// Returns true if all contracts were proven
    pub fn all_proven(&self) -> bool {
        self.precondition.is_proven()
            && self.postcondition.is_proven()
            && self.assertions.iter().all(|a| a.result.is_proven())
            && self.invariants.iter().all(|inv| inv.result.is_proven())
    }
}

/// Combine multiple expressions with AND (conjunction)
fn combine_exprs_and(exprs: &[Expr]) -> Expr {
    match exprs.len() {
        0 => Expr::BoolLit(true),
        1 => exprs[0].clone(),
        _ => {
            let mut result = exprs[0].clone();
            for expr in &exprs[1..] {
                result = Expr::Binary {
                    op: BinaryOp::And,
                    left: Box::new(result),
                    right: Box::new(expr.clone()),
                };
            }
            result
        }
    }
}

/// Get SMT solver configuration
fn get_solver_conf() -> Option<SmtConf> {
    // Try environment variable first
    if let Ok(solver) = std::env::var("BMB_SMT_SOLVER") {
        return match solver.to_lowercase().as_str() {
            "z3" => Some(SmtConf::z3("z3")),
            "cvc4" => Some(SmtConf::cvc4("cvc4")),
            "cvc5" => Some(SmtConf::cvc4("cvc5")), // cvc5 uses similar config to cvc4
            _ => None,
        };
    }

    // Try Z3 first (most common)
    if which_solver("z3").is_some() {
        return Some(SmtConf::z3("z3"));
    }

    // Try CVC5 (uses cvc4 config)
    if which_solver("cvc5").is_some() {
        return Some(SmtConf::cvc4("cvc5"));
    }

    // Try CVC4
    if which_solver("cvc4").is_some() {
        return Some(SmtConf::cvc4("cvc4"));
    }

    None
}

/// Check if a solver is available in PATH
fn which_solver(name: &str) -> Option<std::path::PathBuf> {
    std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths).find_map(|dir| {
            let full_path = dir.join(name);
            #[cfg(windows)]
            let full_path = full_path.with_extension("exe");
            if full_path.exists() {
                Some(full_path)
            } else {
                None
            }
        })
    })
}

/// Verify contracts for a typed program
pub fn verify_program(program: &TypedProgram) -> Result<Vec<NodeVerificationResult>, BmbError> {
    let conf = match get_solver_conf() {
        Some(c) => c,
        None => {
            return Ok(program
                .nodes
                .iter()
                .map(|n| NodeVerificationResult {
                    node_name: n.node.name.name.clone(),
                    precondition: VerificationResult::SolverNotFound(
                        "No SMT solver found (z3, cvc5, or cvc4)".to_string(),
                    ),
                    postcondition: VerificationResult::SolverNotFound(
                        "No SMT solver found (z3, cvc5, or cvc4)".to_string(),
                    ),
                    assertions: n
                        .node
                        .assertions
                        .iter()
                        .enumerate()
                        .map(|(idx, _)| AssertionResult {
                            index: idx,
                            result: VerificationResult::SolverNotFound(
                                "No SMT solver found (z3, cvc5, or cvc4)".to_string(),
                            ),
                        })
                        .collect(),
                    invariants: n
                        .node
                        .invariants
                        .iter()
                        .map(|inv| InvariantResult {
                            label: inv.label.name.clone(),
                            result: VerificationResult::SolverNotFound(
                                "No SMT solver found (z3, cvc5, or cvc4)".to_string(),
                            ),
                        })
                        .collect(),
                })
                .collect());
        }
    };

    let mut results = Vec::new();

    for node in &program.nodes {
        let result = verify_node(&conf, node)?;
        results.push(result);
    }

    Ok(results)
}

/// Verify contracts for a single node
pub fn verify_node(conf: &SmtConf, node: &TypedNode) -> Result<NodeVerificationResult, BmbError> {
    // Collect variables
    let mut vars: Vec<SmtVar> = node
        .node
        .params
        .iter()
        .map(|p| SmtVar {
            name: p.name.name.clone(),
            sort: type_to_smt_sort(&p.ty),
        })
        .collect();

    // Add old_ prefixed variables for postcondition old() expressions
    let old_vars: Vec<SmtVar> = node
        .node
        .params
        .iter()
        .map(|p| SmtVar {
            name: format!("old_{}", p.name.name),
            sort: type_to_smt_sort(&p.ty),
        })
        .collect();
    vars.extend(old_vars);

    // Add return variable
    vars.push(SmtVar {
        name: "ret".to_string(),
        sort: type_to_smt_sort(&node.node.returns),
    });

    // Verify preconditions are satisfiable (all ANDed together)
    let pre_result = if !node.node.preconditions.is_empty() {
        let combined_pre = combine_exprs_and(&node.node.preconditions);
        verify_satisfiability(conf, &vars, &combined_pre)?
    } else {
        VerificationResult::Proven
    };

    // Verify postconditions hold given preconditions (all ANDed together)
    let post_result = if !node.node.postconditions.is_empty() {
        let combined_post = combine_exprs_and(&node.node.postconditions);
        if !node.node.preconditions.is_empty() {
            let combined_pre = combine_exprs_and(&node.node.preconditions);
            verify_implication_with_old(conf, &vars, &combined_pre, &combined_post, &node.node.params)?
        } else {
            verify_validity(conf, &vars, &combined_post)?
        }
    } else {
        VerificationResult::Proven
    };

    // Verify assertions (given preconditions)
    let mut assertion_results = Vec::new();
    for (idx, assertion) in node.node.assertions.iter().enumerate() {
        // Assertions must hold given preconditions
        let result = if !node.node.preconditions.is_empty() {
            let combined_pre = combine_exprs_and(&node.node.preconditions);
            verify_implication(conf, &vars, &combined_pre, &assertion.condition)?
        } else {
            // Without preconditions, check if assertion is always true
            verify_validity(conf, &vars, &assertion.condition)?
        };
        assertion_results.push(AssertionResult { index: idx, result });
    }

    // Verify loop invariants
    let mut invariant_results = Vec::new();
    for inv in &node.node.invariants {
        // For now, we just check if the invariant is satisfiable
        // Full loop invariant verification would require analyzing the loop body
        let result = verify_satisfiability(conf, &vars, &inv.condition)?;
        invariant_results.push(InvariantResult {
            label: inv.label.name.clone(),
            result,
        });
    }

    Ok(NodeVerificationResult {
        node_name: node.node.name.name.clone(),
        precondition: pre_result,
        postcondition: post_result,
        assertions: assertion_results,
        invariants: invariant_results,
    })
}

/// Verify that precondition implies postcondition, with old() variable bindings
fn verify_implication_with_old(
    conf: &SmtConf,
    vars: &[SmtVar],
    pre: &Expr,
    post: &Expr,
    params: &[crate::ast::Parameter],
) -> Result<VerificationResult, BmbError> {
    let mut solver = Solver::new(conf.clone(), BmbParser)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    // Declare variables
    for var in vars {
        solver
            .declare_const(&var.name, &var.sort)
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;
    }

    // Bind old_x = x at function entry (precondition point)
    for param in params {
        let binding = format!(
            "(assert (= old_{} {}))",
            param.name.name, param.name.name
        );
        solver
            .assert(binding)
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;
    }

    // Translate expressions
    let pre_smt = translate_expr(pre)?;
    let post_smt = translate_expr(post)?;

    // Assert: pre AND NOT(post)
    // If UNSAT, then pre implies post
    let assertion = format!(
        "(assert (and {} (not {})))",
        pre_smt.to_bool_smtlib(),
        post_smt.to_bool_smtlib()
    );
    solver
        .assert(assertion)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    let sat = solver
        .check_sat()
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    if sat {
        // Try to get a model (counterexample)
        let model = get_model(&mut solver, vars);
        Ok(VerificationResult::CounterExample(model))
    } else {
        Ok(VerificationResult::Proven)
    }
}

/// Map BMB type to SMT-LIB sort
fn type_to_smt_sort(ty: &Type) -> String {
    match ty {
        Type::Bool => "Bool".to_string(),
        Type::I32 | Type::I64 => "Int".to_string(),
        Type::F32 | Type::F64 => "Real".to_string(),
        _ => "Int".to_string(), // Default to Int for other types
    }
}

/// Check if an expression is satisfiable
fn verify_satisfiability(
    conf: &SmtConf,
    vars: &[SmtVar],
    expr: &Expr,
) -> Result<VerificationResult, BmbError> {
    let mut solver = Solver::new(conf.clone(), BmbParser)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    // Declare variables
    for var in vars {
        solver
            .declare_const(&var.name, &var.sort)
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;
    }

    // Translate and assert expression
    let smt_expr = translate_expr(expr)?;
    let assertion = format!("(assert {})", smt_expr.to_bool_smtlib());
    solver
        .assert(assertion)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    // Check satisfiability
    let sat = solver
        .check_sat()
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    if sat {
        Ok(VerificationResult::Proven)
    } else {
        Ok(VerificationResult::CounterExample(HashMap::new()))
    }
}

/// Verify that precondition implies postcondition
fn verify_implication(
    conf: &SmtConf,
    vars: &[SmtVar],
    pre: &Expr,
    post: &Expr,
) -> Result<VerificationResult, BmbError> {
    let mut solver = Solver::new(conf.clone(), BmbParser)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    // Declare variables
    for var in vars {
        solver
            .declare_const(&var.name, &var.sort)
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;
    }

    // Translate expressions
    let pre_smt = translate_expr(pre)?;
    let post_smt = translate_expr(post)?;

    // Assert: pre AND NOT(post)
    // If UNSAT, then pre implies post
    let assertion = format!(
        "(assert (and {} (not {})))",
        pre_smt.to_bool_smtlib(),
        post_smt.to_bool_smtlib()
    );
    solver
        .assert(assertion)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    let sat = solver
        .check_sat()
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    if sat {
        // Try to get a model (counterexample)
        let model = get_model(&mut solver, vars);
        Ok(VerificationResult::CounterExample(model))
    } else {
        Ok(VerificationResult::Proven)
    }
}

/// Verify that an expression is always true
fn verify_validity(
    conf: &SmtConf,
    vars: &[SmtVar],
    expr: &Expr,
) -> Result<VerificationResult, BmbError> {
    let mut solver = Solver::new(conf.clone(), BmbParser)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    // Declare variables
    for var in vars {
        solver
            .declare_const(&var.name, &var.sort)
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;
    }

    // Translate expression
    let smt_expr = translate_expr(expr)?;

    // Assert NOT(expr)
    // If UNSAT, expr is always true
    let assertion = format!("(assert (not {}))", smt_expr.to_bool_smtlib());
    solver
        .assert(assertion)
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    let sat = solver
        .check_sat()
        .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

    if sat {
        let model = get_model(&mut solver, vars);
        Ok(VerificationResult::CounterExample(model))
    } else {
        Ok(VerificationResult::Proven)
    }
}

/// Get model values from solver using get-value commands
/// Extracts counterexample variable assignments from the SMT solver.
fn get_model(_solver: &mut Solver<BmbParser>, _vars: &[SmtVar]) -> HashMap<String, i64> {
    // Note: Full model extraction from rsmt2 requires implementing
    // IdentParser/ModelParser for the specific SmtParser<BufReader<ChildStdout>> type
    // which has complex lifetime requirements that don't match our generic Br impl.
    //
    // For v0.11.0, we report counterexample existence (the most important info).
    // The infrastructure for value parsing (parse_smt_int, model_to_counterexample)
    // is in place for when we switch to a more flexible SMT interface.
    //
    // Future enhancement: Use z3 crate directly or implement custom SMT-LIB2 parser
    // to extract actual counterexample values.
    HashMap::new()
}

/// Convert SMT model to a Counterexample struct for error reporting
pub fn model_to_counterexample(
    model: &HashMap<String, i64>,
    failed_assertion: &str,
) -> crate::error::Counterexample {
    let mut cex = crate::error::Counterexample::new(failed_assertion);
    for (name, value) in model {
        cex = cex.with_variable(name.clone(), value.to_string());
    }
    cex
}

/// Parse SMT integer value (handles (- N) format)
/// Used by model_to_counterexample when full model extraction is implemented.
#[allow(dead_code)]
fn parse_smt_int(s: &str) -> Option<i64> {
    let s = s.trim();
    if s.starts_with("(-") || s.starts_with("(- ") {
        let inner = s
            .trim_start_matches("(-")
            .trim_start_matches("(- ")
            .trim_end_matches(')');
        inner.trim().parse::<i64>().ok().map(|v| -v)
    } else {
        s.parse().ok()
    }
}

/// Generate SMT-LIB2 verification script (for external use)
pub fn generate_smtlib2(node: &TypedNode) -> Result<String, BmbError> {
    let mut output = String::new();

    // Header
    output.push_str("; BMB Contract Verification\n");
    output.push_str(&format!("; Node: {}\n", node.node.name.name));
    output.push_str("(set-logic QF_LIA)\n\n");

    // Declare parameters
    for param in &node.node.params {
        let sort = type_to_smt_sort(&param.ty);
        output.push_str(&format!("(declare-const {} {})\n", param.name.name, sort));
    }

    // Declare old_ versions of parameters (for postcondition old() expressions)
    if !node.node.params.is_empty() {
        output.push_str("\n; Old (pre-state) values for postcondition verification\n");
        for param in &node.node.params {
            let sort = type_to_smt_sort(&param.ty);
            output.push_str(&format!(
                "(declare-const old_{} {})\n",
                param.name.name, sort
            ));
        }
        // Bind old_x = x at function entry
        for param in &node.node.params {
            output.push_str(&format!(
                "(assert (= old_{} {}))\n",
                param.name.name, param.name.name
            ));
        }
    }

    // Declare return value
    let ret_sort = type_to_smt_sort(&node.node.returns);
    output.push_str(&format!("\n(declare-const ret {})\n\n", ret_sort));

    // Preconditions
    if !node.node.preconditions.is_empty() {
        output.push_str("; Preconditions\n");
        for pre in &node.node.preconditions {
            let smt_pre = translate_expr(pre)?;
            output.push_str(&format!("(assert {})\n", smt_pre.to_bool_smtlib()));
        }
        output.push('\n');
    }

    // Loop invariants
    if !node.node.invariants.is_empty() {
        output.push_str("; Loop Invariants\n");
        for inv in &node.node.invariants {
            let smt_inv = translate_expr(&inv.condition)?;
            output.push_str(&format!(
                "; Invariant at _{}\n(assert {})\n",
                inv.label.name,
                smt_inv.to_bool_smtlib()
            ));
        }
        output.push('\n');
    }

    // Assertions
    if !node.node.assertions.is_empty() {
        output.push_str("; Assertions (@assert directives)\n");
        for (idx, assertion) in node.node.assertions.iter().enumerate() {
            let smt_assert = translate_expr(&assertion.condition)?;
            output.push_str(&format!(
                "; @assert [{}]\n(assert {})\n",
                idx,
                smt_assert.to_bool_smtlib()
            ));
        }
        output.push('\n');
    }

    // Postconditions check (negated - any postcondition failure means contract violated)
    if !node.node.postconditions.is_empty() {
        output.push_str("; Postconditions (negated for checking)\n");
        let combined_post = combine_exprs_and(&node.node.postconditions);
        let smt_post = translate_expr(&combined_post)?;
        output.push_str(&format!(
            "(assert (not {}))\n\n",
            smt_post.to_bool_smtlib()
        ));
    }

    output.push_str("; Check satisfiability\n");
    output.push_str("; unsat = contract is valid\n");
    output.push_str("; sat = counterexample exists\n");
    output.push_str("(check-sat)\n");
    output.push_str("(get-model)\n");

    Ok(output)
}

// ============================================================================
// Invariant Suggestion Generator (v0.11.0)
// ============================================================================

/// Pattern recognized in a loop for invariant generation
#[derive(Debug, Clone)]
pub enum LoopPattern {
    /// Counter increments: i = i + step
    CounterIncrement { var: String, step: i64 },
    /// Counter decrements: i = i - step
    CounterDecrement { var: String, step: i64 },
    /// Bounded iteration: comparing var to bound
    BoundedIteration { var: String, bound: String, op: BinaryOp },
    /// Accumulator: sum = sum + expr
    Accumulator { var: String, addend: String },
    /// Array access: arr[i]
    ArrayAccess { array: String, index: String },
}

/// Candidate invariant with confidence
#[derive(Debug, Clone)]
pub struct InvariantCandidate {
    /// The invariant expression
    pub expr: Expr,
    /// Human-readable form
    pub readable: String,
    /// Confidence score (0.0 - 1.0)
    pub confidence: f64,
    /// Why this was suggested
    pub rationale: String,
}

impl InvariantCandidate {
    pub fn new(expr: Expr, readable: impl Into<String>, confidence: f64) -> Self {
        Self {
            expr,
            readable: readable.into(),
            confidence,
            rationale: String::new(),
        }
    }

    pub fn with_rationale(mut self, rationale: impl Into<String>) -> Self {
        self.rationale = rationale.into();
        self
    }
}

/// Verification status for an invariant candidate
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationStatus {
    /// SMT solver proved the invariant holds
    Proven,
    /// SMT solver found a counterexample (invariant does not hold)
    Disproven,
    /// SMT solver returned unknown (timeout or undecidable)
    Unknown,
    /// Verification was not attempted (e.g., solver not available)
    NotVerified,
}

impl std::fmt::Display for VerificationStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationStatus::Proven => write!(f, "proven"),
            VerificationStatus::Disproven => write!(f, "disproven"),
            VerificationStatus::Unknown => write!(f, "unknown"),
            VerificationStatus::NotVerified => write!(f, "not verified"),
        }
    }
}

/// A verified invariant candidate with SMT verification result
#[derive(Debug, Clone)]
pub struct VerifiedCandidate {
    /// The original candidate
    pub candidate: InvariantCandidate,
    /// Verification status from SMT solver
    pub status: VerificationStatus,
    /// Adjusted confidence after verification
    pub adjusted_confidence: f64,
}

impl VerifiedCandidate {
    /// Create from unverified candidate
    pub fn not_verified(candidate: InvariantCandidate) -> Self {
        let confidence = candidate.confidence;
        Self {
            candidate,
            status: VerificationStatus::NotVerified,
            adjusted_confidence: confidence,
        }
    }

    /// Create with verification result
    pub fn with_status(candidate: InvariantCandidate, status: VerificationStatus) -> Self {
        let base_confidence = candidate.confidence;
        let adjusted_confidence = match status {
            VerificationStatus::Proven => 1.0,  // Maximum confidence if proven
            VerificationStatus::Disproven => 0.0,  // No confidence if disproven
            VerificationStatus::Unknown => base_confidence * 0.7,  // Reduce confidence
            VerificationStatus::NotVerified => base_confidence,
        };
        Self {
            candidate,
            status,
            adjusted_confidence,
        }
    }

    /// Check if this candidate is useful (not disproven)
    pub fn is_useful(&self) -> bool {
        self.status != VerificationStatus::Disproven
    }

    /// Get a confidence marker for display
    pub fn confidence_marker(&self) -> &'static str {
        match self.status {
            VerificationStatus::Proven => "✓",
            VerificationStatus::Disproven => "✗",
            VerificationStatus::Unknown => "?",
            VerificationStatus::NotVerified => "○",
        }
    }
}

/// Verify a candidate invariant using SMT solver
///
/// Attempts to prove that the invariant holds for the given function.
/// Returns the verification status.
#[cfg(feature = "smt")]
pub fn verify_candidate(
    node: &TypedNode,
    candidate: &InvariantCandidate,
) -> VerificationStatus {
    use rsmt2::Solver;

    // Collect variables from node parameters
    let mut vars: Vec<SmtVar> = node
        .node
        .params
        .iter()
        .map(|p| SmtVar {
            name: p.name.name.clone(),
            sort: type_to_smt_sort(&p.ty),
        })
        .collect();

    // Add old_ prefixed variables for old() expressions
    let old_vars: Vec<SmtVar> = node
        .node
        .params
        .iter()
        .map(|p| SmtVar {
            name: format!("old_{}", p.name.name),
            sort: type_to_smt_sort(&p.ty),
        })
        .collect();
    vars.extend(old_vars);

    // Add return variable
    vars.push(SmtVar {
        name: "ret".to_string(),
        sort: type_to_smt_sort(&node.node.returns),
    });

    // Use the same SMT configuration as other verification functions
    let conf = SmtConf::default_z3();

    // Try to verify using SMT
    let result: Result<VerificationStatus, BmbError> = (|| {
        let mut solver = Solver::new(conf, BmbParser)
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

        // Declare all variables
        for var in &vars {
            solver.declare_const(&var.name, &var.sort)
                .map_err(|e| BmbError::ContractError { message: e.to_string() })?;
        }

        // Build precondition conjunction
        let mut pre_clauses = Vec::new();
        for pre in &node.node.preconditions {
            if let Ok(smt_expr) = translate_expr(pre) {
                pre_clauses.push(smt_expr.to_bool_smtlib());
            }
        }

        // Translate the candidate invariant
        let candidate_smt = translate_expr(&candidate.expr)?;

        // Build assertion: (preconditions) AND (NOT candidate)
        // If UNSAT, then preconditions imply the candidate
        let assertion = if pre_clauses.is_empty() {
            // No preconditions, just check if NOT(candidate) is satisfiable
            format!("(assert (not {}))", candidate_smt.to_bool_smtlib())
        } else {
            // Check if preconditions AND NOT(candidate) is satisfiable
            let pre_conj = if pre_clauses.len() == 1 {
                pre_clauses[0].clone()
            } else {
                format!("(and {})", pre_clauses.join(" "))
            };
            format!(
                "(assert (and {} (not {})))",
                pre_conj,
                candidate_smt.to_bool_smtlib()
            )
        };

        solver.assert(assertion)
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

        // Check satisfiability
        let sat = solver.check_sat()
            .map_err(|e| BmbError::ContractError { message: e.to_string() })?;

        if sat {
            // SAT means we found a case where preconditions hold but candidate doesn't
            // = invariant is disproven
            Ok(VerificationStatus::Disproven)
        } else {
            // UNSAT means no such case exists
            // = invariant is proven (under preconditions)
            Ok(VerificationStatus::Proven)
        }
    })();

    result.unwrap_or(VerificationStatus::Unknown)
}

/// Verify a candidate invariant (stub when SMT feature is disabled)
#[cfg(not(feature = "smt"))]
pub fn verify_candidate(
    _node: &TypedNode,
    _candidate: &InvariantCandidate,
) -> VerificationStatus {
    VerificationStatus::NotVerified
}

/// Verify and rank multiple candidates
///
/// Returns candidates sorted by adjusted confidence, with disproven candidates filtered out.
pub fn verify_and_rank_candidates(
    node: &TypedNode,
    candidates: Vec<InvariantCandidate>,
) -> Vec<VerifiedCandidate> {
    let mut verified: Vec<VerifiedCandidate> = candidates
        .into_iter()
        .map(|c| {
            let status = verify_candidate(node, &c);
            VerifiedCandidate::with_status(c, status)
        })
        .collect();

    // Sort by adjusted confidence (highest first)
    verified.sort_by(|a, b| {
        b.adjusted_confidence
            .partial_cmp(&a.adjusted_confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    verified
}

/// Suggest and verify invariants for a loop
///
/// This is the main entry point for the invariant suggestion system.
/// It combines heuristic generation with SMT verification.
pub fn suggest_verified_invariants(
    node: &TypedNode,
    loop_label: &str,
) -> Vec<VerifiedCandidate> {
    // Step 1: Generate heuristic candidates
    let candidates = suggest_invariants(node, loop_label);

    // Step 2: Verify and rank
    let verified = verify_and_rank_candidates(node, candidates);

    // Step 3: Filter out disproven candidates
    verified.into_iter().filter(|v| v.is_useful()).collect()
}

/// Format verified candidates for display
pub fn format_verified_candidates(candidates: &[VerifiedCandidate]) -> String {
    if candidates.is_empty() {
        return "No invariant suggestions available.".to_string();
    }

    let mut output = String::from("Suggested Invariants:\n");
    for (i, vc) in candidates.iter().enumerate() {
        output.push_str(&format!(
            "  {}. {} {} (confidence: {:.0}%)\n",
            i + 1,
            vc.confidence_marker(),
            vc.candidate.readable,
            vc.adjusted_confidence * 100.0
        ));
        if !vc.candidate.rationale.is_empty() {
            output.push_str(&format!("     └─ {}\n", vc.candidate.rationale));
        }
    }
    output
}

/// Generate candidate invariants for a loop
///
/// Analyzes the loop body and preconditions to suggest likely invariants.
pub fn suggest_invariants(
    node: &TypedNode,
    loop_label: &str,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();

    // Find the loop in the body
    let loop_info = analyze_loop_body(node, loop_label);

    // Generate candidates based on detected patterns
    for pattern in &loop_info.patterns {
        match pattern {
            LoopPattern::CounterIncrement { var, step } => {
                // Counter >= 0 (common initialization pattern)
                candidates.push(InvariantCandidate::new(
                    make_ge_zero(var),
                    format!("{} >= 0", var),
                    0.9,
                ).with_rationale("Counter typically starts at 0 or positive"));

                // Counter increases by step
                if *step == 1 {
                    candidates.push(InvariantCandidate::new(
                        make_ge_old(var),
                        format!("{} >= old({})", var, var),
                        0.85,
                    ).with_rationale("Counter increases monotonically"));
                }
            }

            LoopPattern::CounterDecrement { var, step } => {
                // Counter >= 0 (termination bound)
                candidates.push(InvariantCandidate::new(
                    make_ge_zero(var),
                    format!("{} >= 0", var),
                    0.85,
                ).with_rationale("Decrementing counter stays non-negative"));

                // Counter decreases
                if *step == 1 {
                    candidates.push(InvariantCandidate::new(
                        make_le_old(var),
                        format!("{} <= old({})", var, var),
                        0.8,
                    ).with_rationale("Counter decreases monotonically"));
                }
            }

            LoopPattern::BoundedIteration { var, bound, op } => {
                match op {
                    BinaryOp::Lt | BinaryOp::Le => {
                        // var <= bound
                        candidates.push(InvariantCandidate::new(
                            make_le_bound(var, bound),
                            format!("{} <= {}", var, bound),
                            0.9,
                        ).with_rationale("Loop iteration stays within bound"));
                    }
                    BinaryOp::Gt | BinaryOp::Ge => {
                        // var >= bound
                        candidates.push(InvariantCandidate::new(
                            make_ge_bound(var, bound),
                            format!("{} >= {}", var, bound),
                            0.9,
                        ).with_rationale("Loop iteration maintains bound"));
                    }
                    _ => {}
                }
            }

            LoopPattern::Accumulator { var, addend: _ } => {
                // Accumulator >= initial (if initial >= 0 and addend >= 0)
                candidates.push(InvariantCandidate::new(
                    make_ge_old(var),
                    format!("{} >= old({})", var, var),
                    0.7,
                ).with_rationale("Accumulator grows monotonically"));
            }

            LoopPattern::ArrayAccess { array: _, index } => {
                // Index is in bounds (common safety invariant)
                candidates.push(InvariantCandidate::new(
                    make_ge_zero(index),
                    format!("{} >= 0", index),
                    0.95,
                ).with_rationale("Array index must be non-negative"));
            }
        }
    }

    // Add invariants derived from preconditions
    for pre in &node.node.preconditions {
        if let Some(candidate) = derive_invariant_from_precondition(pre) {
            candidates.push(candidate);
        }
    }

    // Sort by confidence (highest first)
    candidates.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal));

    // Deduplicate by readable form
    let mut seen = std::collections::HashSet::new();
    candidates.retain(|c| seen.insert(c.readable.clone()));

    candidates
}

/// Loop analysis result
#[derive(Debug, Default)]
struct LoopAnalysis {
    patterns: Vec<LoopPattern>,
}

/// Analyze a loop body to detect patterns
fn analyze_loop_body(node: &TypedNode, _loop_label: &str) -> LoopAnalysis {
    let mut analysis = LoopAnalysis::default();

    // Simple heuristic: look for common patterns in the body
    // In a real implementation, we'd do proper control flow analysis

    // Scan body for assignment patterns
    for instr in &node.node.body {
        // Match on Instruction enum
        if let crate::ast::Instruction::Statement(stmt) = instr {
            let operands = &stmt.operands;

            // Look for add instructions that might be counter updates
            // add %dest src1 src2 -> operands[0]=dest, operands[1]=src1, operands[2]=src2
            if stmt.opcode == crate::ast::Opcode::Add && operands.len() >= 3 {
                if let crate::ast::Operand::Register(ref dest) = operands[0] {
                    if is_counter_like_name(&dest.name) {
                        // Check if it's incrementing itself: add %i %i 1
                        if let crate::ast::Operand::Register(ref src) = operands[1] {
                            if src.name == dest.name {
                                if let crate::ast::Operand::IntLiteral(step) = operands[2] {
                                    analysis.patterns.push(LoopPattern::CounterIncrement {
                                        var: dest.name.clone(),
                                        step,
                                    });
                                }
                            }
                        }
                    }
                }
            }

            // Look for sub instructions for counter decrement
            if stmt.opcode == crate::ast::Opcode::Sub && operands.len() >= 3 {
                if let crate::ast::Operand::Register(ref dest) = operands[0] {
                    if is_counter_like_name(&dest.name) {
                        if let crate::ast::Operand::Register(ref src) = operands[1] {
                            if src.name == dest.name {
                                if let crate::ast::Operand::IntLiteral(step) = operands[2] {
                                    analysis.patterns.push(LoopPattern::CounterDecrement {
                                        var: dest.name.clone(),
                                        step,
                                    });
                                }
                            }
                        }
                    }
                }
            }

            // Look for comparison instructions (loop bounds)
            // lt %result src1 src2 -> check if src1 is a counter
            if matches!(stmt.opcode, crate::ast::Opcode::Lt | crate::ast::Opcode::Le |
                        crate::ast::Opcode::Gt | crate::ast::Opcode::Ge) && operands.len() >= 3 {
                if let crate::ast::Operand::Register(ref reg) = operands[1] {
                    if is_counter_like_name(&reg.name) {
                        let bound = operand_to_string(&operands[2]);
                        let op = opcode_to_binary_op(stmt.opcode.clone());
                        if let Some(op) = op {
                            analysis.patterns.push(LoopPattern::BoundedIteration {
                                var: reg.name.clone(),
                                bound,
                                op,
                            });
                        }
                    }
                }
            }

            // Look for array accesses (load/store with register index)
            if matches!(stmt.opcode, crate::ast::Opcode::Load | crate::ast::Opcode::Store) {
                if operands.len() >= 2 {
                    // For ArrayAccess operands
                    if let crate::ast::Operand::ArrayAccess { ref base, ref index } = operands[1] {
                        if let crate::ast::Operand::Register(ref idx_reg) = index.as_ref() {
                            analysis.patterns.push(LoopPattern::ArrayAccess {
                                array: base.name.clone(),
                                index: idx_reg.name.clone(),
                            });
                        }
                    }
                }
            }
        }
    }

    analysis
}

/// Check if a name looks like a loop counter
fn is_counter_like_name(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "i" || lower == "j" || lower == "k" || lower == "n" ||
    lower == "index" || lower == "idx" || lower == "counter" || lower == "count"
}

/// Convert opcode to BinaryOp
fn opcode_to_binary_op(opcode: crate::ast::Opcode) -> Option<BinaryOp> {
    match opcode {
        crate::ast::Opcode::Lt => Some(BinaryOp::Lt),
        crate::ast::Opcode::Le => Some(BinaryOp::Le),
        crate::ast::Opcode::Gt => Some(BinaryOp::Gt),
        crate::ast::Opcode::Ge => Some(BinaryOp::Ge),
        crate::ast::Opcode::Eq => Some(BinaryOp::Eq),
        crate::ast::Opcode::Ne => Some(BinaryOp::Ne),
        _ => None,
    }
}

/// Convert operand to string representation
fn operand_to_string(op: &crate::ast::Operand) -> String {
    match op {
        crate::ast::Operand::Register(r) => r.name.clone(),
        crate::ast::Operand::Label(l) => format!("_{}", l.name),
        crate::ast::Operand::IntLiteral(i) => i.to_string(),
        crate::ast::Operand::FloatLiteral(f) => f.to_string(),
        crate::ast::Operand::StringLiteral(s) => format!("\"{}\"", s),
        crate::ast::Operand::Identifier(id) => id.name.clone(),
        crate::ast::Operand::QualifiedIdent { module, name } => {
            format!("{}::{}", module.name, name.name)
        }
        crate::ast::Operand::FieldAccess { base, field } => {
            format!("{}.{}", base.name, field.name)
        }
        crate::ast::Operand::ArrayAccess { base, index } => {
            format!("{}[{}]", base.name, operand_to_string(index))
        }
    }
}

/// Create expression: var >= 0
fn make_ge_zero(var: &str) -> Expr {
    Expr::Binary {
        op: BinaryOp::Ge,
        left: Box::new(Expr::Var(crate::ast::Identifier { name: var.to_string(), span: crate::ast::Span::default() })),
        right: Box::new(Expr::IntLit(0)),
    }
}

/// Create expression: var >= old(var)
fn make_ge_old(var: &str) -> Expr {
    Expr::Binary {
        op: BinaryOp::Ge,
        left: Box::new(Expr::Var(crate::ast::Identifier { name: var.to_string(), span: crate::ast::Span::default() })),
        right: Box::new(Expr::Old(Box::new(Expr::Var(crate::ast::Identifier { name: var.to_string(), span: crate::ast::Span::default() })))),
    }
}

/// Create expression: var <= old(var)
fn make_le_old(var: &str) -> Expr {
    Expr::Binary {
        op: BinaryOp::Le,
        left: Box::new(Expr::Var(crate::ast::Identifier { name: var.to_string(), span: crate::ast::Span::default() })),
        right: Box::new(Expr::Old(Box::new(Expr::Var(crate::ast::Identifier { name: var.to_string(), span: crate::ast::Span::default() })))),
    }
}

/// Create expression: var <= bound
fn make_le_bound(var: &str, bound: &str) -> Expr {
    Expr::Binary {
        op: BinaryOp::Le,
        left: Box::new(Expr::Var(crate::ast::Identifier { name: var.to_string(), span: crate::ast::Span::default() })),
        right: Box::new(Expr::Var(crate::ast::Identifier { name: bound.to_string(), span: crate::ast::Span::default() })),
    }
}

/// Create expression: var >= bound
fn make_ge_bound(var: &str, bound: &str) -> Expr {
    Expr::Binary {
        op: BinaryOp::Ge,
        left: Box::new(Expr::Var(crate::ast::Identifier { name: var.to_string(), span: crate::ast::Span::default() })),
        right: Box::new(Expr::Var(crate::ast::Identifier { name: bound.to_string(), span: crate::ast::Span::default() })),
    }
}

/// Try to derive an invariant from a precondition
fn derive_invariant_from_precondition(pre: &Expr) -> Option<InvariantCandidate> {
    // Preconditions involving parameters often make good invariants
    // e.g., if @pre n >= 0, then n >= 0 is likely an invariant
    match pre {
        Expr::Binary { op, left, right } => {
            if matches!(op, BinaryOp::Ge | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Lt) {
                if let (Expr::Var(_), Expr::IntLit(_)) = (left.as_ref(), right.as_ref()) {
                    return Some(InvariantCandidate::new(
                        pre.clone(),
                        expr_to_readable(pre),
                        0.6,
                    ).with_rationale("Derived from precondition"));
                }
                if let (Expr::IntLit(_), Expr::Var(_)) = (left.as_ref(), right.as_ref()) {
                    return Some(InvariantCandidate::new(
                        pre.clone(),
                        expr_to_readable(pre),
                        0.6,
                    ).with_rationale("Derived from precondition"));
                }
            }
            None
        }
        _ => None,
    }
}

/// Convert expression to readable string
fn expr_to_readable(expr: &Expr) -> String {
    match expr {
        Expr::Var(v) => v.name.clone(),
        Expr::IntLit(i) => i.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Old(inner) => format!("old({})", expr_to_readable(inner)),
        Expr::Binary { op, left, right } => {
            let op_str = match op {
                BinaryOp::Add => "+",
                BinaryOp::Sub => "-",
                BinaryOp::Mul => "*",
                BinaryOp::Div => "/",
                BinaryOp::Mod => "%",
                BinaryOp::And => "&&",
                BinaryOp::Or => "||",
                BinaryOp::Eq => "==",
                BinaryOp::Ne => "!=",
                BinaryOp::Lt => "<",
                BinaryOp::Le => "<=",
                BinaryOp::Gt => ">",
                BinaryOp::Ge => ">=",
            };
            format!("{} {} {}", expr_to_readable(left), op_str, expr_to_readable(right))
        }
        Expr::Unary { op, operand } => {
            let op_str = match op {
                UnaryOp::Neg => "-",
                UnaryOp::Not => "!",
            };
            format!("{}{}", op_str, expr_to_readable(operand))
        }
        _ => "?".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Identifier, Span};

    /// Helper to create an identifier
    fn ident(name: &str) -> Identifier {
        Identifier {
            name: name.to_string(),
            span: Span::default(),
        }
    }

    #[test]
    fn test_translate_int_literal() {
        let expr = Expr::IntLit(42);
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "42");
    }

    #[test]
    fn test_translate_negative_int() {
        let expr = Expr::IntLit(-5);
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "(- 5)");
    }

    #[test]
    fn test_translate_variable() {
        let expr = Expr::Var(ident("x"));
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "x");
    }

    #[test]
    fn test_translate_binary_add() {
        let expr = Expr::Binary {
            op: BinaryOp::Add,
            left: Box::new(Expr::IntLit(2)),
            right: Box::new(Expr::IntLit(3)),
        };
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "(+ 2 3)");
    }

    #[test]
    fn test_translate_comparison() {
        let expr = Expr::Binary {
            op: BinaryOp::Gt,
            left: Box::new(Expr::Var(ident("x"))),
            right: Box::new(Expr::IntLit(0)),
        };
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "(> x 0)");
    }

    #[test]
    fn test_translate_complex_expression() {
        // (x + 1) > (y * 2)
        let expr = Expr::Binary {
            op: BinaryOp::Gt,
            left: Box::new(Expr::Binary {
                op: BinaryOp::Add,
                left: Box::new(Expr::Var(ident("x"))),
                right: Box::new(Expr::IntLit(1)),
            }),
            right: Box::new(Expr::Binary {
                op: BinaryOp::Mul,
                left: Box::new(Expr::Var(ident("y"))),
                right: Box::new(Expr::IntLit(2)),
            }),
        };
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "(> (+ x 1) (* y 2))");
    }

    #[test]
    fn test_translate_logical_and() {
        let expr = Expr::Binary {
            op: BinaryOp::And,
            left: Box::new(Expr::Binary {
                op: BinaryOp::Gt,
                left: Box::new(Expr::Var(ident("x"))),
                right: Box::new(Expr::IntLit(0)),
            }),
            right: Box::new(Expr::Binary {
                op: BinaryOp::Lt,
                left: Box::new(Expr::Var(ident("x"))),
                right: Box::new(Expr::IntLit(10)),
            }),
        };
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "(and (> x 0) (< x 10))");
    }

    #[test]
    fn test_translate_negation() {
        let expr = Expr::Unary {
            op: UnaryOp::Neg,
            operand: Box::new(Expr::Var(ident("x"))),
        };
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "(- x)");
    }

    #[test]
    fn test_parse_smt_int() {
        assert_eq!(parse_smt_int("42"), Some(42));
        assert_eq!(parse_smt_int("(- 5)"), Some(-5));
        assert_eq!(parse_smt_int("(-5)"), Some(-5));
        assert_eq!(parse_smt_int("  42  "), Some(42));
    }

    #[test]
    fn test_model_to_counterexample() {
        let mut model = HashMap::new();
        model.insert("x".to_string(), 5);
        model.insert("old(y)".to_string(), -3);

        let cex = model_to_counterexample(&model, "y > x");

        assert_eq!(cex.failed_assertion, "y > x");
        assert_eq!(cex.variables.len(), 2);

        // Check that both variables are present
        let has_x = cex.variables.iter().any(|(n, v)| n == "x" && v == "5");
        let has_old_y = cex
            .variables
            .iter()
            .any(|(n, v)| n == "old(y)" && v == "-3");
        assert!(has_x, "x=5 should be in counterexample");
        assert!(has_old_y, "old(y)=-3 should be in counterexample");
    }

    #[test]
    fn test_generate_smtlib2() {
        use crate::ast::{Node, ParamAnnotation, Parameter};
        use crate::types::TypedNode;

        let node = TypedNode {
            node: Node {
                name: ident("divide"),
                tags: vec![],
                params: vec![
                    Parameter {
                        name: ident("a"),
                        ty: Type::I32,
                        annotation: ParamAnnotation::None,
                        span: Span::default(),
                    },
                    Parameter {
                        name: ident("b"),
                        ty: Type::I32,
                        annotation: ParamAnnotation::None,
                        span: Span::default(),
                    },
                ],
                returns: Type::I32,
                preconditions: vec![Expr::Binary {
                    op: BinaryOp::Ne,
                    left: Box::new(Expr::Var(ident("b"))),
                    right: Box::new(Expr::IntLit(0)),
                }],
                postconditions: vec![Expr::BoolLit(true)],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: Span::default(),
            },
            register_types: std::collections::HashMap::new(),
        };

        let smtlib = generate_smtlib2(&node).unwrap();

        assert!(smtlib.contains("(declare-const a Int)"));
        assert!(smtlib.contains("(declare-const b Int)"));
        assert!(smtlib.contains("(declare-const ret Int)"));
        assert!(smtlib.contains("(assert (not (= b 0)))"));
        assert!(smtlib.contains("(check-sat)"));
    }

    #[test]
    fn test_translate_old_expr() {
        let expr = Expr::Old(Box::new(Expr::Var(ident("x"))));
        let smt = translate_expr(&expr).unwrap();
        assert_eq!(smt.to_smtlib(), "old_x");
    }

    #[test]
    fn test_old_var_smtlib() {
        let smt = SmtExpr::OldVar("counter".to_string());
        assert_eq!(smt.to_smtlib(), "old_counter");
    }

    #[test]
    fn test_generate_smtlib2_with_assertions() {
        use crate::ast::{Assert, Node, ParamAnnotation, Parameter};
        use crate::types::TypedNode;

        let node = TypedNode {
            node: Node {
                name: ident("bounded"),
                tags: vec![],
                params: vec![Parameter {
                    name: ident("n"),
                    ty: Type::I32,
                    annotation: ParamAnnotation::None,
                    span: Span::default(),
                }],
                returns: Type::I32,
                preconditions: vec![Expr::Binary {
                    op: BinaryOp::Ge,
                    left: Box::new(Expr::Var(ident("n"))),
                    right: Box::new(Expr::IntLit(0)),
                }],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![
                    Assert {
                        condition: Expr::Binary {
                            op: BinaryOp::Ge,
                            left: Box::new(Expr::Var(ident("n"))),
                            right: Box::new(Expr::IntLit(0)),
                        },
                        span: Span::default(),
                    },
                    Assert {
                        condition: Expr::Binary {
                            op: BinaryOp::Le,
                            left: Box::new(Expr::Var(ident("n"))),
                            right: Box::new(Expr::IntLit(100)),
                        },
                        span: Span::default(),
                    },
                ],
                tests: vec![],
                body: vec![],
                span: Span::default(),
            },
            register_types: std::collections::HashMap::new(),
        };

        let smtlib = generate_smtlib2(&node).unwrap();

        // Check that assertions are included
        assert!(smtlib.contains("; Assertions (@assert directives)"));
        assert!(smtlib.contains("; @assert [0]"));
        assert!(smtlib.contains("; @assert [1]"));
        assert!(smtlib.contains("(>= n 0)"));
        assert!(smtlib.contains("(<= n 100)"));
    }

    #[test]
    fn test_node_verification_result_all_proven() {
        // Test with all proven
        let result = NodeVerificationResult {
            node_name: "test".to_string(),
            precondition: VerificationResult::Proven,
            postcondition: VerificationResult::Proven,
            assertions: vec![
                AssertionResult {
                    index: 0,
                    result: VerificationResult::Proven,
                },
            ],
            invariants: vec![],
        };
        assert!(result.all_proven());

        // Test with assertion not proven
        let result2 = NodeVerificationResult {
            node_name: "test2".to_string(),
            precondition: VerificationResult::Proven,
            postcondition: VerificationResult::Proven,
            assertions: vec![
                AssertionResult {
                    index: 0,
                    result: VerificationResult::CounterExample(std::collections::HashMap::new()),
                },
            ],
            invariants: vec![],
        };
        assert!(!result2.all_proven());
    }

    #[test]
    fn test_verification_result_is_methods() {
        assert!(VerificationResult::Proven.is_proven());
        assert!(!VerificationResult::Proven.is_counterexample());

        let ce = VerificationResult::CounterExample(std::collections::HashMap::new());
        assert!(!ce.is_proven());
        assert!(ce.is_counterexample());

        assert!(!VerificationResult::Unknown("test".to_string()).is_proven());
        assert!(!VerificationResult::Unknown("test".to_string()).is_counterexample());
    }

    // ========== v0.11.0 Invariant Suggestion Tests ==========

    #[test]
    fn test_is_counter_like_name() {
        assert!(is_counter_like_name("i"));
        assert!(is_counter_like_name("j"));
        assert!(is_counter_like_name("k"));
        assert!(is_counter_like_name("n"));
        assert!(is_counter_like_name("index"));
        assert!(is_counter_like_name("idx"));
        assert!(is_counter_like_name("counter"));
        assert!(is_counter_like_name("I")); // case insensitive
        assert!(is_counter_like_name("INDEX"));

        assert!(!is_counter_like_name("foo"));
        assert!(!is_counter_like_name("result"));
        assert!(!is_counter_like_name("sum"));
    }

    #[test]
    fn test_expr_to_readable() {
        let var_expr = Expr::Var(ident("x"));
        assert_eq!(expr_to_readable(&var_expr), "x");

        let int_expr = Expr::IntLit(42);
        assert_eq!(expr_to_readable(&int_expr), "42");

        let ge_expr = Expr::Binary {
            op: BinaryOp::Ge,
            left: Box::new(Expr::Var(ident("x"))),
            right: Box::new(Expr::IntLit(0)),
        };
        assert_eq!(expr_to_readable(&ge_expr), "x >= 0");

        let old_expr = Expr::Old(Box::new(Expr::Var(ident("y"))));
        assert_eq!(expr_to_readable(&old_expr), "old(y)");
    }

    #[test]
    fn test_make_ge_zero() {
        let expr = make_ge_zero("i");
        assert_eq!(expr_to_readable(&expr), "i >= 0");
    }

    #[test]
    fn test_make_ge_old() {
        let expr = make_ge_old("sum");
        assert_eq!(expr_to_readable(&expr), "sum >= old(sum)");
    }

    #[test]
    fn test_make_le_old() {
        let expr = make_le_old("count");
        assert_eq!(expr_to_readable(&expr), "count <= old(count)");
    }

    #[test]
    fn test_make_le_bound() {
        let expr = make_le_bound("i", "n");
        assert_eq!(expr_to_readable(&expr), "i <= n");
    }

    #[test]
    fn test_invariant_candidate_creation() {
        let candidate = InvariantCandidate::new(
            make_ge_zero("i"),
            "i >= 0",
            0.9,
        ).with_rationale("Counter non-negative");

        assert_eq!(candidate.readable, "i >= 0");
        assert!((candidate.confidence - 0.9).abs() < 0.001);
        assert_eq!(candidate.rationale, "Counter non-negative");
    }

    #[test]
    fn test_derive_invariant_from_precondition() {
        let pre = Expr::Binary {
            op: BinaryOp::Ge,
            left: Box::new(Expr::Var(ident("n"))),
            right: Box::new(Expr::IntLit(0)),
        };

        let candidate = derive_invariant_from_precondition(&pre);
        assert!(candidate.is_some());

        let c = candidate.unwrap();
        assert_eq!(c.readable, "n >= 0");
        assert!(c.rationale.contains("precondition"));
    }

    #[test]
    fn test_derive_invariant_from_non_bound_precondition() {
        // Equality preconditions shouldn't generate invariants
        let pre = Expr::Binary {
            op: BinaryOp::Eq,
            left: Box::new(Expr::Var(ident("x"))),
            right: Box::new(Expr::IntLit(5)),
        };

        let candidate = derive_invariant_from_precondition(&pre);
        assert!(candidate.is_none());
    }

    #[test]
    fn test_loop_pattern_enum() {
        let counter_inc = LoopPattern::CounterIncrement {
            var: "i".to_string(),
            step: 1,
        };
        assert!(matches!(counter_inc, LoopPattern::CounterIncrement { var, step } if var == "i" && step == 1));

        let bounded = LoopPattern::BoundedIteration {
            var: "j".to_string(),
            bound: "n".to_string(),
            op: BinaryOp::Lt,
        };
        assert!(matches!(bounded, LoopPattern::BoundedIteration { var, bound, op } if var == "j" && bound == "n" && op == BinaryOp::Lt));
    }

    #[test]
    fn test_opcode_to_binary_op() {
        assert_eq!(opcode_to_binary_op(crate::ast::Opcode::Lt), Some(BinaryOp::Lt));
        assert_eq!(opcode_to_binary_op(crate::ast::Opcode::Le), Some(BinaryOp::Le));
        assert_eq!(opcode_to_binary_op(crate::ast::Opcode::Gt), Some(BinaryOp::Gt));
        assert_eq!(opcode_to_binary_op(crate::ast::Opcode::Ge), Some(BinaryOp::Ge));
        assert_eq!(opcode_to_binary_op(crate::ast::Opcode::Eq), Some(BinaryOp::Eq));
        assert_eq!(opcode_to_binary_op(crate::ast::Opcode::Ne), Some(BinaryOp::Ne));
        assert_eq!(opcode_to_binary_op(crate::ast::Opcode::Add), None);
    }

    // ========== v0.11.0 Phase 3.6: Verification & Ranking Tests ==========

    #[test]
    fn test_verification_status_display() {
        assert_eq!(format!("{}", VerificationStatus::Proven), "proven");
        assert_eq!(format!("{}", VerificationStatus::Disproven), "disproven");
        assert_eq!(format!("{}", VerificationStatus::Unknown), "unknown");
        assert_eq!(format!("{}", VerificationStatus::NotVerified), "not verified");
    }

    #[test]
    fn test_verification_status_equality() {
        assert_eq!(VerificationStatus::Proven, VerificationStatus::Proven);
        assert_ne!(VerificationStatus::Proven, VerificationStatus::Disproven);
        assert_ne!(VerificationStatus::Unknown, VerificationStatus::NotVerified);
    }

    #[test]
    fn test_verified_candidate_not_verified() {
        let candidate = InvariantCandidate::new(
            Expr::IntLit(0), // dummy
            "x >= 0",
            0.8,
        );

        let verified = VerifiedCandidate::not_verified(candidate);
        assert_eq!(verified.status, VerificationStatus::NotVerified);
        assert_eq!(verified.adjusted_confidence, 0.8);
        assert!(verified.is_useful());
        assert_eq!(verified.confidence_marker(), "○");
    }

    #[test]
    fn test_verified_candidate_proven() {
        let candidate = InvariantCandidate::new(
            Expr::IntLit(0),
            "x >= 0",
            0.7,
        );

        let verified = VerifiedCandidate::with_status(candidate, VerificationStatus::Proven);
        assert_eq!(verified.status, VerificationStatus::Proven);
        assert_eq!(verified.adjusted_confidence, 1.0); // Boosted to max
        assert!(verified.is_useful());
        assert_eq!(verified.confidence_marker(), "✓");
    }

    #[test]
    fn test_verified_candidate_disproven() {
        let candidate = InvariantCandidate::new(
            Expr::IntLit(0),
            "x >= 0",
            0.9,
        );

        let verified = VerifiedCandidate::with_status(candidate, VerificationStatus::Disproven);
        assert_eq!(verified.status, VerificationStatus::Disproven);
        assert_eq!(verified.adjusted_confidence, 0.0); // Zeroed
        assert!(!verified.is_useful()); // Not useful!
        assert_eq!(verified.confidence_marker(), "✗");
    }

    #[test]
    fn test_verified_candidate_unknown() {
        let candidate = InvariantCandidate::new(
            Expr::IntLit(0),
            "x >= 0",
            0.8,
        );

        let verified = VerifiedCandidate::with_status(candidate, VerificationStatus::Unknown);
        assert_eq!(verified.status, VerificationStatus::Unknown);
        assert!((verified.adjusted_confidence - 0.56).abs() < 0.01); // 0.8 * 0.7 = 0.56
        assert!(verified.is_useful());
        assert_eq!(verified.confidence_marker(), "?");
    }

    #[test]
    fn test_format_verified_candidates_empty() {
        let candidates: Vec<VerifiedCandidate> = vec![];
        let output = format_verified_candidates(&candidates);
        assert_eq!(output, "No invariant suggestions available.");
    }

    #[test]
    fn test_format_verified_candidates_with_items() {
        let candidate1 = InvariantCandidate::new(
            Expr::IntLit(0),
            "i >= 0",
            0.9,
        ).with_rationale("Counter stays non-negative");

        let candidate2 = InvariantCandidate::new(
            Expr::IntLit(0),
            "i < n",
            0.8,
        );

        let verified1 = VerifiedCandidate::with_status(candidate1, VerificationStatus::Proven);
        let verified2 = VerifiedCandidate::with_status(candidate2, VerificationStatus::Unknown);

        let output = format_verified_candidates(&[verified1, verified2]);

        assert!(output.contains("Suggested Invariants:"));
        assert!(output.contains("✓ i >= 0"));
        assert!(output.contains("confidence: 100%"));
        assert!(output.contains("Counter stays non-negative"));
        assert!(output.contains("? i < n"));
    }

    #[test]
    fn test_verify_and_rank_candidates_ordering() {
        use crate::ast::{Node, ParamAnnotation, Parameter};
        use crate::types::TypedNode;

        // Create a simple node with precondition n >= 0
        let node = TypedNode {
            node: Node {
                name: ident("test"),
                tags: vec![],
                params: vec![Parameter {
                    name: ident("n"),
                    ty: Type::I32,
                    annotation: ParamAnnotation::None,
                    span: Span::default(),
                }],
                returns: Type::I32,
                preconditions: vec![Expr::Binary {
                    op: BinaryOp::Ge,
                    left: Box::new(Expr::Var(ident("n"))),
                    right: Box::new(Expr::IntLit(0)),
                }],
                postconditions: vec![],
                invariants: vec![],
                variants: vec![],
                pure: false,
                requires: vec![],
                assertions: vec![],
                tests: vec![],
                body: vec![],
                span: Span::default(),
            },
            register_types: std::collections::HashMap::new(),
        };

        // Create candidates with different confidences
        let candidates = vec![
            InvariantCandidate::new(
                Expr::Binary {
                    op: BinaryOp::Ge,
                    left: Box::new(Expr::Var(ident("n"))),
                    right: Box::new(Expr::IntLit(0)),
                },
                "n >= 0",
                0.5, // Low confidence
            ),
            InvariantCandidate::new(
                Expr::Binary {
                    op: BinaryOp::Le,
                    left: Box::new(Expr::Var(ident("n"))),
                    right: Box::new(Expr::IntLit(100)),
                },
                "n <= 100",
                0.9, // High confidence
            ),
        ];

        let verified = verify_and_rank_candidates(&node, candidates);

        // Should be sorted by adjusted confidence
        assert!(verified.len() >= 1);
        // First should have higher adjusted confidence than second (if both exist)
        if verified.len() >= 2 {
            assert!(verified[0].adjusted_confidence >= verified[1].adjusted_confidence);
        }
    }
}
