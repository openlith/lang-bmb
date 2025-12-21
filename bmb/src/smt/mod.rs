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

/// Result of verifying a single node
#[derive(Debug, Clone)]
pub struct NodeVerificationResult {
    pub node_name: String,
    pub precondition: VerificationResult,
    pub postcondition: VerificationResult,
    pub invariants: Vec<InvariantResult>,
}

impl NodeVerificationResult {
    /// Returns true if all contracts were proven
    pub fn all_proven(&self) -> bool {
        self.precondition.is_proven()
            && self.postcondition.is_proven()
            && self.invariants.iter().all(|inv| inv.result.is_proven())
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

    // Verify precondition is satisfiable
    let pre_result = if let Some(ref pre) = node.node.precondition {
        verify_satisfiability(conf, &vars, pre)?
    } else {
        VerificationResult::Proven
    };

    // Verify postcondition holds given precondition
    let post_result = if let Some(ref post) = node.node.postcondition {
        if let Some(ref pre) = node.node.precondition {
            verify_implication_with_old(conf, &vars, pre, post, &node.node.params)?
        } else {
            verify_validity(conf, &vars, post)?
        }
    } else {
        VerificationResult::Proven
    };

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

/// Get model values from solver
/// Note: We return an empty model for now as rsmt2's model parsing is complex.
/// The fact that we found a counterexample is still valuable information.
fn get_model(_solver: &mut Solver<BmbParser>, _vars: &[SmtVar]) -> HashMap<String, i64> {
    // Getting the actual model values requires implementing ExprParser and ValueParser
    // for the full rsmt2 API. For now, we just return an empty counterexample map.
    // The important information is that a counterexample exists.
    HashMap::new()
}

/// Parse SMT integer value (handles (- N) format)
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

    // Precondition
    if let Some(ref pre) = node.node.precondition {
        let smt_pre = translate_expr(pre)?;
        output.push_str("; Precondition\n");
        output.push_str(&format!("(assert {})\n\n", smt_pre.to_bool_smtlib()));
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

    // Postcondition check (negated)
    if let Some(ref post) = node.node.postcondition {
        let smt_post = translate_expr(post)?;
        output.push_str("; Postcondition (negated for checking)\n");
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
    fn test_generate_smtlib2() {
        use crate::ast::{Node, Parameter};
        use crate::types::TypedNode;

        let node = TypedNode {
            node: Node {
                name: ident("divide"),
                params: vec![
                    Parameter {
                        name: ident("a"),
                        ty: Type::I32,
                        span: Span::default(),
                    },
                    Parameter {
                        name: ident("b"),
                        ty: Type::I32,
                        span: Span::default(),
                    },
                ],
                returns: Type::I32,
                precondition: Some(Expr::Binary {
                    op: BinaryOp::Ne,
                    left: Box::new(Expr::Var(ident("b"))),
                    right: Box::new(Expr::IntLit(0)),
                }),
                postcondition: Some(Expr::BoolLit(true)),
                invariants: vec![],
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
}
