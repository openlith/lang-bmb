//! BMB Linter
//!
//! Static analysis and style checking for BMB programs.
//!
//! "Omission is guessing, and guessing is error."
//! - The linter helps catch potential issues before runtime.

use crate::ast::*;
use std::collections::HashSet;

/// Lint warning severity
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Warning,
    Style,
    Info,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Severity::Warning => write!(f, "warning"),
            Severity::Style => write!(f, "style"),
            Severity::Info => write!(f, "info"),
        }
    }
}

/// A lint warning
#[derive(Debug, Clone)]
pub struct LintWarning {
    pub severity: Severity,
    pub code: &'static str,
    pub message: String,
    pub line: Option<usize>,
    pub suggestion: Option<String>,
}

impl std::fmt::Display for LintWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.severity)?;
        if let Some(line) = self.line {
            write!(f, " at line {}", line)?;
        }
        write!(f, ": [{}] {}", self.code, self.message)?;
        if let Some(ref suggestion) = self.suggestion {
            write!(f, "\n  help: {}", suggestion)?;
        }
        Ok(())
    }
}

/// Lint a BMB program and return warnings
pub fn lint(program: &Program) -> Vec<LintWarning> {
    let mut warnings = Vec::new();

    for node in &program.nodes {
        lint_node(node, &mut warnings);
    }

    warnings
}

fn lint_node(node: &Node, warnings: &mut Vec<LintWarning>) {
    // Check for missing contracts
    if node.precondition.is_none() && node.postcondition.is_none() {
        warnings.push(LintWarning {
            severity: Severity::Style,
            code: "S001",
            message: format!("function '{}' has no contracts", node.name.name),
            line: Some(node.span.line),
            suggestion: Some("consider adding @pre and @post contracts for safety".to_string()),
        });
    }

    // Check for trivial contracts
    if let Some(ref pre) = node.precondition {
        if is_trivial_contract(pre) {
            warnings.push(LintWarning {
                severity: Severity::Info,
                code: "I001",
                message: format!(
                    "function '{}' has trivial precondition 'true'",
                    node.name.name
                ),
                line: Some(node.span.line),
                suggestion: Some("consider specifying actual preconditions".to_string()),
            });
        }
    }

    if let Some(ref post) = node.postcondition {
        if is_trivial_contract(post) {
            warnings.push(LintWarning {
                severity: Severity::Info,
                code: "I002",
                message: format!(
                    "function '{}' has trivial postcondition 'true'",
                    node.name.name
                ),
                line: Some(node.span.line),
                suggestion: Some("consider specifying actual postconditions".to_string()),
            });
        }
    }

    // Check for unused parameters
    let used_vars = collect_used_variables(node);
    for param in &node.params {
        if !used_vars.contains(&param.name.name) {
            warnings.push(LintWarning {
                severity: Severity::Warning,
                code: "W001",
                message: format!(
                    "parameter '{}' is never used in function '{}'",
                    param.name.name, node.name.name
                ),
                line: Some(node.span.line),
                suggestion: Some(format!(
                    "prefix with underscore to indicate intentionally unused: _{}",
                    param.name.name
                )),
            });
        }
    }

    // Check for function naming convention (snake_case)
    if !is_snake_case(&node.name.name) {
        warnings.push(LintWarning {
            severity: Severity::Style,
            code: "S002",
            message: format!("function name '{}' should use snake_case", node.name.name),
            line: Some(node.span.line),
            suggestion: Some(format!(
                "consider renaming to '{}'",
                to_snake_case(&node.name.name)
            )),
        });
    }

    // Check for empty body
    if node.body.is_empty() {
        warnings.push(LintWarning {
            severity: Severity::Warning,
            code: "W002",
            message: format!("function '{}' has empty body", node.name.name),
            line: Some(node.span.line),
            suggestion: None,
        });
    }

    // Check for division without zero-check precondition
    for instr in &node.body {
        if let Instruction::Statement(stmt) = instr {
            if stmt.opcode == Opcode::Div {
                if let Some(divisor) = stmt.operands.get(2) {
                    if let Operand::Identifier(name) = divisor {
                        if !has_nonzero_precondition(node, &name.name) {
                            warnings.push(LintWarning {
                                severity: Severity::Warning,
                                code: "W003",
                                message: format!(
                                    "division by '{}' without precondition check",
                                    name.name
                                ),
                                line: Some(stmt.span.line),
                                suggestion: Some(format!(
                                    "add '@pre {} != 0' to prevent division by zero",
                                    name.name
                                )),
                            });
                        }
                    }
                }
            }
        }
    }
}

fn is_trivial_contract(expr: &Expr) -> bool {
    matches!(expr, Expr::BoolLit(true))
}

fn collect_used_variables(node: &Node) -> HashSet<String> {
    let mut used = HashSet::new();

    // Check contracts
    if let Some(ref pre) = node.precondition {
        collect_vars_in_expr(pre, &mut used);
    }
    if let Some(ref post) = node.postcondition {
        collect_vars_in_expr(post, &mut used);
    }

    // Check body
    for instr in &node.body {
        if let Instruction::Statement(stmt) = instr {
            for operand in &stmt.operands {
                if let Operand::Identifier(name) = operand {
                    used.insert(name.name.clone());
                }
            }
        }
    }

    used
}

fn collect_vars_in_expr(expr: &Expr, vars: &mut HashSet<String>) {
    match expr {
        Expr::Var(id) => {
            vars.insert(id.name.clone());
        }
        Expr::Binary { left, right, .. } => {
            collect_vars_in_expr(left, vars);
            collect_vars_in_expr(right, vars);
        }
        Expr::Unary { operand, .. } => {
            collect_vars_in_expr(operand, vars);
        }
        _ => {}
    }
}

fn is_snake_case(name: &str) -> bool {
    // Allow names starting with underscore (for unused params)
    let name = name.strip_prefix('_').unwrap_or(name);

    // Must be lowercase with optional underscores, no consecutive underscores
    name.chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
        && !name.contains("__")
        && !name.ends_with('_')
}

fn to_snake_case(name: &str) -> String {
    let mut result = String::new();
    for (i, c) in name.chars().enumerate() {
        if c.is_ascii_uppercase() {
            if i > 0 {
                result.push('_');
            }
            result.push(c.to_ascii_lowercase());
        } else {
            result.push(c);
        }
    }
    result
}

fn has_nonzero_precondition(node: &Node, var_name: &str) -> bool {
    if let Some(ref pre) = node.precondition {
        return check_nonzero_condition(pre, var_name);
    }
    false
}

fn check_nonzero_condition(expr: &Expr, var_name: &str) -> bool {
    match expr {
        Expr::Binary { op, left, right } => {
            // Check for x != 0
            if *op == BinaryOp::Ne {
                let is_var_check = match (left.as_ref(), right.as_ref()) {
                    (Expr::Var(id), Expr::IntLit(0)) if id.name == var_name => true,
                    (Expr::IntLit(0), Expr::Var(id)) if id.name == var_name => true,
                    (Expr::Var(id), Expr::FloatLit(v)) if id.name == var_name && *v == 0.0 => true,
                    (Expr::FloatLit(v), Expr::Var(id)) if id.name == var_name && *v == 0.0 => true,
                    _ => false,
                };
                if is_var_check {
                    return true;
                }
            }

            // Check for x > 0 or x >= 1
            if *op == BinaryOp::Gt || *op == BinaryOp::Ge {
                if let (Expr::Var(id), Expr::IntLit(v)) = (left.as_ref(), right.as_ref()) {
                    if id.name == var_name {
                        if (*op == BinaryOp::Gt && *v >= 0) || (*op == BinaryOp::Ge && *v >= 1) {
                            return true;
                        }
                    }
                }
            }

            // Check for compound conditions (&&)
            if *op == BinaryOp::And {
                return check_nonzero_condition(left, var_name)
                    || check_nonzero_condition(right, var_name);
            }

            false
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    #[test]
    fn test_lint_missing_contracts() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32

  add %r a b
  ret %r
"#;

        let ast = parser::parse(source).unwrap();
        let warnings = lint(&ast);

        assert!(warnings.iter().any(|w| w.code == "S001"));
    }

    #[test]
    fn test_lint_trivial_precondition() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32
@pre true

  add %r a b
  ret %r
"#;

        let ast = parser::parse(source).unwrap();
        let warnings = lint(&ast);

        assert!(warnings.iter().any(|w| w.code == "I001"));
    }

    #[test]
    fn test_lint_unused_param() {
        let source = r#"
@node identity
@params x:i32 unused:i32
@returns i32

  mov %r x
  ret %r
"#;

        let ast = parser::parse(source).unwrap();
        let warnings = lint(&ast);

        assert!(warnings
            .iter()
            .any(|w| w.code == "W001" && w.message.contains("unused")));
    }

    #[test]
    fn test_lint_division_no_check() {
        let source = r#"
@node divide
@params a:i32 b:i32
@returns i32
@pre true

  div %r a b
  ret %r
"#;

        let ast = parser::parse(source).unwrap();
        let warnings = lint(&ast);

        assert!(warnings.iter().any(|w| w.code == "W003"));
    }

    #[test]
    fn test_lint_division_with_check() {
        let source = r#"
@node divide
@params a:i32 b:i32
@returns i32
@pre b != 0

  div %r a b
  ret %r
"#;

        let ast = parser::parse(source).unwrap();
        let warnings = lint(&ast);

        // Should NOT have W003 warning
        assert!(!warnings.iter().any(|w| w.code == "W003"));
    }

    #[test]
    fn test_snake_case() {
        assert!(is_snake_case("sum"));
        assert!(is_snake_case("get_value"));
        assert!(is_snake_case("_unused"));
        assert!(!is_snake_case("getValue"));
        assert!(!is_snake_case("GetValue"));
    }
}
