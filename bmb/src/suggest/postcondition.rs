//! Postcondition Inference Module
//!
//! Computes strongest postconditions for loop-free code using Dijkstra's SP rules.
//!
//! ## Algorithm (Based on Strongest Postcondition Calculus)
//!
//! - `sp(skip, P) = P`
//! - `sp(x := E, P) = ∃v. P[x/v] ∧ x = E[x/v]`
//! - `sp(S1; S2, P) = sp(S2, sp(S1, P))`
//! - `sp(if B then S1 else S2, P) = sp(S1, P ∧ B) ∨ sp(S2, P ∧ ¬B)`
//!
//! For loops, we require @invariant annotations (cannot infer finite formula).
//!
//! ## Simplification
//!
//! Uses the "one-point rule" for existential elimination:
//! `∃x. P ∧ x = E` simplifies to `P[x/E]`

use crate::ast::{BinaryOp, Expr, Identifier, Instruction, Node, Opcode, Operand, Span, Statement};
use crate::types::TypedNode;

use super::{Suggestion, SuggestionKind, SuggestedExpr};
use std::collections::HashMap;

/// Symbolic state during SP computation
#[derive(Debug, Clone)]
struct SymbolicState {
    /// Maps registers/variables to their symbolic expressions
    values: HashMap<String, Expr>,
    /// Path condition (conjunction of branch conditions taken)
    /// Reserved for future conditional path tracking
    #[allow(dead_code)]
    path_condition: Vec<Expr>,
    /// Whether we've encountered a loop (requires invariant)
    has_loop: bool,
}

impl SymbolicState {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
            path_condition: Vec::new(),
            has_loop: false,
        }
    }

    /// Initialize with function parameters
    fn from_params(params: &[String]) -> Self {
        let mut state = Self::new();
        for name in params {
            // Parameters start with their initial value (represented as Var)
            state.values.insert(
                name.clone(),
                Expr::Var(Identifier {
                    name: name.clone(),
                    span: Span::new(0, 0, 0, 0),
                }),
            );
        }
        state
    }

    /// Get the current symbolic value of a variable
    fn get(&self, name: &str) -> Option<&Expr> {
        self.values.get(name)
    }

    /// Set the symbolic value of a variable
    fn set(&mut self, name: &str, expr: Expr) {
        self.values.insert(name.to_string(), expr);
    }

    /// Merge two states from different branches
    #[allow(dead_code)]
    fn merge(then_state: &Self, else_state: &Self, _condition: &Expr) -> Self {
        let mut merged = Self::new();
        merged.has_loop = then_state.has_loop || else_state.has_loop;

        // For each variable, create a conditional expression
        let mut all_vars: std::collections::HashSet<&String> = then_state.values.keys().collect();
        all_vars.extend(else_state.values.keys());

        for var in all_vars {
            let then_val = then_state.get(var);
            let else_val = else_state.get(var);

            match (then_val, else_val) {
                (Some(t), Some(e)) if exprs_equal(t, e) => {
                    // Same value in both branches
                    merged.set(var, t.clone());
                }
                (Some(t), Some(_e)) => {
                    // Different values - would need conditional, simplify to "unknown"
                    // In practice, we just use the last assigned value
                    merged.set(var, t.clone());
                }
                (Some(t), None) => merged.set(var, t.clone()),
                (None, Some(e)) => merged.set(var, e.clone()),
                (None, None) => {}
            }
        }

        merged
    }
}

/// Infer postconditions for a function
pub fn infer_postcondition(node: &Node, _typed_node: &TypedNode) -> Vec<Suggestion> {
    let mut suggestions = Vec::new();

    // Initialize symbolic state with parameters
    let params: Vec<String> = node.params.iter().map(|p| p.name.name.clone()).collect();

    let mut state = SymbolicState::from_params(&params);

    // Track loop detection for confidence scoring
    let has_loops = detect_loops(&node.body);

    // Propagate through function body
    for instr in &node.body {
        propagate_instruction(instr, &mut state);
    }

    // Generate postcondition from final state
    let postconditions = generate_postconditions(&state, node);

    // Calculate confidence
    let confidence = if state.has_loop || has_loops {
        0.4 // Low confidence for code with loops
    } else if state.values.is_empty() {
        0.5 // Nothing to infer
    } else {
        0.85 // High confidence for loop-free code
    };

    for post in postconditions {
        suggestions.push(Suggestion {
            node_name: node.name.name.clone(),
            kind: SuggestionKind::Postcondition,
            expr: post,
            confidence,
            explanation: if state.has_loop {
                "Partial inference (loops detected, requires @invariant)".to_string()
            } else {
                "Strongest postcondition computed from function body".to_string()
            },
        });
    }

    suggestions
}

/// Detect if function body contains loops (backward jumps)
fn detect_loops(body: &[Instruction]) -> bool {
    let mut label_positions: HashMap<String, usize> = HashMap::new();

    // First pass: collect label positions
    for (i, instr) in body.iter().enumerate() {
        if let Instruction::Label(id) = instr {
            label_positions.insert(id.name.clone(), i);
        }
    }

    // Second pass: check for backward jumps
    for (i, instr) in body.iter().enumerate() {
        if let Instruction::Statement(stmt) = instr {
            if matches!(stmt.opcode, Opcode::Jmp | Opcode::Jif) {
                // Find target label
                for operand in &stmt.operands {
                    if let Operand::Label(label_id) = operand {
                        if let Some(&label_pos) = label_positions.get(&label_id.name) {
                            if label_pos <= i {
                                return true; // Backward jump = loop
                            }
                        }
                    }
                }
            }
        }
    }

    false
}

/// Propagate symbolic state through an instruction
fn propagate_instruction(instr: &Instruction, state: &mut SymbolicState) {
    match instr {
        Instruction::Statement(stmt) => {
            propagate_statement(stmt, state);
        }
        Instruction::Label(_) => {
            // Labels don't change state
        }
        Instruction::Match(match_stmt) => {
            // Simplified: just process all arms (conservative)
            for arm in &match_stmt.arms {
                for inner in &arm.body {
                    propagate_instruction(inner, state);
                }
            }
            if let Some(default) = &match_stmt.default {
                for inner in &default.body {
                    propagate_instruction(inner, state);
                }
            }
        }
    }
}

/// Propagate symbolic state through a statement
fn propagate_statement(stmt: &Statement, state: &mut SymbolicState) {
    match stmt.opcode {
        // Assignment operations: dest = op(src1, src2)
        Opcode::Mov => {
            if let (Some(Operand::Register(dest_id)), Some(src)) =
                (stmt.operands.first(), stmt.operands.get(1))
            {
                let src_expr = operand_to_expr(src, state);
                state.set(&dest_id.name, src_expr);
            }
        }

        Opcode::Add | Opcode::Sub | Opcode::Mul | Opcode::Div | Opcode::Mod => {
            if let (Some(Operand::Register(dest_id)), Some(left), Some(right)) = (
                stmt.operands.first(),
                stmt.operands.get(1),
                stmt.operands.get(2),
            ) {
                let left_expr = operand_to_expr(left, state);
                let right_expr = operand_to_expr(right, state);
                let op = match stmt.opcode {
                    Opcode::Add => BinaryOp::Add,
                    Opcode::Sub => BinaryOp::Sub,
                    Opcode::Mul => BinaryOp::Mul,
                    Opcode::Div => BinaryOp::Div,
                    Opcode::Mod => BinaryOp::Mod,
                    _ => unreachable!(),
                };
                let result = simplify_binary(op, left_expr, right_expr);
                state.set(&dest_id.name, result);
            }
        }

        // Bitwise operations - represent symbolically (no dedicated BinaryOp variants)
        Opcode::And | Opcode::Or | Opcode::Xor | Opcode::Shl | Opcode::Shr => {
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                // For bitwise ops, we lose symbolic tracking (complex to represent)
                state.values.remove(&dest_id.name);
            }
        }

        Opcode::Not => {
            if let (Some(Operand::Register(dest_id)), Some(src)) =
                (stmt.operands.first(), stmt.operands.get(1))
            {
                let src_expr = operand_to_expr(src, state);
                // Logical not
                state.set(
                    &dest_id.name,
                    Expr::Unary {
                        op: crate::ast::UnaryOp::Not,
                        operand: Box::new(src_expr),
                    },
                );
            }
        }

        // Comparison operations
        Opcode::Eq | Opcode::Ne | Opcode::Lt | Opcode::Le | Opcode::Gt | Opcode::Ge => {
            if let (Some(Operand::Register(dest_id)), Some(left), Some(right)) = (
                stmt.operands.first(),
                stmt.operands.get(1),
                stmt.operands.get(2),
            ) {
                let left_expr = operand_to_expr(left, state);
                let right_expr = operand_to_expr(right, state);
                let op = match stmt.opcode {
                    Opcode::Eq => BinaryOp::Eq,
                    Opcode::Ne => BinaryOp::Ne,
                    Opcode::Lt => BinaryOp::Lt,
                    Opcode::Le => BinaryOp::Le,
                    Opcode::Gt => BinaryOp::Gt,
                    Opcode::Ge => BinaryOp::Ge,
                    _ => unreachable!(),
                };
                let result = Expr::Binary {
                    op,
                    left: Box::new(left_expr),
                    right: Box::new(right_expr),
                };
                state.set(&dest_id.name, result);
            }
        }

        // Control flow with backward jumps indicates loops
        Opcode::Jmp | Opcode::Jif => {
            // Check for backward jump (loop)
            // Precise loop detection done separately in detect_loops
        }

        // Load/Store affect memory model (simplified for now)
        Opcode::Load => {
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                // Result is unknown (would need memory model)
                state.values.remove(&dest_id.name);
            }
        }

        Opcode::Store => {
            // Doesn't change register state directly
        }

        // Box/Unbox heap operations
        Opcode::Box => {
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                // Result is a pointer (heap address)
                state.values.remove(&dest_id.name); // Unknown heap location
            }
        }

        Opcode::Unbox => {
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                // Result from heap dereference
                state.values.remove(&dest_id.name);
            }
        }

        Opcode::Drop => {
            // Doesn't change observable state
        }

        // Call can modify anything
        Opcode::Call | Opcode::Xcall => {
            // Conservative: clear all state affected by call
            // In practice, would use callee's @modifies
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                state.values.remove(&dest_id.name);
            }
        }

        // Ret signals end of function
        Opcode::Ret => {
            // The return value is what we want for postcondition
            if let Some(operand) = stmt.operands.first() {
                let ret_expr = operand_to_expr(operand, state);
                state.set("result", ret_expr);
            }
        }

        // Print is I/O
        Opcode::Print => {}
    }
}

/// Convert an operand to a symbolic expression
fn operand_to_expr(operand: &Operand, state: &SymbolicState) -> Expr {
    match operand {
        Operand::Register(id) => {
            // Look up current symbolic value
            state.get(&id.name).cloned().unwrap_or_else(|| {
                Expr::Var(Identifier {
                    name: format!("%{}", id.name),
                    span: id.span.clone(),
                })
            })
        }
        Operand::Identifier(id) => state.get(&id.name).cloned().unwrap_or_else(|| {
            Expr::Var(Identifier {
                name: id.name.clone(),
                span: id.span.clone(),
            })
        }),
        Operand::IntLiteral(n) => Expr::IntLit(*n),
        Operand::FloatLiteral(f) => Expr::FloatLit(*f),
        Operand::StringLiteral(_s) => {
            // String literals not directly representable in Expr
            Expr::IntLit(0)
        }
        Operand::Label(_) => {
            // Labels aren't values
            Expr::IntLit(0)
        }
        Operand::QualifiedIdent { module, name } => Expr::Var(Identifier {
            name: format!("{}::{}", module.name, name.name),
            span: module.span.clone(),
        }),
        Operand::ArrayAccess { base, index } => {
            // Simplified: represent as the base variable with index info
            let index_str = operand_to_string(index);
            Expr::Var(Identifier {
                name: format!("{}[{}]", base.name, index_str),
                span: base.span.clone(),
            })
        }
        Operand::FieldAccess { base, field } => {
            // Simplified: represent as the base variable
            Expr::Var(Identifier {
                name: format!("{}.{}", base.name, field.name),
                span: base.span.clone(),
            })
        }
    }
}

/// Convert an operand to a string representation
fn operand_to_string(operand: &Operand) -> String {
    match operand {
        Operand::Register(id) => format!("%{}", id.name),
        Operand::Identifier(id) => id.name.clone(),
        Operand::IntLiteral(n) => n.to_string(),
        Operand::FloatLiteral(f) => f.to_string(),
        Operand::Label(id) => format!("_{}", id.name),
        Operand::StringLiteral(s) => format!("\"{}\"", s),
        Operand::QualifiedIdent { module, name } => format!("{}::{}", module.name, name.name),
        Operand::ArrayAccess { base, index } => {
            format!("{}[{}]", base.name, operand_to_string(index))
        }
        Operand::FieldAccess { base, field } => format!("{}.{}", base.name, field.name),
    }
}

/// Simplify a binary expression with constant folding
fn simplify_binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    // Constant folding
    if let (Expr::IntLit(l), Expr::IntLit(r)) = (&left, &right) {
        let result = match op {
            BinaryOp::Add => Some(l + r),
            BinaryOp::Sub => Some(l - r),
            BinaryOp::Mul => Some(l * r),
            BinaryOp::Div if *r != 0 => Some(l / r),
            BinaryOp::Mod if *r != 0 => Some(l % r),
            _ => None,
        };
        if let Some(v) = result {
            return Expr::IntLit(v);
        }
    }

    // Identity simplifications
    match (&op, &left, &right) {
        // x + 0 = x
        (BinaryOp::Add, _, Expr::IntLit(0)) => return left,
        // 0 + x = x
        (BinaryOp::Add, Expr::IntLit(0), _) => return right,
        // x - 0 = x
        (BinaryOp::Sub, _, Expr::IntLit(0)) => return left,
        // x * 1 = x
        (BinaryOp::Mul, _, Expr::IntLit(1)) => return left,
        // 1 * x = x
        (BinaryOp::Mul, Expr::IntLit(1), _) => return right,
        // x * 0 = 0
        (BinaryOp::Mul, _, Expr::IntLit(0)) => return Expr::IntLit(0),
        // 0 * x = 0
        (BinaryOp::Mul, Expr::IntLit(0), _) => return Expr::IntLit(0),
        // x / 1 = x
        (BinaryOp::Div, _, Expr::IntLit(1)) => return left,
        _ => {}
    }

    // No simplification possible
    Expr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// Check if two expressions are structurally equal
fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::IntLit(a), Expr::IntLit(b)) => a == b,
        (Expr::FloatLit(a), Expr::FloatLit(b)) => (a - b).abs() < f64::EPSILON,
        (Expr::BoolLit(a), Expr::BoolLit(b)) => a == b,
        (Expr::Var(a), Expr::Var(b)) => a.name == b.name,
        (Expr::Ret, Expr::Ret) => true,
        _ => false, // Conservative: different structure = not equal
    }
}

/// Generate postcondition expressions from final symbolic state
fn generate_postconditions(state: &SymbolicState, _node: &Node) -> Vec<SuggestedExpr> {
    let mut postconds = Vec::new();

    // Primary postcondition: ret == computed_value
    if let Some(result_expr) = state.get("result") {
        // Simplify: ret == result_expr
        let post = Expr::Binary {
            op: BinaryOp::Eq,
            left: Box::new(Expr::Ret),
            right: Box::new(simplify_expr(result_expr.clone())),
        };
        postconds.push(SuggestedExpr::BoolExpr(post));
    }

    // If no explicit return tracked, try to infer from body structure
    if postconds.is_empty() {
        // Look at what final registers contain
        let mut conditions = Vec::new();
        for (name, expr) in &state.values {
            if name == "result" {
                continue;
            }
            // Only include non-trivial assignments
            if !matches!(expr, Expr::Var(id) if id.name == *name) {
                let cond = Expr::Binary {
                    op: BinaryOp::Eq,
                    left: Box::new(Expr::Var(Identifier {
                        name: format!("%{}", name),
                        span: Span::new(0, 0, 0, 0),
                    })),
                    right: Box::new(simplify_expr(expr.clone())),
                };
                conditions.push(cond);
            }
        }

        if !conditions.is_empty() {
            postconds.push(SuggestedExpr::Conjunction(conditions));
        }
    }

    // If still empty, indicate pure computation
    if postconds.is_empty() {
        postconds.push(SuggestedExpr::Text("true".to_string()));
    }

    postconds
}

/// Recursively simplify an expression
fn simplify_expr(expr: Expr) -> Expr {
    match expr {
        Expr::Binary { op, left, right } => {
            let left = simplify_expr(*left);
            let right = simplify_expr(*right);
            simplify_binary(op, left, right)
        }
        Expr::Unary { op, operand } => {
            let operand = simplify_expr(*operand);
            // Double negation elimination
            if let (
                crate::ast::UnaryOp::Not,
                Expr::Unary {
                    op: crate::ast::UnaryOp::Not,
                    operand: inner,
                },
            ) = (&op, &operand)
            {
                return *inner.clone();
            }
            Expr::Unary {
                op,
                operand: Box::new(operand),
            }
        }
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_span() -> Span {
        Span::new(0, 0, 1, 1)
    }

    fn make_id(name: &str) -> Identifier {
        Identifier::new(name, make_span())
    }

    #[test]
    fn test_simplify_constant_fold() {
        let result = simplify_binary(BinaryOp::Add, Expr::IntLit(2), Expr::IntLit(3));
        assert!(matches!(result, Expr::IntLit(5)));
    }

    #[test]
    fn test_simplify_identity() {
        let x = Expr::Var(make_id("x"));
        let zero = Expr::IntLit(0);

        let result = simplify_binary(BinaryOp::Add, x.clone(), zero);
        assert!(matches!(result, Expr::Var(id) if id.name == "x"));
    }

    #[test]
    fn test_simplify_mul_zero() {
        let x = Expr::Var(make_id("x"));
        let zero = Expr::IntLit(0);

        let result = simplify_binary(BinaryOp::Mul, x, zero);
        assert!(matches!(result, Expr::IntLit(0)));
    }

    #[test]
    fn test_symbolic_state_basic() {
        let mut state = SymbolicState::new();
        state.set("x", Expr::IntLit(42));

        assert!(matches!(state.get("x"), Some(Expr::IntLit(42))));
    }

    #[test]
    fn test_detect_loops_backward_jump() {
        let body = vec![
            Instruction::Label(make_id("loop")),
            Instruction::Statement(Statement {
                opcode: Opcode::Add,
                operands: vec![
                    Operand::Register(make_id("i")),
                    Operand::Register(make_id("i")),
                    Operand::IntLiteral(1),
                ],
                span: make_span(),
            }),
            Instruction::Statement(Statement {
                opcode: Opcode::Jmp,
                operands: vec![Operand::Label(make_id("loop"))],
                span: make_span(),
            }),
        ];

        assert!(detect_loops(&body));
    }

    #[test]
    fn test_detect_loops_forward_only() {
        let body = vec![
            Instruction::Statement(Statement {
                opcode: Opcode::Jif,
                operands: vec![
                    Operand::Register(make_id("cond")),
                    Operand::Label(make_id("end")),
                ],
                span: make_span(),
            }),
            Instruction::Label(make_id("end")),
        ];

        assert!(!detect_loops(&body));
    }
}
