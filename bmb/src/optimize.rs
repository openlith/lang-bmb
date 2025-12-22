//! BMB Optimizer
//!
//! Optimization passes for BMB programs.
//!
//! "Omission is guessing, and guessing is error."
//! - Optimizations should preserve program semantics while improving performance.

use crate::ast::*;
use crate::contracts::VerifiedProgram;
use crate::types::TypedProgram;

/// Optimization level
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OptLevel {
    /// No optimizations
    None,
    /// Basic optimizations (constant folding, dead code elimination)
    Basic,
    /// Aggressive optimizations
    Aggressive,
}

impl Default for OptLevel {
    fn default() -> Self {
        OptLevel::Basic
    }
}

/// Optimize a verified BMB program
pub fn optimize(program: &mut VerifiedProgram, level: OptLevel) {
    if level == OptLevel::None {
        return;
    }

    optimize_typed_program(&mut program.program, level);
}

/// Optimize a typed program
fn optimize_typed_program(program: &mut TypedProgram, level: OptLevel) {
    for node in &mut program.nodes {
        optimize_typed_node(node, level);
    }
}

/// Optimize a typed node
fn optimize_typed_node(node: &mut crate::types::TypedNode, level: OptLevel) {
    // Optimize contracts in the original node (multiple allowed)
    for pre in &mut node.node.preconditions {
        *pre = optimize_expr(pre.clone(), level);
    }
    for post in &mut node.node.postconditions {
        *post = optimize_expr(post.clone(), level);
    }

    // Optimize body
    let mut optimized_body = Vec::new();
    for instr in &node.node.body {
        if let Some(opt_instr) = optimize_instruction(instr.clone(), level) {
            optimized_body.push(opt_instr);
        }
    }
    node.node.body = optimized_body;

    // Dead code elimination after unconditional jump
    if level >= OptLevel::Basic {
        eliminate_dead_code(&mut node.node.body);
    }
}

/// Optimize an expression (constant folding)
fn optimize_expr(expr: Expr, level: OptLevel) -> Expr {
    if level == OptLevel::None {
        return expr;
    }

    match expr {
        Expr::Binary { op, left, right } => {
            let left = optimize_expr(*left, level);
            let right = optimize_expr(*right, level);

            // Constant folding for integer operations
            if let (Expr::IntLit(l), Expr::IntLit(r)) = (&left, &right) {
                if let Some(result) = fold_int_binary(&op, *l, *r) {
                    return result;
                }
            }

            // Constant folding for float operations
            if let (Expr::FloatLit(l), Expr::FloatLit(r)) = (&left, &right) {
                if let Some(result) = fold_float_binary(&op, *l, *r) {
                    return result;
                }
            }

            // Constant folding for boolean operations
            if let (Expr::BoolLit(l), Expr::BoolLit(r)) = (&left, &right) {
                if let Some(result) = fold_bool_binary(&op, *l, *r) {
                    return result;
                }
            }

            // Algebraic simplifications
            if let Some(simplified) = simplify_binary(&op, &left, &right) {
                return simplified;
            }

            Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }
        }
        Expr::Unary { op, operand } => {
            let operand = optimize_expr(*operand, level);

            // Constant folding for unary operations
            match (&op, &operand) {
                (UnaryOp::Neg, Expr::IntLit(v)) => Expr::IntLit(-v),
                (UnaryOp::Neg, Expr::FloatLit(v)) => Expr::FloatLit(-v),
                (UnaryOp::Not, Expr::BoolLit(b)) => Expr::BoolLit(!b),
                // Double negation elimination
                (
                    UnaryOp::Neg,
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        operand: inner,
                    },
                ) => *inner.clone(),
                (
                    UnaryOp::Not,
                    Expr::Unary {
                        op: UnaryOp::Not,
                        operand: inner,
                    },
                ) => *inner.clone(),
                _ => Expr::Unary {
                    op,
                    operand: Box::new(operand),
                },
            }
        }
        _ => expr,
    }
}

/// Fold integer binary operations
fn fold_int_binary(op: &BinaryOp, l: i64, r: i64) -> Option<Expr> {
    Some(match op {
        BinaryOp::Add => Expr::IntLit(l.wrapping_add(r)),
        BinaryOp::Sub => Expr::IntLit(l.wrapping_sub(r)),
        BinaryOp::Mul => Expr::IntLit(l.wrapping_mul(r)),
        BinaryOp::Div if r != 0 => Expr::IntLit(l / r),
        BinaryOp::Mod if r != 0 => Expr::IntLit(l % r),
        BinaryOp::Eq => Expr::BoolLit(l == r),
        BinaryOp::Ne => Expr::BoolLit(l != r),
        BinaryOp::Lt => Expr::BoolLit(l < r),
        BinaryOp::Le => Expr::BoolLit(l <= r),
        BinaryOp::Gt => Expr::BoolLit(l > r),
        BinaryOp::Ge => Expr::BoolLit(l >= r),
        _ => return None,
    })
}

/// Fold float binary operations
fn fold_float_binary(op: &BinaryOp, l: f64, r: f64) -> Option<Expr> {
    Some(match op {
        BinaryOp::Add => Expr::FloatLit(l + r),
        BinaryOp::Sub => Expr::FloatLit(l - r),
        BinaryOp::Mul => Expr::FloatLit(l * r),
        BinaryOp::Div if r != 0.0 => Expr::FloatLit(l / r),
        BinaryOp::Eq => Expr::BoolLit((l - r).abs() < f64::EPSILON),
        BinaryOp::Ne => Expr::BoolLit((l - r).abs() >= f64::EPSILON),
        BinaryOp::Lt => Expr::BoolLit(l < r),
        BinaryOp::Le => Expr::BoolLit(l <= r),
        BinaryOp::Gt => Expr::BoolLit(l > r),
        BinaryOp::Ge => Expr::BoolLit(l >= r),
        _ => return None,
    })
}

/// Fold boolean binary operations
fn fold_bool_binary(op: &BinaryOp, l: bool, r: bool) -> Option<Expr> {
    Some(match op {
        BinaryOp::And => Expr::BoolLit(l && r),
        BinaryOp::Or => Expr::BoolLit(l || r),
        BinaryOp::Eq => Expr::BoolLit(l == r),
        BinaryOp::Ne => Expr::BoolLit(l != r),
        _ => return None,
    })
}

/// Algebraic simplifications
fn simplify_binary(op: &BinaryOp, left: &Expr, right: &Expr) -> Option<Expr> {
    match op {
        // x + 0 = x, 0 + x = x
        BinaryOp::Add => match (left, right) {
            (Expr::IntLit(0), other) | (other, Expr::IntLit(0)) => Some(other.clone()),
            (Expr::FloatLit(v), other) | (other, Expr::FloatLit(v)) if *v == 0.0 => {
                Some(other.clone())
            }
            _ => None,
        },
        // x - 0 = x
        BinaryOp::Sub => match right {
            Expr::IntLit(0) => Some(left.clone()),
            Expr::FloatLit(v) if *v == 0.0 => Some(left.clone()),
            _ => None,
        },
        // x * 1 = x, 1 * x = x, x * 0 = 0, 0 * x = 0
        BinaryOp::Mul => match (left, right) {
            (Expr::IntLit(1), other) | (other, Expr::IntLit(1)) => Some(other.clone()),
            (Expr::FloatLit(v), other) | (other, Expr::FloatLit(v)) if *v == 1.0 => {
                Some(other.clone())
            }
            (Expr::IntLit(0), _) | (_, Expr::IntLit(0)) => Some(Expr::IntLit(0)),
            (Expr::FloatLit(v), _) | (_, Expr::FloatLit(v)) if *v == 0.0 => {
                Some(Expr::FloatLit(0.0))
            }
            _ => None,
        },
        // x / 1 = x
        BinaryOp::Div => match right {
            Expr::IntLit(1) => Some(left.clone()),
            Expr::FloatLit(v) if *v == 1.0 => Some(left.clone()),
            _ => None,
        },
        // true && x = x, x && true = x, false && x = false
        BinaryOp::And => match (left, right) {
            (Expr::BoolLit(true), other) | (other, Expr::BoolLit(true)) => Some(other.clone()),
            (Expr::BoolLit(false), _) | (_, Expr::BoolLit(false)) => Some(Expr::BoolLit(false)),
            _ => None,
        },
        // false || x = x, x || false = x, true || x = true
        BinaryOp::Or => match (left, right) {
            (Expr::BoolLit(false), other) | (other, Expr::BoolLit(false)) => Some(other.clone()),
            (Expr::BoolLit(true), _) | (_, Expr::BoolLit(true)) => Some(Expr::BoolLit(true)),
            _ => None,
        },
        _ => None,
    }
}

/// Optimize an instruction
fn optimize_instruction(instr: Instruction, level: OptLevel) -> Option<Instruction> {
    if level == OptLevel::None {
        return Some(instr);
    }

    match instr {
        Instruction::Statement(stmt) => {
            // Most optimizations are at the expression level for contracts
            Some(Instruction::Statement(stmt))
        }
        Instruction::Label(_) => Some(instr),
    }
}

/// Eliminate dead code after unconditional jumps
fn eliminate_dead_code(body: &mut Vec<Instruction>) {
    let mut i = 0;
    while i < body.len() {
        let is_unconditional_jump = match &body[i] {
            Instruction::Statement(stmt) => {
                matches!(stmt.opcode, Opcode::Jmp | Opcode::Ret)
            }
            _ => false,
        };

        if is_unconditional_jump && i + 1 < body.len() {
            // Check if next instruction is a label (labels are jump targets, keep them)
            if !matches!(&body[i + 1], Instruction::Label(_)) {
                // Remove dead code
                body.remove(i + 1);
                continue;
            }
        }
        i += 1;
    }
}

/// Statistics about optimizations performed
#[derive(Debug, Default)]
pub struct OptStats {
    pub constants_folded: usize,
    pub dead_code_eliminated: usize,
    pub expressions_simplified: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_folding_int() {
        let expr = Expr::Binary {
            op: BinaryOp::Add,
            left: Box::new(Expr::IntLit(2)),
            right: Box::new(Expr::IntLit(3)),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::IntLit(5)));
    }

    #[test]
    fn test_constant_folding_nested() {
        // (2 + 3) * 4 = 20
        let expr = Expr::Binary {
            op: BinaryOp::Mul,
            left: Box::new(Expr::Binary {
                op: BinaryOp::Add,
                left: Box::new(Expr::IntLit(2)),
                right: Box::new(Expr::IntLit(3)),
            }),
            right: Box::new(Expr::IntLit(4)),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::IntLit(20)));
    }

    #[test]
    fn test_simplify_add_zero() {
        let expr = Expr::Binary {
            op: BinaryOp::Add,
            left: Box::new(Expr::Var(Identifier::new("x", Span::default()))),
            right: Box::new(Expr::IntLit(0)),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::Var(_)));
    }

    #[test]
    fn test_simplify_mul_one() {
        let expr = Expr::Binary {
            op: BinaryOp::Mul,
            left: Box::new(Expr::IntLit(1)),
            right: Box::new(Expr::Var(Identifier::new("x", Span::default()))),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::Var(_)));
    }

    #[test]
    fn test_simplify_mul_zero() {
        let expr = Expr::Binary {
            op: BinaryOp::Mul,
            left: Box::new(Expr::Var(Identifier::new("x", Span::default()))),
            right: Box::new(Expr::IntLit(0)),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::IntLit(0)));
    }

    #[test]
    fn test_double_negation_elimination() {
        let expr = Expr::Unary {
            op: UnaryOp::Neg,
            operand: Box::new(Expr::Unary {
                op: UnaryOp::Neg,
                operand: Box::new(Expr::IntLit(5)),
            }),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::IntLit(5)));
    }

    #[test]
    fn test_bool_simplification() {
        // true && x = x
        let expr = Expr::Binary {
            op: BinaryOp::And,
            left: Box::new(Expr::BoolLit(true)),
            right: Box::new(Expr::Var(Identifier::new("x", Span::default()))),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::Var(_)));

        // false || x = x
        let expr = Expr::Binary {
            op: BinaryOp::Or,
            left: Box::new(Expr::BoolLit(false)),
            right: Box::new(Expr::Var(Identifier::new("x", Span::default()))),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::Var(_)));
    }

    #[test]
    fn test_comparison_folding() {
        let expr = Expr::Binary {
            op: BinaryOp::Lt,
            left: Box::new(Expr::IntLit(3)),
            right: Box::new(Expr::IntLit(5)),
        };

        let result = optimize_expr(expr, OptLevel::Basic);
        assert!(matches!(result, Expr::BoolLit(true)));
    }
}
