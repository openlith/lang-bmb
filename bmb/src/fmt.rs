//! BMB Source Code Formatter
//!
//! Consistent formatting for BMB programs.
//!
//! "Omission is guessing, and guessing is error."
//! - Consistent formatting makes code clearer and reduces guessing.

use crate::ast::*;

/// Format a BMB program as a string
pub fn format_program(program: &Program) -> String {
    let mut output = String::new();

    for (i, node) in program.nodes.iter().enumerate() {
        if i > 0 {
            output.push('\n');
        }
        output.push_str(&format_node(node));
    }

    output
}

/// Format a single node
fn format_node(node: &Node) -> String {
    let mut output = String::new();

    // Node declaration
    output.push_str(&format!("@node {}\n", node.name.name));

    // Parameters
    output.push_str("@params");
    if !node.params.is_empty() {
        for param in &node.params {
            output.push_str(&format!(" {}:{}", param.name.name, param.ty));
        }
    }
    output.push('\n');

    // Return type
    output.push_str(&format!("@returns {}\n", node.returns));

    // Preconditions (multiple allowed)
    for pre in &node.preconditions {
        output.push_str(&format!("@pre {}\n", format_expr(pre)));
    }

    // Postconditions (multiple allowed)
    for post in &node.postconditions {
        output.push_str(&format!("@post {}\n", format_expr(post)));
    }

    // Loop invariants
    for inv in &node.invariants {
        output.push_str(&format!(
            "@invariant _{} {}\n",
            inv.label.name,
            format_expr(&inv.condition)
        ));
    }

    // Body
    for instr in &node.body {
        output.push_str(&format_instruction(instr));
    }

    output
}

/// Format an instruction
fn format_instruction(instr: &Instruction) -> String {
    match instr {
        Instruction::Label(name) => format!("{}:\n", name.name),
        Instruction::Statement(stmt) => {
            let mut line = format!("  {}", stmt.opcode);
            for operand in &stmt.operands {
                line.push(' ');
                line.push_str(&format_operand(operand));
            }
            line.push('\n');
            line
        }
    }
}

/// Format an operand
fn format_operand(operand: &Operand) -> String {
    match operand {
        Operand::Register(name) => format!("%{}", name.name),
        Operand::Identifier(name) => name.name.clone(),
        Operand::IntLiteral(v) => v.to_string(),
        Operand::FloatLiteral(v) => format!("{:.1}", v),
        Operand::StringLiteral(s) => format!("\"{}\"", escape_string(s)),
        Operand::Label(name) => format!("_{}", name.name),
        Operand::FieldAccess { base, field } => format!("{}.{}", base.name, field.name),
        Operand::ArrayAccess { base, index } => {
            format!("{}[{}]", base.name, format_operand(index))
        }
        Operand::QualifiedIdent { module, name } => format!("{}::{}", module.name, name.name),
    }
}

/// Escape special characters in a string for output
fn escape_string(s: &str) -> String {
    let mut result = String::new();
    for c in s.chars() {
        match c {
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '\0' => result.push_str("\\0"),
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            _ => result.push(c),
        }
    }
    result
}

/// Format an expression
fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::IntLit(v) => v.to_string(),
        Expr::FloatLit(v) => {
            if v.fract() == 0.0 {
                format!("{:.1}", v)
            } else {
                v.to_string()
            }
        }
        Expr::BoolLit(b) => b.to_string(),
        Expr::Var(id) => id.name.clone(),
        Expr::Ret => "ret".to_string(),
        Expr::Old(inner) => format!("old({})", format_expr(inner)),
        Expr::Binary { op, left, right } => {
            let left_str = format_expr(left);
            let right_str = format_expr(right);
            let op_str = match op {
                BinaryOp::Add => "+",
                BinaryOp::Sub => "-",
                BinaryOp::Mul => "*",
                BinaryOp::Div => "/",
                BinaryOp::Mod => "%",
                BinaryOp::Eq => "==",
                BinaryOp::Ne => "!=",
                BinaryOp::Lt => "<",
                BinaryOp::Le => "<=",
                BinaryOp::Gt => ">",
                BinaryOp::Ge => ">=",
                BinaryOp::And => "&&",
                BinaryOp::Or => "||",
            };
            format!("{} {} {}", left_str, op_str, right_str)
        }
        Expr::Unary { op, operand } => {
            let operand_str = format_expr(operand);
            let op_str = match op {
                UnaryOp::Neg => "-",
                UnaryOp::Not => "!",
            };
            format!("{}{}", op_str, operand_str)
        }
        Expr::SelfRef => "self".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    #[test]
    fn test_format_simple() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32

  add %r a b
  ret %r
"#;

        let ast = parser::parse(source).unwrap();
        let formatted = format_program(&ast);

        assert!(formatted.contains("@node sum"));
        assert!(formatted.contains("@params a:i32 b:i32"));
        assert!(formatted.contains("@returns i32"));
        assert!(formatted.contains("add %r a b"));
        assert!(formatted.contains("ret %r"));
    }

    #[test]
    fn test_format_with_contracts() {
        let source = r#"
@node divide
@params a:i32 b:i32
@returns i32
@pre b != 0
@post true

  div %r a b
  ret %r
"#;

        let ast = parser::parse(source).unwrap();
        let formatted = format_program(&ast);

        assert!(formatted.contains("@pre b != 0"));
        assert!(formatted.contains("@post true"));
    }
}
