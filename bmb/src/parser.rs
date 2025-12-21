//! BMB Parser
//!
//! Parses BMB source code into an AST using pest PEG parser.

use pest::Parser;
use pest_derive::Parser;

use crate::ast::*;
use crate::{BmbError, Result};

#[derive(Parser)]
#[grammar = "../grammar/bmb.pest"]
struct BmbParser;

/// Parse BMB source code into an AST
///
/// # Arguments
///
/// * `source` - The BMB source code to parse
///
/// # Returns
///
/// The parsed program AST or a parse error
pub fn parse(source: &str) -> Result<Program> {
    let mut pairs = BmbParser::parse(Rule::program, source).map_err(|e| {
        let (line, column) = match e.line_col {
            pest::error::LineColLocation::Pos((l, c)) => (l, c),
            pest::error::LineColLocation::Span((l, c), _) => (l, c),
        };
        BmbError::ParseError {
            line,
            column,
            message: e.variant.message().to_string(),
        }
    })?;

    let mut imports = Vec::new();
    let mut nodes = Vec::new();

    // Get the program pair and iterate over its inner pairs
    if let Some(program_pair) = pairs.next() {
        for pair in program_pair.into_inner() {
            match pair.as_rule() {
                Rule::import => {
                    imports.push(parse_import(pair)?);
                }
                Rule::node => {
                    nodes.push(parse_node(pair)?);
                }
                Rule::EOI => {}
                _ => {}
            }
        }
    }

    Ok(Program { imports, nodes })
}

fn parse_import(pair: pest::iterators::Pair<Rule>) -> Result<Import> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap())?;

    // Parse parameter types (optional)
    let mut param_types = Vec::new();
    if let Some(import_params) = inner.next() {
        if import_params.as_rule() == Rule::import_params {
            for type_pair in import_params.into_inner() {
                param_types.push(parse_type(type_pair)?);
            }
        }
    }

    Ok(Import {
        name,
        param_types,
        span,
    })
}

fn parse_node(pair: pest::iterators::Pair<Rule>) -> Result<Node> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap())?;
    let params = parse_params(inner.next().unwrap())?;
    let returns_pair = inner.next().unwrap();
    let returns = parse_type(returns_pair.into_inner().next().unwrap())?;

    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();
    let mut body = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::contracts => {
                // Parse contracts block which can contain multiple @pre and @post
                for contract in item.into_inner() {
                    match contract.as_rule() {
                        Rule::pre => {
                            preconditions.push(parse_expr(contract.into_inner().next().unwrap())?);
                        }
                        Rule::post => {
                            postconditions.push(parse_expr(contract.into_inner().next().unwrap())?);
                        }
                        _ => {}
                    }
                }
            }
            Rule::body => {
                body = parse_body(item)?;
            }
            _ => {}
        }
    }

    // For now, combine multiple preconditions with AND
    // In the future, we could store them separately
    let precondition = if preconditions.is_empty() {
        None
    } else if preconditions.len() == 1 {
        Some(preconditions.remove(0))
    } else {
        // Combine with AND
        let mut combined = preconditions.remove(0);
        for pre in preconditions {
            combined = Expr::Binary {
                left: Box::new(combined),
                op: BinaryOp::And,
                right: Box::new(pre),
            };
        }
        Some(combined)
    };

    let postcondition = if postconditions.is_empty() {
        None
    } else if postconditions.len() == 1 {
        Some(postconditions.remove(0))
    } else {
        let mut combined = postconditions.remove(0);
        for post in postconditions {
            combined = Expr::Binary {
                left: Box::new(combined),
                op: BinaryOp::And,
                right: Box::new(post),
            };
        }
        Some(combined)
    };

    Ok(Node {
        name,
        params,
        returns,
        precondition,
        postcondition,
        body,
        span,
    })
}

fn parse_params(pair: pest::iterators::Pair<Rule>) -> Result<Vec<Parameter>> {
    let mut params = Vec::new();

    for param_pair in pair.into_inner() {
        if param_pair.as_rule() == Rule::param {
            let span = pair_to_span(&param_pair);
            let mut inner = param_pair.into_inner();
            let name = parse_identifier(inner.next().unwrap())?;
            let ty = parse_type(inner.next().unwrap())?;
            params.push(Parameter { name, ty, span });
        }
    }

    Ok(params)
}

fn parse_type(pair: pest::iterators::Pair<Rule>) -> Result<Type> {
    match pair.as_str() {
        "i32" => Ok(Type::I32),
        "i64" => Ok(Type::I64),
        "f32" => Ok(Type::F32),
        "f64" => Ok(Type::F64),
        "bool" => Ok(Type::Bool),
        other => Err(BmbError::ParseError {
            line: 0,
            column: 0,
            message: format!("Unknown type: {}", other),
        }),
    }
}

fn parse_body(pair: pest::iterators::Pair<Rule>) -> Result<Vec<Instruction>> {
    let mut instructions = Vec::new();

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::label => {
                // Label is atomic: "_name:"
                // Extract name by removing "_" prefix and ":" suffix
                let text = item.as_str();
                let name = &text[1..text.len() - 1]; // Remove "_" and ":"
                let span = pair_to_span(&item);
                instructions.push(Instruction::Label(Identifier::new(name, span)));
            }
            Rule::stmt => {
                instructions.push(Instruction::Statement(parse_statement(item)?));
            }
            _ => {}
        }
    }

    Ok(instructions)
}

fn parse_statement(pair: pest::iterators::Pair<Rule>) -> Result<Statement> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    let opcode = parse_opcode(inner.next().unwrap())?;
    let operands: Vec<Operand> = inner.map(|p| parse_operand(p)).collect::<Result<_>>()?;

    Ok(Statement {
        opcode,
        operands,
        span,
    })
}

fn parse_opcode(pair: pest::iterators::Pair<Rule>) -> Result<Opcode> {
    match pair.as_str() {
        "add" => Ok(Opcode::Add),
        "sub" => Ok(Opcode::Sub),
        "mul" => Ok(Opcode::Mul),
        "div" => Ok(Opcode::Div),
        "mod" => Ok(Opcode::Mod),
        "eq" => Ok(Opcode::Eq),
        "ne" => Ok(Opcode::Ne),
        "lt" => Ok(Opcode::Lt),
        "le" => Ok(Opcode::Le),
        "gt" => Ok(Opcode::Gt),
        "ge" => Ok(Opcode::Ge),
        "ret" => Ok(Opcode::Ret),
        "jmp" => Ok(Opcode::Jmp),
        "jif" => Ok(Opcode::Jif),
        "call" => Ok(Opcode::Call),
        "xcall" => Ok(Opcode::Xcall),
        "mov" => Ok(Opcode::Mov),
        "load" => Ok(Opcode::Load),
        "store" => Ok(Opcode::Store),
        other => Err(BmbError::ParseError {
            line: 0,
            column: 0,
            message: format!("Unknown opcode: {}", other),
        }),
    }
}

fn parse_operand(pair: pest::iterators::Pair<Rule>) -> Result<Operand> {
    match pair.as_rule() {
        Rule::operand => {
            // operand = { register | label_ref | float_literal | int_literal | ident }
            // Drill into the inner pair
            parse_operand(pair.into_inner().next().unwrap())
        }
        Rule::register => {
            let name = pair.as_str()[1..].to_string(); // Remove '%' prefix
            Ok(Operand::Register(Identifier::new(
                name,
                pair_to_span(&pair),
            )))
        }
        Rule::label_ref => {
            let name = pair.as_str()[1..].to_string(); // Remove '_' prefix
            Ok(Operand::Label(Identifier::new(name, pair_to_span(&pair))))
        }
        Rule::int_literal => {
            let value: i64 = pair.as_str().parse().map_err(|_| BmbError::ParseError {
                line: 0,
                column: 0,
                message: format!("Invalid integer: {}", pair.as_str()),
            })?;
            Ok(Operand::IntLiteral(value))
        }
        Rule::float_literal => {
            let value: f64 = pair.as_str().parse().map_err(|_| BmbError::ParseError {
                line: 0,
                column: 0,
                message: format!("Invalid float: {}", pair.as_str()),
            })?;
            Ok(Operand::FloatLiteral(value))
        }
        Rule::ident => Ok(Operand::Identifier(parse_identifier(pair)?)),
        _ => Err(BmbError::ParseError {
            line: 0,
            column: 0,
            message: format!("Unexpected operand: {:?}", pair.as_rule()),
        }),
    }
}

fn parse_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr> {
    match pair.as_rule() {
        Rule::expr => {
            // expr = { or_expr }
            parse_expr(pair.into_inner().next().unwrap())
        }
        Rule::or_expr => {
            // or_expr = { and_expr ~ ("||" ~ and_expr)* }
            parse_binary_expr(pair, |op| op == "||", BinaryOp::Or)
        }
        Rule::and_expr => {
            // and_expr = { comparison ~ ("&&" ~ comparison)* }
            parse_binary_expr(pair, |op| op == "&&", BinaryOp::And)
        }
        Rule::comparison => {
            // comparison = { term ~ (comp_op ~ term)? }
            let mut inner = pair.into_inner();
            let left = parse_expr(inner.next().unwrap())?;

            if let Some(op_pair) = inner.next() {
                let op = match op_pair.as_str() {
                    "==" => BinaryOp::Eq,
                    "!=" => BinaryOp::Ne,
                    "<=" => BinaryOp::Le,
                    ">=" => BinaryOp::Ge,
                    "<" => BinaryOp::Lt,
                    ">" => BinaryOp::Gt,
                    _ => {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!("Unknown comparison operator: {}", op_pair.as_str()),
                        })
                    }
                };
                let right = parse_expr(inner.next().unwrap())?;
                Ok(Expr::Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                })
            } else {
                Ok(left)
            }
        }
        Rule::term => {
            // term = { factor ~ (term_op ~ factor)* }
            let mut inner = pair.into_inner();
            let mut left = parse_expr(inner.next().unwrap())?;

            while let Some(op_pair) = inner.next() {
                let op = match op_pair.as_str() {
                    "+" => BinaryOp::Add,
                    "-" => BinaryOp::Sub,
                    _ => {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!("Unknown term operator: {}", op_pair.as_str()),
                        })
                    }
                };
                let right = parse_expr(inner.next().unwrap())?;
                left = Expr::Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                };
            }
            Ok(left)
        }
        Rule::factor => {
            // factor = { unary ~ (factor_op ~ unary)* }
            let mut inner = pair.into_inner();
            let mut left = parse_expr(inner.next().unwrap())?;

            while let Some(op_pair) = inner.next() {
                let op = match op_pair.as_str() {
                    "*" => BinaryOp::Mul,
                    "/" => BinaryOp::Div,
                    "%" => BinaryOp::Mod,
                    _ => {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!("Unknown factor operator: {}", op_pair.as_str()),
                        })
                    }
                };
                let right = parse_expr(inner.next().unwrap())?;
                left = Expr::Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                };
            }
            Ok(left)
        }
        Rule::unary => {
            // unary = { unary_op? ~ primary }
            let mut inner = pair.into_inner();
            let first = inner.next().unwrap();

            if first.as_rule() == Rule::unary_op {
                let op = match first.as_str() {
                    "!" => UnaryOp::Not,
                    "-" => UnaryOp::Neg,
                    _ => {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!("Unknown unary operator: {}", first.as_str()),
                        })
                    }
                };
                let operand = parse_expr(inner.next().unwrap())?;
                Ok(Expr::Unary {
                    op,
                    operand: Box::new(operand),
                })
            } else {
                parse_expr(first)
            }
        }
        Rule::primary => {
            // primary = { "(" ~ expr ~ ")" | float_literal | int_literal | bool_literal | ident }
            let inner = pair.into_inner().next().unwrap();
            parse_expr(inner)
        }
        Rule::int_literal => {
            let value: i64 = pair.as_str().parse().unwrap();
            Ok(Expr::IntLit(value))
        }
        Rule::float_literal => {
            let value: f64 = pair.as_str().parse().unwrap();
            Ok(Expr::FloatLit(value))
        }
        Rule::bool_literal => {
            let value = pair.as_str() == "true";
            Ok(Expr::BoolLit(value))
        }
        Rule::ret_keyword => {
            // 'ret' keyword in contracts refers to the return value
            Ok(Expr::Ret)
        }
        Rule::ident => Ok(Expr::Var(parse_identifier(pair)?)),
        _ => Err(BmbError::ParseError {
            line: 0,
            column: 0,
            message: format!("Unexpected expression: {:?}", pair.as_rule()),
        }),
    }
}

fn parse_binary_expr<F>(
    pair: pest::iterators::Pair<Rule>,
    is_op: F,
    binary_op: BinaryOp,
) -> Result<Expr>
where
    F: Fn(&str) -> bool,
{
    let mut inner = pair.into_inner();
    let mut left = parse_expr(inner.next().unwrap())?;

    while let Some(next) = inner.next() {
        if is_op(next.as_str()) {
            // This is an operator, get the right operand
            if let Some(right_pair) = inner.next() {
                let right = parse_expr(right_pair)?;
                left = Expr::Binary {
                    left: Box::new(left),
                    op: binary_op.clone(),
                    right: Box::new(right),
                };
            }
        } else {
            // This is a sub-expression, parse it
            let right = parse_expr(next)?;
            left = Expr::Binary {
                left: Box::new(left),
                op: binary_op.clone(),
                right: Box::new(right),
            };
        }
    }

    Ok(left)
}

fn parse_identifier(pair: pest::iterators::Pair<Rule>) -> Result<Identifier> {
    Ok(Identifier::new(pair.as_str(), pair_to_span(&pair)))
}

fn pair_to_span(pair: &pest::iterators::Pair<Rule>) -> Span {
    let pest_span = pair.as_span();
    let (line, column) = pest_span.start_pos().line_col();
    Span::new(pest_span.start(), pest_span.end(), line, column)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty_program() {
        let result = parse("");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().nodes.len(), 0);
    }

    #[test]
    fn test_pest_debug() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32

  add %r a b
  ret %r
"#;
        let result = BmbParser::parse(Rule::program, source);
        match result {
            Ok(pairs) => {
                for pair in pairs {
                    println!("Rule: {:?}, Text: {:?}", pair.as_rule(), pair.as_str());
                    for inner in pair.into_inner() {
                        println!(
                            "  Inner Rule: {:?}, Text: {:?}",
                            inner.as_rule(),
                            inner.as_str()
                        );
                    }
                }
            }
            Err(e) => {
                panic!("Parse error: {}", e);
            }
        }
    }

    #[test]
    fn test_label_parsing_directly() {
        // Test if label rule can parse a label directly
        let label_source = "_one:";
        let result = BmbParser::parse(Rule::label, label_source);
        assert!(
            result.is_ok(),
            "Failed to parse label directly: {:?}",
            result.err()
        );

        // Test label_ref without colon
        let label_ref_source = "_one";
        let result2 = BmbParser::parse(Rule::label_ref, label_ref_source);
        assert!(
            result2.is_ok(),
            "Failed to parse label_ref: {:?}",
            result2.err()
        );
    }

    #[test]
    fn test_body_with_label() {
        // Test parsing a body that contains a label
        let body_source = r#"ret 1
_one:
  ret 0"#;
        let result = BmbParser::parse(Rule::body, body_source);
        assert!(
            result.is_ok(),
            "Failed to parse body with label: {:?}",
            result.err()
        );

        let body = result.unwrap().next().unwrap();
        let items: Vec<_> = body.into_inner().collect();
        assert_eq!(items.len(), 3, "Expected 3 items: stmt, label, stmt");
    }

    #[test]
    fn test_body_two_stmts() {
        // Test parsing a body that contains two statements
        let body_source = "add %r a b\nret %r";
        let result = BmbParser::parse(Rule::body, body_source);
        assert!(
            result.is_ok(),
            "Failed to parse body with two stmts: {:?}",
            result.err()
        );

        let body = result.unwrap().next().unwrap();
        let items: Vec<_> = body.into_inner().collect();
        assert_eq!(items.len(), 2, "Expected 2 statements");
    }

    #[test]
    fn test_parse_simple_function() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32

  add %r a b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let program = result.unwrap();
        assert_eq!(program.nodes.len(), 1);

        let node = &program.nodes[0];
        assert_eq!(node.name.name, "sum");
        assert_eq!(node.params.len(), 2);
        assert_eq!(node.params[0].name.name, "a");
        assert_eq!(node.params[0].ty, Type::I32);
        assert_eq!(node.returns, Type::I32);

        // Check body structure
        assert_eq!(node.body.len(), 2, "Expected 2 instructions in body");
        if let Instruction::Statement(ref stmt) = node.body[0] {
            assert_eq!(
                stmt.operands.len(),
                3,
                "add should have 3 operands: {:?}",
                stmt.operands
            );
        }
    }

    #[test]
    fn test_parse_with_precondition() {
        let source = r#"
@node divide
@params a:f64 b:f64
@returns f64
@pre b != 0

  div %r a b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let program = result.unwrap();
        let node = &program.nodes[0];
        assert!(node.precondition.is_some());
        assert!(node.postcondition.is_none());
    }

    #[test]
    fn test_parse_with_labels() {
        let source = r#"
@node factorial
@params n:i32
@returns i32
@pre n >= 0

  eq %base n 0
  jif %base _one
  ret %base
_one:
  ret 1
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let program = result.unwrap();
        let node = &program.nodes[0];

        // Check that we have instructions including a label
        let has_label = node.body.iter().any(|i| matches!(i, Instruction::Label(_)));
        assert!(has_label, "Expected to find a label in body");
    }

    #[test]
    fn test_parse_factorial_example() {
        let source = include_str!("../tests/examples/factorial.bmb");
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Failed to parse factorial.bmb: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_divide_example() {
        let source = include_str!("../tests/examples/divide.bmb");
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Failed to parse divide.bmb: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_fibonacci_example() {
        let source = include_str!("../tests/examples/fibonacci.bmb");
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Failed to parse fibonacci.bmb: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_gcd_example() {
        let source = include_str!("../tests/examples/gcd.bmb");
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Failed to parse gcd.bmb: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_error_invalid_type() {
        let source = r#"
@node bad
@params x:invalid_type
@returns i32

  ret x
"#;
        let result = parse(source);
        assert!(result.is_err(), "Expected parse error for invalid type");
    }
}
