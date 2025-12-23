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

    let mut module = None;
    let mut imports = Vec::new();
    let mut uses = Vec::new();
    let mut type_defs = Vec::new();
    let mut structs = Vec::new();
    let mut enums = Vec::new();
    let mut contracts = Vec::new();
    let mut nodes = Vec::new();

    // Get the program pair and iterate over its inner pairs
    if let Some(program_pair) = pairs.next() {
        for pair in program_pair.into_inner() {
            match pair.as_rule() {
                Rule::module_decl => {
                    module = Some(parse_module_decl(pair)?);
                }
                Rule::import => {
                    imports.push(parse_import(pair)?);
                }
                Rule::use_module => {
                    uses.push(parse_use_module(pair)?);
                }
                Rule::type_def => {
                    type_defs.push(parse_type_def(pair)?);
                }
                Rule::struct_def => {
                    structs.push(parse_struct_def(pair)?);
                }
                Rule::enum_def => {
                    enums.push(parse_enum_def(pair)?);
                }
                Rule::contract_def => {
                    contracts.push(parse_contract_def(pair)?);
                }
                Rule::node => {
                    nodes.push(parse_node(pair)?);
                }
                Rule::EOI => {}
                _ => {}
            }
        }
    }

    Ok(Program {
        module,
        imports,
        uses,
        type_defs,
        structs,
        enums,
        contracts,
        nodes,
    })
}

/// Parse module declaration: @module math.arithmetic OR @. math.arithmetic
fn parse_module_decl(pair: pest::iterators::Pair<Rule>) -> Result<ModuleDecl> {
    let span = pair_to_span(&pair);
    let mut path = Vec::new();

    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::module_name {
            // module_name = { ident ~ ("." ~ ident)* }
            // Parse the dot-separated path
            let module_str = inner.as_str();
            for part in module_str.split('.') {
                path.push(Identifier::new(part, span));
            }
        }
    }

    Ok(ModuleDecl { path, span })
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

fn parse_use_module(pair: pest::iterators::Pair<Rule>) -> Result<ModuleUse> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    let first = inner.next().unwrap();
    let path = match first.as_rule() {
        Rule::module_path => {
            // Extract the path from the quoted string
            let path_inner = first.into_inner().next().unwrap();
            ModulePath::FilePath(path_inner.as_str().to_string())
        }
        Rule::ident => ModulePath::Name(parse_identifier(first)?),
        _ => {
            return Err(BmbError::ParseError {
                line: span.line,
                column: span.column,
                message: format!("Unexpected module path: {:?}", first.as_rule()),
            })
        }
    };

    // Parse optional alias
    let alias = inner.next().map(|p| parse_identifier(p)).transpose()?;

    Ok(ModuleUse { path, alias, span })
}

fn parse_struct_def(pair: pest::iterators::Pair<Rule>) -> Result<StructDef> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap())?;
    let mut fields = Vec::new();

    for field_pair in inner {
        if field_pair.as_rule() == Rule::struct_field {
            let field_span = pair_to_span(&field_pair);
            let mut field_inner = field_pair.into_inner();
            let field_name = parse_identifier(field_inner.next().unwrap())?;
            let field_type = parse_type(field_inner.next().unwrap())?;
            fields.push(StructField {
                name: field_name,
                ty: field_type,
                span: field_span,
            });
        }
    }

    Ok(StructDef { name, fields, span })
}

fn parse_enum_def(pair: pest::iterators::Pair<Rule>) -> Result<EnumDef> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap())?;
    let mut variants = Vec::new();

    for variant_pair in inner {
        if variant_pair.as_rule() == Rule::enum_variant {
            let variant_span = pair_to_span(&variant_pair);
            let mut variant_inner = variant_pair.into_inner();
            let variant_name = parse_identifier(variant_inner.next().unwrap())?;
            let payload = variant_inner.next().map(|t| parse_type(t)).transpose()?;
            variants.push(EnumVariant {
                name: variant_name,
                payload,
                span: variant_span,
            });
        }
    }

    Ok(EnumDef {
        name,
        variants,
        span,
    })
}

/// Parse a refined type definition: @type nz_i32 i32 where self != 0
/// Grammar: type_def = { ("@type" | "@#t") ~ ident ~ type_params? ~ type_spec ~ "where" ~ expr }
fn parse_type_def(pair: pest::iterators::Pair<Rule>) -> Result<TypeDef> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    // Parse type name (e.g., "nz_i32", "pos_i32", "index")
    let name = parse_identifier(inner.next().unwrap())?;

    // Parse optional type parameters and base type
    let mut params = Vec::new();
    let mut base_type = None;
    let mut constraint = None;

    for item in inner {
        match item.as_rule() {
            Rule::type_params => {
                // type_params = { "[" ~ ident ~ ("," ~ ident)* ~ "]" }
                for param_pair in item.into_inner() {
                    if param_pair.as_rule() == Rule::ident {
                        params.push(parse_identifier(param_pair)?);
                    }
                }
            }
            Rule::type_spec | Rule::type_name => {
                base_type = Some(parse_type(item)?);
            }
            Rule::expr => {
                constraint = Some(parse_expr(item)?);
            }
            _ => {}
        }
    }

    let base_type = base_type.ok_or_else(|| BmbError::ParseError {
        line: 0,
        column: 0,
        message: "Refined type definition missing base type".to_string(),
    })?;

    let constraint = constraint.ok_or_else(|| BmbError::ParseError {
        line: 0,
        column: 0,
        message: "Refined type definition missing constraint expression".to_string(),
    })?;

    Ok(TypeDef {
        name,
        params,
        base_type,
        constraint,
        span,
    })
}

/// Parse a named contract definition: @contract name(params) @pre ... @post ...
fn parse_contract_def(pair: pest::iterators::Pair<Rule>) -> Result<ContractDef> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    // Parse name
    let name = parse_identifier(inner.next().unwrap())?;

    // Parse parameters and body
    let mut params = Vec::new();
    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::contract_params => {
                for param_pair in item.into_inner() {
                    if param_pair.as_rule() == Rule::contract_param {
                        let param_span = pair_to_span(&param_pair);
                        let mut param_inner = param_pair.into_inner();
                        let param_name = parse_identifier(param_inner.next().unwrap())?;
                        let param_type = parse_type(param_inner.next().unwrap())?;
                        params.push(Parameter {
                            name: param_name,
                            ty: param_type,
                            span: param_span,
                        });
                    }
                }
            }
            Rule::contract_body => {
                for body_item in item.into_inner() {
                    match body_item.as_rule() {
                        Rule::contract_pre => {
                            for expr_pair in body_item.into_inner() {
                                preconditions.push(parse_expr(expr_pair)?);
                            }
                        }
                        Rule::contract_post => {
                            for expr_pair in body_item.into_inner() {
                                postconditions.push(parse_expr(expr_pair)?);
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    Ok(ContractDef {
        name,
        params,
        preconditions,
        postconditions,
        span,
    })
}

fn parse_node(pair: pest::iterators::Pair<Rule>) -> Result<Node> {
    let span = pair_to_span(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap())?;

    // Initialize all node fields
    let mut tags = Vec::new();
    let mut params = Vec::new();
    let mut returns = Type::Void;
    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();
    let mut invariants = Vec::new();
    let mut variants = Vec::new();
    let mut pure = false;
    let mut requires = Vec::new();
    let mut assertions = Vec::new();
    let mut tests = Vec::new();
    let mut body = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::node_tags => {
                // Parse tags: @tags [tag1, tag2, ...] OR @# [...]
                for tag_item in item.into_inner() {
                    if tag_item.as_rule() == Rule::tag_list {
                        for tag in tag_item.into_inner() {
                            tags.push(parse_identifier(tag)?);
                        }
                    }
                }
            }
            Rule::params => {
                params = parse_params(item)?;
            }
            Rule::returns => {
                returns = parse_type(item.into_inner().next().unwrap())?;
            }
            Rule::contracts => {
                // Parse contracts: @pre, @post, @invariant, @assert, @variant, @pure, @requires
                for contract in item.into_inner() {
                    match contract.as_rule() {
                        Rule::pre => {
                            preconditions.push(parse_expr(contract.into_inner().next().unwrap())?);
                        }
                        Rule::post => {
                            postconditions.push(parse_expr(contract.into_inner().next().unwrap())?);
                        }
                        Rule::invariant => {
                            let inv_span = pair_to_span(&contract);
                            let mut inv_inner = contract.into_inner();
                            let label_pair = inv_inner.next().unwrap();
                            let label_name = label_pair.as_str()[1..].to_string();
                            let label = Identifier::new(label_name, pair_to_span(&label_pair));
                            let condition = parse_expr(inv_inner.next().unwrap())?;
                            invariants.push(Invariant {
                                label,
                                condition,
                                span: inv_span,
                            });
                        }
                        Rule::assert_stmt => {
                            let assert_span = pair_to_span(&contract);
                            let condition = parse_expr(contract.into_inner().next().unwrap())?;
                            assertions.push(Assert {
                                condition,
                                span: assert_span,
                            });
                        }
                        Rule::variant => {
                            let var_span = pair_to_span(&contract);
                            let measure = parse_expr(contract.into_inner().next().unwrap())?;
                            variants.push(Variant {
                                measure,
                                span: var_span,
                            });
                        }
                        Rule::pure => {
                            pure = true;
                        }
                        Rule::requires => {
                            let req_span = pair_to_span(&contract);
                            let mut req_inner = contract.into_inner();
                            let contract_name = parse_identifier(req_inner.next().unwrap())?;
                            let mut args = Vec::new();
                            if let Some(args_pair) = req_inner.next() {
                                if args_pair.as_rule() == Rule::requires_args {
                                    for arg in args_pair.into_inner() {
                                        args.push(parse_expr(arg)?);
                                    }
                                }
                            }
                            requires.push(Requires {
                                contract: contract_name,
                                args,
                                span: req_span,
                            });
                        }
                        _ => {}
                    }
                }
            }
            Rule::tests => {
                // Parse test cases: @test expect(...) OR @? expect(...)
                for test_item in item.into_inner() {
                    if test_item.as_rule() == Rule::test_case {
                        tests.push(parse_test_case(test_item)?);
                    }
                }
            }
            Rule::body => {
                body = parse_body(item)?;
            }
            _ => {}
        }
    }

    Ok(Node {
        name,
        tags,
        params,
        returns,
        preconditions,
        postconditions,
        invariants,
        variants,
        pure,
        requires,
        assertions,
        tests,
        body,
        span,
    })
}

/// Parse a test case: @test expect(factorial(5), 120)
fn parse_test_case(pair: pest::iterators::Pair<Rule>) -> Result<TestCase> {
    let span = pair_to_span(&pair);

    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::test_expr {
            let mut test_inner = inner.into_inner();
            let function = parse_identifier(test_inner.next().unwrap())?;

            let mut args = Vec::new();
            if let Some(args_pair) = test_inner.next() {
                if args_pair.as_rule() == Rule::test_args {
                    for arg in args_pair.into_inner() {
                        args.push(parse_test_arg(arg)?);
                    }
                }
            }

            return Ok(TestCase {
                function,
                args,
                span,
            });
        }
    }

    Err(BmbError::ParseError {
        line: span.line,
        column: span.column,
        message: "Invalid test case".to_string(),
    })
}

/// Parse a test argument
fn parse_test_arg(pair: pest::iterators::Pair<Rule>) -> Result<TestArg> {
    match pair.as_rule() {
        Rule::test_arg => {
            // test_arg can be: float_literal | int_literal | bool_literal | ident("("test_args?")") | ident
            // We need to check if there are multiple children (function call) or just one
            let mut inner = pair.into_inner();
            let first = inner.next().unwrap();

            match first.as_rule() {
                Rule::float_literal => {
                    let value: f64 = first.as_str().parse().unwrap();
                    Ok(TestArg::Float(value))
                }
                Rule::int_literal => {
                    let value: i64 = first.as_str().parse().unwrap();
                    Ok(TestArg::Int(value))
                }
                Rule::bool_literal => {
                    let value = first.as_str() == "true";
                    Ok(TestArg::Bool(value))
                }
                Rule::ident => {
                    // Check if there's a test_args following (function call)
                    if let Some(args_pair) = inner.next() {
                        if args_pair.as_rule() == Rule::test_args {
                            let func = parse_identifier(first)?;
                            let mut args = Vec::new();
                            for arg in args_pair.into_inner() {
                                args.push(parse_test_arg(arg)?);
                            }
                            return Ok(TestArg::Call { func, args });
                        }
                    }
                    // Just a variable reference
                    Ok(TestArg::Var(parse_identifier(first)?))
                }
                _ => Err(BmbError::ParseError {
                    line: 0,
                    column: 0,
                    message: format!("Invalid test argument rule: {:?}", first.as_rule()),
                }),
            }
        }
        Rule::int_literal => {
            let value: i64 = pair.as_str().parse().unwrap();
            Ok(TestArg::Int(value))
        }
        Rule::float_literal => {
            let value: f64 = pair.as_str().parse().unwrap();
            Ok(TestArg::Float(value))
        }
        Rule::bool_literal => {
            let value = pair.as_str() == "true";
            Ok(TestArg::Bool(value))
        }
        Rule::ident => {
            Ok(TestArg::Var(parse_identifier(pair)?))
        }
        _ => {
            Err(BmbError::ParseError {
                line: 0,
                column: 0,
                message: format!("Invalid test argument: {:?}", pair.as_rule()),
            })
        }
    }
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
    match pair.as_rule() {
        Rule::type_name | Rule::type_spec => {
            // Drill into inner
            parse_type(pair.into_inner().next().unwrap())
        }
        Rule::primitive_type => match pair.as_str() {
            // Signed integers
            "i8" => Ok(Type::I8),
            "i16" => Ok(Type::I16),
            "i32" => Ok(Type::I32),
            "i64" => Ok(Type::I64),
            // Unsigned integers
            "u8" => Ok(Type::U8),
            "u16" => Ok(Type::U16),
            "u32" => Ok(Type::U32),
            "u64" => Ok(Type::U64),
            // Floating-point
            "f32" => Ok(Type::F32),
            "f64" => Ok(Type::F64),
            // Other primitives
            "bool" => Ok(Type::Bool),
            "char" => Ok(Type::Char),
            "void" => Ok(Type::Void),
            other => Err(BmbError::ParseError {
                line: 0,
                column: 0,
                message: format!("Unknown primitive type: {}", other),
            }),
        },
        Rule::array_type => {
            // array_type = { "[" ~ type_spec ~ ";" ~ array_size ~ "]" }
            let mut inner = pair.into_inner();
            let element_type = parse_type(inner.next().unwrap())?;
            let size_str = inner.next().unwrap().as_str();
            let size: usize = size_str.parse().map_err(|_| BmbError::ParseError {
                line: 0,
                column: 0,
                message: format!("Invalid array size: {}", size_str),
            })?;
            Ok(Type::Array {
                element: Box::new(element_type),
                size,
            })
        }
        Rule::ref_type => {
            // ref_type = { "&" ~ type_spec }
            let inner_type = parse_type(pair.into_inner().next().unwrap())?;
            Ok(Type::Ref(Box::new(inner_type)))
        }
        Rule::ptr_type => {
            // ptr_type = { "*" ~ type_spec }
            let inner_type = parse_type(pair.into_inner().next().unwrap())?;
            Ok(Type::Ptr(Box::new(inner_type)))
        }
        Rule::generic_type => {
            // generic_type = { generic_name ~ "<" ~ type_spec ~ ("," ~ type_spec)* ~ ">" }
            let mut inner = pair.into_inner();
            let generic_name = inner.next().unwrap().as_str();
            let type_args: Vec<Type> = inner.map(|p| parse_type(p)).collect::<Result<Vec<_>>>()?;

            match generic_name {
                "Option" => {
                    if type_args.len() != 1 {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!(
                                "Option requires exactly 1 type argument, got {}",
                                type_args.len()
                            ),
                        });
                    }
                    Ok(Type::Option(Box::new(type_args.into_iter().next().unwrap())))
                }
                "Result" => {
                    if type_args.len() != 2 {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!(
                                "Result requires exactly 2 type arguments, got {}",
                                type_args.len()
                            ),
                        });
                    }
                    let mut iter = type_args.into_iter();
                    Ok(Type::Result {
                        ok: Box::new(iter.next().unwrap()),
                        err: Box::new(iter.next().unwrap()),
                    })
                }
                "Vector" => {
                    if type_args.len() != 1 {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!(
                                "Vector requires exactly 1 type argument, got {}",
                                type_args.len()
                            ),
                        });
                    }
                    Ok(Type::Vector(Box::new(type_args.into_iter().next().unwrap())))
                }
                "Slice" => {
                    if type_args.len() != 1 {
                        return Err(BmbError::ParseError {
                            line: 0,
                            column: 0,
                            message: format!(
                                "Slice requires exactly 1 type argument, got {}",
                                type_args.len()
                            ),
                        });
                    }
                    Ok(Type::Slice(Box::new(type_args.into_iter().next().unwrap())))
                }
                _ => Err(BmbError::ParseError {
                    line: 0,
                    column: 0,
                    message: format!("Unknown generic type: {}", generic_name),
                }),
            }
        }
        Rule::user_type => {
            // User-defined type (struct or enum name)
            // We'll resolve whether it's a struct or enum during type checking
            Ok(Type::Struct(pair.as_str().to_string()))
        }
        _ => {
            // Fallback for simple type names (backwards compatibility)
            match pair.as_str() {
                "i8" => Ok(Type::I8),
                "i16" => Ok(Type::I16),
                "i32" => Ok(Type::I32),
                "i64" => Ok(Type::I64),
                "u8" => Ok(Type::U8),
                "u16" => Ok(Type::U16),
                "u32" => Ok(Type::U32),
                "u64" => Ok(Type::U64),
                "f32" => Ok(Type::F32),
                "f64" => Ok(Type::F64),
                "bool" => Ok(Type::Bool),
                "char" => Ok(Type::Char),
                "void" => Ok(Type::Void),
                other => Err(BmbError::ParseError {
                    line: 0,
                    column: 0,
                    message: format!("Unknown type: {}", other),
                }),
            }
        }
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
        "and" => Ok(Opcode::And),
        "or" => Ok(Opcode::Or),
        "xor" => Ok(Opcode::Xor),
        "shl" => Ok(Opcode::Shl),
        "shr" => Ok(Opcode::Shr),
        "not" => Ok(Opcode::Not),
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
        "print" => Ok(Opcode::Print),
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
            // operand = { register | label_ref | float_literal | int_literal | field_access | array_access | qualified_ident | ident }
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
        Rule::str_literal => {
            // String literal: parse escape sequences
            let raw = pair.as_str();
            // Remove surrounding quotes
            let inner = &raw[1..raw.len() - 1];
            let parsed = parse_string_escapes(inner);
            Ok(Operand::StringLiteral(parsed))
        }
        Rule::field_access => {
            // field_access = { ident ~ "." ~ ident }
            let mut inner = pair.into_inner();
            let base = parse_identifier(inner.next().unwrap())?;
            let field = parse_identifier(inner.next().unwrap())?;
            Ok(Operand::FieldAccess { base, field })
        }
        Rule::array_access => {
            // array_access = { ident ~ "[" ~ (register | int_literal | ident) ~ "]" }
            let mut inner = pair.into_inner();
            let base = parse_identifier(inner.next().unwrap())?;
            let index_pair = inner.next().unwrap();
            let index = Box::new(parse_operand(index_pair)?);
            Ok(Operand::ArrayAccess { base, index })
        }
        Rule::qualified_ident => {
            // qualified_ident = { ident ~ "::" ~ ident }
            let mut inner = pair.into_inner();
            let module = parse_identifier(inner.next().unwrap())?;
            let name = parse_identifier(inner.next().unwrap())?;
            Ok(Operand::QualifiedIdent { module, name })
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
        Rule::self_keyword => {
            // 'self' keyword in refined type constraints refers to the value being constrained
            Ok(Expr::SelfRef)
        }
        Rule::old_expr => {
            // old(expr) refers to the pre-state value of an expression
            let inner_expr = parse_expr(pair.into_inner().next().unwrap())?;
            Ok(Expr::Old(Box::new(inner_expr)))
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

/// Parse escape sequences in a string literal
fn parse_string_escapes(s: &str) -> String {
    let mut result = String::new();
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            if let Some(&next) = chars.peek() {
                chars.next();
                match next {
                    'n' => result.push('\n'),
                    'r' => result.push('\r'),
                    't' => result.push('\t'),
                    '0' => result.push('\0'),
                    '\\' => result.push('\\'),
                    '"' => result.push('"'),
                    _ => {
                        result.push('\\');
                        result.push(next);
                    }
                }
            } else {
                result.push('\\');
            }
        } else {
            result.push(c);
        }
    }

    result
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
        assert!(!node.preconditions.is_empty());
        assert!(node.postconditions.is_empty());
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
    fn test_parse_user_defined_type() {
        // User-defined types are now allowed at parsing level (Phase A).
        // Type validation happens during type checking, not parsing.
        let source = r#"
@node bad
@params x:MyStruct
@returns i32

  ret x
"#;
        let result = parse(source);
        assert!(result.is_ok(), "User-defined types should parse successfully");
        let program = result.unwrap();
        assert_eq!(
            program.nodes[0].params[0].ty,
            Type::Struct("MyStruct".to_string())
        );
    }

    #[test]
    fn test_parse_array_type() {
        let source = r#"
@node test_arrays
@params arr:[i32; 10]
@returns i32

  ret 0
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Array types should parse successfully");
        let program = result.unwrap();
        match &program.nodes[0].params[0].ty {
            Type::Array { element, size } => {
                assert_eq!(**element, Type::I32);
                assert_eq!(*size, 10);
            }
            _ => panic!("Expected array type"),
        }
    }

    #[test]
    fn test_parse_ref_type() {
        let source = r#"
@node test_ref
@params ptr:&i32
@returns i32

  ret 0
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Reference types should parse successfully");
        let program = result.unwrap();
        match &program.nodes[0].params[0].ty {
            Type::Ref(inner) => {
                assert_eq!(**inner, Type::I32);
            }
            _ => panic!("Expected reference type"),
        }
    }

    #[test]
    fn test_parse_struct_def() {
        let source = r#"
@struct Point
  x:i32
  y:i32

@node main
@params
@returns i32
  ret 0
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Struct definitions should parse successfully");
        let program = result.unwrap();
        assert_eq!(program.structs.len(), 1);
        assert_eq!(program.structs[0].name.name, "Point");
        assert_eq!(program.structs[0].fields.len(), 2);
    }

    #[test]
    fn test_parse_enum_def() {
        let source = r#"
@enum Color
  Red
  Green
  Blue

@node main
@params
@returns i32
  ret 0
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Enum definitions should parse successfully");
        let program = result.unwrap();
        assert_eq!(program.enums.len(), 1);
        assert_eq!(program.enums[0].name.name, "Color");
        assert_eq!(program.enums[0].variants.len(), 3);
    }

    #[test]
    fn test_parse_variant() {
        let source = r#"
@node factorial
@params n:i32
@returns i32
@pre n >= 0
@variant n
@post ret >= 1

  lt %is_base n 2
  jif %is_base _base
  sub %n1 n 1
  call %rec factorial %n1
  mul %result n %rec
  ret %result
_base:
  ret 1
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @variant: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.nodes.len(), 1);
        assert_eq!(program.nodes[0].variants.len(), 1);
        // The measure should be the variable 'n'
        match &program.nodes[0].variants[0].measure {
            Expr::Var(ident) => assert_eq!(ident.name, "n"),
            _ => panic!("Expected variable 'n' as variant measure"),
        }
    }

    #[test]
    fn test_parse_variant_compact() {
        let source = r#"
@node gcd
@p a:i32 b:i32
@r i32
@< a >= 0 && b >= 0
@% a + b

  ret 0
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @% (compact variant): {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.nodes[0].variants.len(), 1);
        // The measure should be a + b
        match &program.nodes[0].variants[0].measure {
            Expr::Binary { op: BinaryOp::Add, .. } => (),
            _ => panic!("Expected 'a + b' as variant measure"),
        }
    }

    #[test]
    fn test_parse_pure() {
        let source = r#"
@node square
@params x:i32
@returns i32
@pure
@post ret == x * x

  mul %r x x
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @pure: {:?}", result.err());
        let program = result.unwrap();
        assert!(program.nodes[0].pure, "Node should be marked as pure");
    }

    #[test]
    fn test_parse_pure_compact() {
        let source = r#"
@node identity
@p x:i32
@r i32
@!
@> ret == x

  ret x
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @! (compact pure): {:?}", result.err());
        let program = result.unwrap();
        assert!(program.nodes[0].pure, "Node should be marked as pure");
    }

    #[test]
    fn test_parse_requires() {
        let source = r#"
@node safe_divide
@params a:i32 b:i32
@returns i32
@requires non_zero(b)
@post true

  div %r a b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @requires: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.nodes[0].requires.len(), 1);
        assert_eq!(program.nodes[0].requires[0].contract.name, "non_zero");
        assert_eq!(program.nodes[0].requires[0].args.len(), 1);
    }

    #[test]
    fn test_parse_requires_compact() {
        let source = r#"
@node sqrt_safe
@p x:f64
@r f64
@& non_negative(x)

  ret x
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @& (compact requires): {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.nodes[0].requires.len(), 1);
        assert_eq!(program.nodes[0].requires[0].contract.name, "non_negative");
    }

    #[test]
    fn test_parse_multiple_contracts() {
        let source = r#"
@node complex_fn
@params a:i32 b:i32
@returns i32
@pre a > 0
@pre b > 0
@variant a + b
@pure
@requires positive(a)
@requires positive(b)
@post ret > 0

  add %r a b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse multiple contracts: {:?}", result.err());
        let program = result.unwrap();
        let node = &program.nodes[0];
        assert_eq!(node.preconditions.len(), 2);
        assert_eq!(node.variants.len(), 1);
        assert!(node.pure);
        assert_eq!(node.requires.len(), 2);
        assert_eq!(node.postconditions.len(), 1);
    }

    // ========== Bitwise Operation Tests ==========

    #[test]
    fn test_parse_bitwise_and() {
        let source = r#"
@node bitwise_and
@params a:i32 b:i32
@returns i32

  and %r a b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse bitwise AND: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.nodes.len(), 1);
        let node = &program.nodes[0];
        assert_eq!(node.body.len(), 2);
        if let crate::ast::Instruction::Statement(stmt) = &node.body[0] {
            assert_eq!(stmt.opcode, crate::ast::Opcode::And);
        } else {
            panic!("Expected Statement, got Label");
        }
    }

    #[test]
    fn test_parse_bitwise_or() {
        let source = r#"
@node bitwise_or
@params a:i32 b:i32
@returns i32

  or %r a b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse bitwise OR: {:?}", result.err());
        let program = result.unwrap();
        if let crate::ast::Instruction::Statement(stmt) = &program.nodes[0].body[0] {
            assert_eq!(stmt.opcode, crate::ast::Opcode::Or);
        }
    }

    #[test]
    fn test_parse_bitwise_xor() {
        let source = r#"
@node bitwise_xor
@params a:i32 b:i32
@returns i32

  xor %r a b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse bitwise XOR: {:?}", result.err());
        let program = result.unwrap();
        if let crate::ast::Instruction::Statement(stmt) = &program.nodes[0].body[0] {
            assert_eq!(stmt.opcode, crate::ast::Opcode::Xor);
        }
    }

    #[test]
    fn test_parse_bitwise_shl() {
        let source = r#"
@node shift_left
@params a:i32 n:i32
@returns i32

  shl %r a n
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse shift left: {:?}", result.err());
        let program = result.unwrap();
        if let crate::ast::Instruction::Statement(stmt) = &program.nodes[0].body[0] {
            assert_eq!(stmt.opcode, crate::ast::Opcode::Shl);
        }
    }

    #[test]
    fn test_parse_bitwise_shr() {
        let source = r#"
@node shift_right
@params a:i32 n:i32
@returns i32

  shr %r a n
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse shift right: {:?}", result.err());
        let program = result.unwrap();
        if let crate::ast::Instruction::Statement(stmt) = &program.nodes[0].body[0] {
            assert_eq!(stmt.opcode, crate::ast::Opcode::Shr);
        }
    }

    #[test]
    fn test_parse_bitwise_not() {
        let source = r#"
@node bitwise_not
@params a:i32
@returns i32

  not %r a
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse bitwise NOT: {:?}", result.err());
        let program = result.unwrap();
        if let crate::ast::Instruction::Statement(stmt) = &program.nodes[0].body[0] {
            assert_eq!(stmt.opcode, crate::ast::Opcode::Not);
        }
    }

    #[test]
    fn test_parse_chained_bitwise() {
        let source = r#"
@node chained_bitwise
@params a:i32 b:i32
@returns i32

  and %tmp a b
  or %tmp2 %tmp a
  xor %r %tmp2 b
  ret %r
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse chained bitwise ops: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.nodes[0].body.len(), 4);
    }

    // ========== @contract Definition Tests ==========

    #[test]
    fn test_parse_contract_def_basic() {
        let source = r#"
@contract positive(n:i32)
@pre n > 0
@post ret > 0

@node test_fn
@params x:i32
@returns i32

  ret x
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @contract definition: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.contracts.len(), 1);
        assert_eq!(program.contracts[0].name.name, "positive");
        assert_eq!(program.contracts[0].params.len(), 1);
        assert_eq!(program.contracts[0].preconditions.len(), 1);
        assert_eq!(program.contracts[0].postconditions.len(), 1);
    }

    #[test]
    fn test_parse_contract_def_multiple_params() {
        let source = r#"
@contract in_range(n:i32, min:i32, max:i32)
@pre n >= min
@pre n <= max
@post ret == n

@node test_fn
@params x:i32
@returns i32

  ret x
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @contract with multiple params: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.contracts[0].params.len(), 3);
        assert_eq!(program.contracts[0].params[0].name.name, "n");
        assert_eq!(program.contracts[0].params[1].name.name, "min");
        assert_eq!(program.contracts[0].params[2].name.name, "max");
        assert_eq!(program.contracts[0].preconditions.len(), 2);
    }

    #[test]
    fn test_parse_contract_def_compact() {
        let source = r#"
@#c non_negative(x:i64)
@< x >= 0
@> ret >= 0

@node test_fn
@params x:i32
@returns i32

  ret x
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @#c (compact contract): {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.contracts.len(), 1);
        assert_eq!(program.contracts[0].name.name, "non_negative");
    }

    #[test]
    fn test_parse_multiple_contract_defs() {
        let source = r#"
@contract positive(n:i32)
@pre n > 0

@contract non_zero(n:i32)
@pre n != 0
@post ret != 0

@node test_fn
@params x:i32
@returns i32

  ret x
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse multiple @contract definitions: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.contracts.len(), 2);
        assert_eq!(program.contracts[0].name.name, "positive");
        assert_eq!(program.contracts[1].name.name, "non_zero");
    }

    #[test]
    fn test_parse_contract_no_params() {
        let source = r#"
@contract always_true()
@pre true
@post true

@node test_fn
@params
@returns i32

  ret 42
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Should parse @contract with no params: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.contracts[0].params.len(), 0);
    }

    #[test]
    fn test_parse_all_integer_types() {
        let source = r#"
@node test_integers
@params a:i8 b:i16 c:i32 d:i64 e:u8 f:u16 g:u32 h:u64
@returns i32

  ret 0
"#;
        let result = parse(source);
        assert!(result.is_ok(), "All integer types should parse: {:?}", result.err());
        let program = result.unwrap();
        let params = &program.nodes[0].params;
        assert_eq!(params[0].ty, Type::I8);
        assert_eq!(params[1].ty, Type::I16);
        assert_eq!(params[2].ty, Type::I32);
        assert_eq!(params[3].ty, Type::I64);
        assert_eq!(params[4].ty, Type::U8);
        assert_eq!(params[5].ty, Type::U16);
        assert_eq!(params[6].ty, Type::U32);
        assert_eq!(params[7].ty, Type::U64);
    }

    #[test]
    fn test_parse_char_type() {
        let source = r#"
@node test_char
@params c:char
@returns char

  ret c
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Char type should parse: {:?}", result.err());
        let program = result.unwrap();
        assert_eq!(program.nodes[0].params[0].ty, Type::Char);
        assert_eq!(program.nodes[0].returns, Type::Char);
    }

    #[test]
    fn test_parse_ptr_type() {
        let source = r#"
@node test_ptr
@params ptr:*i32 buf:*u8
@returns *i32

  ret ptr
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Pointer types should parse: {:?}", result.err());
        let program = result.unwrap();
        match &program.nodes[0].params[0].ty {
            Type::Ptr(inner) => assert_eq!(**inner, Type::I32),
            _ => panic!("Expected pointer type"),
        }
        match &program.nodes[0].params[1].ty {
            Type::Ptr(inner) => assert_eq!(**inner, Type::U8),
            _ => panic!("Expected pointer type"),
        }
    }

    #[test]
    fn test_parse_nested_ptr_type() {
        let source = r#"
@node test_nested_ptr
@params pp:**i32
@returns **i32

  ret pp
"#;
        let result = parse(source);
        assert!(result.is_ok(), "Nested pointer types should parse: {:?}", result.err());
        let program = result.unwrap();
        match &program.nodes[0].params[0].ty {
            Type::Ptr(inner) => match &**inner {
                Type::Ptr(innermost) => assert_eq!(**innermost, Type::I32),
                _ => panic!("Expected nested pointer type"),
            },
            _ => panic!("Expected pointer type"),
        }
    }

    // ==================== Refined Types Tests (v0.8+) ====================

    #[test]
    fn test_parse_refined_type_simple() {
        // Basic refined type: @type nz_i32 i32 where self != 0
        let source = r#"
@type nz_i32 i32 where self != 0

@node test
@params
@returns i32

  ret 1
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Simple refined type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name.name, "nz_i32");
        assert_eq!(program.type_defs[0].base_type, Type::I32);
        assert!(program.type_defs[0].params.is_empty());
    }

    #[test]
    fn test_parse_refined_type_positive() {
        // Positive integer type: @type pos_i32 i32 where self > 0
        let source = r#"
@type pos_i32 i32 where self > 0

@node test
@params
@returns i32

  ret 1
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Positive refined type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name.name, "pos_i32");
    }

    #[test]
    fn test_parse_refined_type_with_params() {
        // Parameterized refined type: @type index[N] u64 where self < N
        let source = r#"
@type index[N] u64 where self < N

@node test
@params
@returns i32

  ret 1
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Parameterized refined type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name.name, "index");
        assert_eq!(program.type_defs[0].params.len(), 1);
        assert_eq!(program.type_defs[0].params[0].name, "N");
        assert_eq!(program.type_defs[0].base_type, Type::U64);
    }

    #[test]
    fn test_parse_refined_type_compact() {
        // Compact syntax: @#t nz_i32 i32 where self != 0
        let source = r#"
@#t nz_i32 i32 where self != 0

@node test
@params
@returns i32

  ret 1
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Compact refined type syntax should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name.name, "nz_i32");
    }

    #[test]
    fn test_parse_refined_type_complex_constraint() {
        // Complex constraint: @type bounded_i32 i32 where self >= 0 && self <= 100
        let source = r#"
@type bounded_i32 i32 where self >= 0 && self <= 100

@node test
@params
@returns i32

  ret 1
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Complex constraint refined type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name.name, "bounded_i32");
    }

    #[test]
    fn test_parse_multiple_refined_types() {
        // Multiple refined types
        let source = r#"
@type nz_i32 i32 where self != 0
@type pos_i32 i32 where self > 0
@type neg_i32 i32 where self < 0

@node test
@params
@returns i32

  ret 1
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Multiple refined types should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.type_defs.len(), 3);
        assert_eq!(program.type_defs[0].name.name, "nz_i32");
        assert_eq!(program.type_defs[1].name.name, "pos_i32");
        assert_eq!(program.type_defs[2].name.name, "neg_i32");
    }

    #[test]
    fn test_parse_self_keyword_in_constraint() {
        // Verify self is parsed as SelfRef in constraint expression
        let source = r#"
@type nz_i32 i32 where self != 0

@node test
@params
@returns i32

  ret 1
"#;
        let result = parse(source);
        assert!(result.is_ok());
        let program = result.unwrap();

        // Check that the constraint contains SelfRef
        match &program.type_defs[0].constraint {
            Expr::Binary { left, .. } => match &**left {
                Expr::SelfRef => {} // Expected
                other => panic!("Expected SelfRef, got {:?}", other),
            },
            other => panic!("Expected Binary expression, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_option_type() {
        // Function with Option<i32> parameter
        let source = r#"
@node maybe_double
@params x:Option<i32>
@returns Option<i32>

  ret 0
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Option type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.nodes.len(), 1);
        let param_type = &program.nodes[0].params[0].ty;
        assert!(
            matches!(param_type, Type::Option(inner) if matches!(&**inner, Type::I32)),
            "Expected Option<i32>, got {:?}",
            param_type
        );
    }

    #[test]
    fn test_parse_result_type() {
        // Function with Result<i32, i32> return type
        let source = r#"
@node divide
@params a:i32 b:i32
@returns Result<i32, i32>

  ret 0
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Result type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        assert_eq!(program.nodes.len(), 1);
        let ret_type = &program.nodes[0].returns;
        assert!(
            matches!(ret_type, Type::Result { ok, err } if matches!(&**ok, Type::I32) && matches!(&**err, Type::I32)),
            "Expected Result<i32, i32>, got {:?}",
            ret_type
        );
    }

    #[test]
    fn test_parse_nested_generic_types() {
        // Nested generic types: Option<Result<i32, bool>>
        let source = r#"
@node complex
@params
@returns Option<Result<i32, bool>>

  ret 0
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Nested generic types should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        let ret_type = &program.nodes[0].returns;
        match ret_type {
            Type::Option(inner) => match &**inner {
                Type::Result { ok, err } => {
                    assert!(matches!(&**ok, Type::I32));
                    assert!(matches!(&**err, Type::Bool));
                }
                other => panic!("Expected Result inside Option, got {:?}", other),
            },
            other => panic!("Expected Option, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_vector_type() {
        // Vector<f64> parameter
        let source = r#"
@node sum_vector
@params v:Vector<f64>
@returns f64

  ret 0.0
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Vector type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        let param_type = &program.nodes[0].params[0].ty;
        assert!(
            matches!(param_type, Type::Vector(inner) if matches!(&**inner, Type::F64)),
            "Expected Vector<f64>, got {:?}",
            param_type
        );
    }

    #[test]
    fn test_parse_slice_type() {
        // Slice<i32> parameter
        let source = r#"
@node process_slice
@params s:Slice<i32>
@returns i32

  ret 0
"#;
        let result = parse(source);
        assert!(
            result.is_ok(),
            "Slice type should parse: {:?}",
            result.err()
        );
        let program = result.unwrap();
        let param_type = &program.nodes[0].params[0].ty;
        assert!(
            matches!(param_type, Type::Slice(inner) if matches!(&**inner, Type::I32)),
            "Expected Slice<i32>, got {:?}",
            param_type
        );
    }
}
