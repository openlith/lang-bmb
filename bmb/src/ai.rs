//! BMB AI Integration Module
//!
//! Provides interfaces for AI-guided code generation with grammar-constrained decoding.
//!
//! "Omission is guessing, and guessing is error."
//! - By constraining the AI to valid grammar, we eliminate syntax errors entirely.
//!
//! This module enables:
//! 1. Grammar-constrained token prediction
//! 2. Partial program validation
//! 3. Next-token guidance based on grammar state
//! 4. Incremental verification during generation

use std::collections::HashSet;

use crate::parser;
use crate::{BmbError, Result};

/// Helper function to create a parse error
fn parse_error(message: String) -> BmbError {
    BmbError::ParseError {
        line: 0,
        column: 0,
        message,
    }
}

/// Grammar state tracker for constrained decoding
///
/// Tracks the current position in the grammar to determine valid next tokens.
#[derive(Debug, Clone, PartialEq)]
pub enum GrammarState {
    /// Starting state, expecting @node
    Start,
    /// After @node, expecting identifier
    ExpectingNodeName,
    /// After node name, expecting @params
    ExpectingParams,
    /// Inside @params, expecting parameter or @returns
    InsideParams,
    /// Expecting parameter type after colon
    ExpectingParamType,
    /// After @params, expecting @returns
    ExpectingReturns,
    /// After @returns, expecting type
    ExpectingReturnType,
    /// After return type, expecting @pre, @post, or body
    ExpectingContractOrBody,
    /// Inside @pre expression
    InsidePrecondition,
    /// Inside @post expression
    InsidePostcondition,
    /// Inside function body, expecting instruction
    InsideBody,
    /// Expecting opcode
    ExpectingOpcode,
    /// Expecting operand (register, identifier, literal, or label)
    ExpectingOperand,
    /// Complete node, can start new node or end
    NodeComplete,
}

/// Token categories for constrained decoding
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenCategory {
    /// Keywords like @node, @params, @returns, @pre, @post
    Keyword,
    /// Type names: i32, i64, f32, f64, bool
    TypeName,
    /// Opcodes: add, sub, mul, div, etc.
    Opcode,
    /// Identifier (function name, parameter name)
    Identifier,
    /// Register (%name)
    Register,
    /// Integer literal
    IntLiteral,
    /// Float literal
    FloatLiteral,
    /// Boolean literal (true, false)
    BoolLiteral,
    /// Label definition (_name:)
    LabelDef,
    /// Label reference (_name)
    LabelRef,
    /// Operators for expressions (==, !=, <, >, etc.)
    Operator,
    /// Colon separator
    Colon,
    /// End of input
    EndOfInput,
}

/// Valid tokens for the current grammar state
pub fn valid_tokens(state: &GrammarState) -> HashSet<TokenCategory> {
    let mut tokens = HashSet::new();

    match state {
        GrammarState::Start | GrammarState::NodeComplete => {
            tokens.insert(TokenCategory::Keyword); // @node
            tokens.insert(TokenCategory::EndOfInput);
        }
        GrammarState::ExpectingNodeName => {
            tokens.insert(TokenCategory::Identifier);
        }
        GrammarState::ExpectingParams => {
            tokens.insert(TokenCategory::Keyword); // @params
        }
        GrammarState::InsideParams => {
            tokens.insert(TokenCategory::Identifier); // parameter name
            tokens.insert(TokenCategory::Keyword); // @returns
        }
        GrammarState::ExpectingParamType => {
            tokens.insert(TokenCategory::TypeName);
        }
        GrammarState::ExpectingReturns => {
            tokens.insert(TokenCategory::Keyword); // @returns
        }
        GrammarState::ExpectingReturnType => {
            tokens.insert(TokenCategory::TypeName);
        }
        GrammarState::ExpectingContractOrBody => {
            tokens.insert(TokenCategory::Keyword); // @pre, @post
            tokens.insert(TokenCategory::Opcode); // body start
            tokens.insert(TokenCategory::LabelDef);
        }
        GrammarState::InsidePrecondition | GrammarState::InsidePostcondition => {
            tokens.insert(TokenCategory::Identifier);
            tokens.insert(TokenCategory::IntLiteral);
            tokens.insert(TokenCategory::FloatLiteral);
            tokens.insert(TokenCategory::BoolLiteral);
            tokens.insert(TokenCategory::Operator);
            // ret keyword in postcondition
            if matches!(state, GrammarState::InsidePostcondition) {
                tokens.insert(TokenCategory::Keyword); // ret
            }
        }
        GrammarState::InsideBody => {
            tokens.insert(TokenCategory::Opcode);
            tokens.insert(TokenCategory::LabelDef);
            tokens.insert(TokenCategory::Keyword); // @node for next function
            tokens.insert(TokenCategory::EndOfInput);
        }
        GrammarState::ExpectingOpcode => {
            tokens.insert(TokenCategory::Opcode);
        }
        GrammarState::ExpectingOperand => {
            tokens.insert(TokenCategory::Register);
            tokens.insert(TokenCategory::Identifier);
            tokens.insert(TokenCategory::IntLiteral);
            tokens.insert(TokenCategory::FloatLiteral);
            tokens.insert(TokenCategory::LabelRef);
        }
    }

    tokens
}

/// Get list of valid keywords for current state
pub fn valid_keywords(state: &GrammarState) -> Vec<&'static str> {
    match state {
        GrammarState::Start | GrammarState::NodeComplete => vec!["@node"],
        GrammarState::ExpectingParams => vec!["@params"],
        GrammarState::InsideParams => vec!["@returns"],
        GrammarState::ExpectingReturns => vec!["@returns"],
        GrammarState::ExpectingContractOrBody => vec!["@pre", "@post"],
        GrammarState::InsideBody => vec!["@node"],
        GrammarState::InsidePostcondition => vec!["ret"],
        _ => vec![],
    }
}

/// Get list of valid type names
pub fn valid_types() -> Vec<&'static str> {
    vec!["i32", "i64", "f32", "f64", "bool"]
}

/// Get list of valid opcodes
pub fn valid_opcodes() -> Vec<&'static str> {
    vec![
        "add", "sub", "mul", "div", "mod",
        "eq", "ne", "lt", "le", "gt", "ge",
        "ret", "jmp", "jif", "call",
        "mov", "load", "store",
    ]
}

/// Get list of valid comparison operators
pub fn valid_operators() -> Vec<&'static str> {
    vec!["==", "!=", "<", "<=", ">", ">=", "&&", "||", "+", "-", "*", "/", "%"]
}

/// Constrained decoder for BMB code generation
pub struct ConstrainedDecoder {
    /// Current grammar state
    state: GrammarState,
    /// Partial source code being built
    source: String,
    /// Current indentation level
    indent: usize,
    /// Track if we're in a contract expression
    in_expr: bool,
    /// Expected operand count for current instruction
    expected_operands: usize,
    /// Current operand count
    current_operands: usize,
}

impl ConstrainedDecoder {
    /// Create a new constrained decoder
    pub fn new() -> Self {
        Self {
            state: GrammarState::Start,
            source: String::new(),
            indent: 0,
            in_expr: false,
            expected_operands: 0,
            current_operands: 0,
        }
    }

    /// Get current grammar state
    pub fn state(&self) -> &GrammarState {
        &self.state
    }

    /// Get valid token categories for next position
    pub fn valid_next_tokens(&self) -> HashSet<TokenCategory> {
        valid_tokens(&self.state)
    }

    /// Get valid concrete tokens for next position
    pub fn valid_concrete_tokens(&self) -> Vec<String> {
        let mut tokens = Vec::new();

        for keyword in valid_keywords(&self.state) {
            tokens.push(keyword.to_string());
        }

        match &self.state {
            GrammarState::ExpectingParamType | GrammarState::ExpectingReturnType => {
                tokens.extend(valid_types().iter().map(|s| s.to_string()));
            }
            GrammarState::ExpectingOpcode |
            GrammarState::ExpectingContractOrBody |
            GrammarState::InsideBody => {
                tokens.extend(valid_opcodes().iter().map(|s| s.to_string()));
            }
            GrammarState::InsidePrecondition | GrammarState::InsidePostcondition => {
                tokens.extend(valid_operators().iter().map(|s| s.to_string()));
            }
            _ => {}
        }

        tokens
    }

    /// Attempt to add a token to the partial program
    pub fn add_token(&mut self, token: &str) -> Result<()> {
        // Validate and transition state based on token
        match &self.state {
            GrammarState::Start | GrammarState::NodeComplete => {
                if token == "@node" {
                    self.source.push_str("@node ");
                    self.state = GrammarState::ExpectingNodeName;
                    Ok(())
                } else {
                    Err(parse_error(format!("Expected @node, got '{}'", token)))
                }
            }
            GrammarState::ExpectingNodeName => {
                if is_valid_identifier(token) {
                    self.source.push_str(token);
                    self.source.push('\n');
                    self.state = GrammarState::ExpectingParams;
                    Ok(())
                } else {
                    Err(parse_error(format!("Invalid identifier: '{}'", token)))
                }
            }
            GrammarState::ExpectingParams => {
                if token == "@params" {
                    self.source.push_str("@params");
                    self.state = GrammarState::InsideParams;
                    Ok(())
                } else {
                    Err(parse_error(format!("Expected @params, got '{}'", token)))
                }
            }
            GrammarState::InsideParams => {
                if token == "@returns" {
                    self.source.push('\n');
                    self.source.push_str("@returns ");
                    self.state = GrammarState::ExpectingReturnType;
                    Ok(())
                } else if is_valid_identifier(token) {
                    self.source.push(' ');
                    self.source.push_str(token);
                    self.source.push(':');
                    self.state = GrammarState::ExpectingParamType;
                    Ok(())
                } else {
                    Err(parse_error(format!("Expected parameter or @returns, got '{}'", token)))
                }
            }
            GrammarState::ExpectingParamType => {
                if valid_types().contains(&token) {
                    self.source.push_str(token);
                    self.state = GrammarState::InsideParams;
                    Ok(())
                } else {
                    Err(parse_error(format!("Invalid type: '{}'", token)))
                }
            }
            GrammarState::ExpectingReturnType => {
                if valid_types().contains(&token) {
                    self.source.push_str(token);
                    self.source.push('\n');
                    self.state = GrammarState::ExpectingContractOrBody;
                    Ok(())
                } else {
                    Err(parse_error(format!("Invalid return type: '{}'", token)))
                }
            }
            GrammarState::ExpectingContractOrBody => {
                if token == "@pre" {
                    self.source.push_str("@pre ");
                    self.state = GrammarState::InsidePrecondition;
                    self.in_expr = true;
                    Ok(())
                } else if token == "@post" {
                    self.source.push_str("@post ");
                    self.state = GrammarState::InsidePostcondition;
                    self.in_expr = true;
                    Ok(())
                } else if valid_opcodes().contains(&token) || token.starts_with('_') {
                    // Start of body
                    self.source.push('\n');
                    self.add_instruction_token(token)
                } else {
                    Err(parse_error(format!("Expected @pre, @post, or instruction, got '{}'", token)))
                }
            }
            GrammarState::InsidePrecondition => {
                self.add_expression_token(token, GrammarState::ExpectingContractOrBody)
            }
            GrammarState::InsidePostcondition => {
                self.add_expression_token(token, GrammarState::ExpectingContractOrBody)
            }
            GrammarState::InsideBody | GrammarState::ExpectingOpcode => {
                if token == "@node" {
                    self.source.push_str("\n@node ");
                    self.state = GrammarState::ExpectingNodeName;
                    Ok(())
                } else {
                    self.add_instruction_token(token)
                }
            }
            GrammarState::ExpectingOperand => {
                self.add_operand_token(token)
            }
            _ => {
                Err(parse_error(format!("Unexpected token '{}' in state {:?}", token, self.state)))
            }
        }
    }

    fn add_instruction_token(&mut self, token: &str) -> Result<()> {
        if token.starts_with('_') && token.ends_with(':') {
            // Label definition
            self.source.push_str("  ");
            self.source.push_str(token);
            self.source.push('\n');
            self.state = GrammarState::InsideBody;
            Ok(())
        } else if valid_opcodes().contains(&token) {
            self.source.push_str("  ");
            self.source.push_str(token);
            self.expected_operands = expected_operand_count(token);
            self.current_operands = 0;
            if self.expected_operands > 0 {
                self.source.push(' ');
                self.state = GrammarState::ExpectingOperand;
            } else {
                self.source.push('\n');
                self.state = GrammarState::InsideBody;
            }
            Ok(())
        } else {
            Err(parse_error(format!("Expected opcode or label, got '{}'", token)))
        }
    }

    fn add_operand_token(&mut self, token: &str) -> Result<()> {
        // Validate operand
        if !is_valid_operand(token) {
            return Err(parse_error(format!("Invalid operand: '{}'", token)));
        }

        self.source.push_str(token);
        self.current_operands += 1;

        if self.current_operands >= self.expected_operands {
            self.source.push('\n');
            self.state = GrammarState::InsideBody;
        } else {
            self.source.push(' ');
        }

        Ok(())
    }

    fn add_expression_token(&mut self, token: &str, next_state: GrammarState) -> Result<()> {
        // Simple expression handling - in practice would need proper expression parsing
        if token == "\n" || token == "EXPR_END" {
            self.source.push('\n');
            self.state = next_state;
            self.in_expr = false;
        } else {
            self.source.push_str(token);
            self.source.push(' ');
        }
        Ok(())
    }

    /// Complete the current program and validate
    pub fn complete(&mut self) -> Result<String> {
        let source = self.source.clone();

        // Try to parse the source to validate it
        parser::parse(&source)?;

        Ok(source)
    }

    /// Get the current partial source
    pub fn partial_source(&self) -> &str {
        &self.source
    }

    /// Validate partial source at current state
    pub fn validate_partial(&self) -> Result<()> {
        // Check if we're in a valid intermediate state
        match &self.state {
            GrammarState::Start => Ok(()),
            GrammarState::NodeComplete => {
                // Try parsing what we have
                parser::parse(&self.source)?;
                Ok(())
            }
            _ => {
                // In the middle of generation, can't fully validate yet
                Ok(())
            }
        }
    }
}

impl Default for ConstrainedDecoder {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if a string is a valid BMB identifier
fn is_valid_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    // Must start with letter
    let mut chars = s.chars();
    if let Some(first) = chars.next() {
        if !first.is_ascii_alphabetic() {
            return false;
        }
    }

    // Rest can be alphanumeric or underscore
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Check if a string is a valid operand
fn is_valid_operand(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    // Register: starts with %
    if s.starts_with('%') {
        return s.len() > 1 && s[1..].chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    }

    // Label reference: starts with _
    if s.starts_with('_') {
        return s.len() > 1 && s[1..].chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    }

    // Integer literal
    if let Ok(_) = s.parse::<i64>() {
        return true;
    }

    // Float literal
    if let Ok(_) = s.parse::<f64>() {
        return true;
    }

    // Identifier
    is_valid_identifier(s)
}

/// Get expected operand count for an opcode
fn expected_operand_count(opcode: &str) -> usize {
    match opcode {
        "add" | "sub" | "mul" | "div" | "mod" => 3, // dest src1 src2
        "eq" | "ne" | "lt" | "le" | "gt" | "ge" => 3,
        "ret" => 1,
        "jmp" => 1,
        "jif" => 2, // condition label
        "call" => 2, // At least dest and func_name, can have more
        "mov" => 2,
        "load" | "store" => 2,
        _ => 0,
    }
}

/// Verification result for partial programs
#[derive(Debug)]
pub struct PartialVerification {
    /// Whether the partial program is syntactically valid so far
    pub syntax_valid: bool,
    /// Current grammar state
    pub state: GrammarState,
    /// Valid next token categories
    pub valid_next: HashSet<TokenCategory>,
    /// Estimated completion percentage (0.0 - 1.0)
    pub completion: f64,
    /// Error message if syntax_valid is false
    pub error: Option<String>,
}

/// Verify a partial BMB program
pub fn verify_partial(source: &str) -> PartialVerification {
    // Try to parse - if it succeeds, it's complete
    match parser::parse(source) {
        Ok(_) => PartialVerification {
            syntax_valid: true,
            state: GrammarState::NodeComplete,
            valid_next: valid_tokens(&GrammarState::NodeComplete),
            completion: 1.0,
            error: None,
        },
        Err(e) => {
            // Try to determine where we are based on the partial source
            let state = infer_grammar_state(source);
            let valid_next = valid_tokens(&state);

            PartialVerification {
                syntax_valid: !source.is_empty(), // Partial is valid if not empty
                state,
                valid_next,
                completion: estimate_completion(source),
                error: Some(format!("{}", e)),
            }
        }
    }
}

/// Infer the grammar state from partial source
fn infer_grammar_state(source: &str) -> GrammarState {
    let lines: Vec<&str> = source.lines().collect();

    if lines.is_empty() || source.is_empty() {
        return GrammarState::Start;
    }

    // Look at the last non-empty line
    let last_line = lines.iter().rev().find(|l| !l.trim().is_empty());

    match last_line {
        None => GrammarState::Start,
        Some(line) => {
            let trimmed = line.trim();
            if trimmed.starts_with("@node") && !trimmed.contains(' ') {
                GrammarState::ExpectingNodeName
            } else if trimmed.starts_with("@params") {
                GrammarState::InsideParams
            } else if trimmed.starts_with("@returns") && trimmed.split_whitespace().count() == 1 {
                GrammarState::ExpectingReturnType
            } else if trimmed.starts_with("@pre") {
                GrammarState::InsidePrecondition
            } else if trimmed.starts_with("@post") {
                GrammarState::InsidePostcondition
            } else if trimmed.starts_with("  ") || trimmed.starts_with('\t') {
                // Inside body
                GrammarState::InsideBody
            } else {
                GrammarState::ExpectingContractOrBody
            }
        }
    }
}

/// Estimate completion percentage of a program
fn estimate_completion(source: &str) -> f64 {
    // Simple heuristic based on structure
    let has_node = source.contains("@node");
    let has_params = source.contains("@params");
    let has_returns = source.contains("@returns");
    let has_body = source.lines().any(|l| l.starts_with("  ") || l.starts_with('\t'));
    let has_ret = source.contains(" ret ") || source.contains("\tret ");

    let parts = [has_node, has_params, has_returns, has_body, has_ret];
    let completed = parts.iter().filter(|&&x| x).count();

    completed as f64 / parts.len() as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_tokens_start() {
        let tokens = valid_tokens(&GrammarState::Start);
        assert!(tokens.contains(&TokenCategory::Keyword));
        assert!(tokens.contains(&TokenCategory::EndOfInput));
    }

    #[test]
    fn test_valid_identifier() {
        assert!(is_valid_identifier("foo"));
        assert!(is_valid_identifier("bar_baz"));
        assert!(is_valid_identifier("x1"));
        assert!(!is_valid_identifier("1x"));
        assert!(!is_valid_identifier("_foo")); // BMB idents can't start with _
        assert!(!is_valid_identifier(""));
    }

    #[test]
    fn test_valid_operand() {
        assert!(is_valid_operand("%r"));
        assert!(is_valid_operand("%result"));
        assert!(is_valid_operand("_loop"));
        assert!(is_valid_operand("42"));
        assert!(is_valid_operand("-5"));
        assert!(is_valid_operand("3.14"));
        assert!(is_valid_operand("foo"));
        assert!(!is_valid_operand(""));
    }

    #[test]
    fn test_constrained_decoder_simple() {
        let mut decoder = ConstrainedDecoder::new();

        // Build: @node sum\n@params a:i32 b:i32\n@returns i32\n  add %r a b\n  ret %r
        assert!(decoder.add_token("@node").is_ok());
        assert!(decoder.add_token("sum").is_ok());
        assert!(decoder.add_token("@params").is_ok());
        assert!(decoder.add_token("a").is_ok());
        assert!(decoder.add_token("i32").is_ok());
        assert!(decoder.add_token("b").is_ok());
        assert!(decoder.add_token("i32").is_ok());
        assert!(decoder.add_token("@returns").is_ok());
        assert!(decoder.add_token("i32").is_ok());
        assert!(decoder.add_token("add").is_ok());
        assert!(decoder.add_token("%r").is_ok());
        assert!(decoder.add_token("a").is_ok());
        assert!(decoder.add_token("b").is_ok());
        assert!(decoder.add_token("ret").is_ok());
        assert!(decoder.add_token("%r").is_ok());

        // Should be able to complete
        let source = decoder.complete();
        assert!(source.is_ok());
    }

    #[test]
    fn test_verify_partial() {
        let partial = "@node foo\n@params x:i32\n";
        let result = verify_partial(partial);
        assert!(result.completion > 0.0);
        assert!(result.completion < 1.0);
    }

    #[test]
    fn test_infer_grammar_state() {
        assert_eq!(infer_grammar_state(""), GrammarState::Start);
        assert_eq!(infer_grammar_state("@node"), GrammarState::ExpectingNodeName);
        assert_eq!(infer_grammar_state("@node foo\n@params"), GrammarState::InsideParams);
    }

    #[test]
    fn test_estimate_completion() {
        let empty = "";
        assert_eq!(estimate_completion(empty), 0.0);

        let complete = "@node f\n@params\n@returns i32\n  add %r 1 2\n  ret %r\n";
        assert_eq!(estimate_completion(complete), 1.0);

        let partial = "@node f\n@params\n";
        let comp = estimate_completion(partial);
        assert!(comp > 0.0 && comp < 1.0);
    }
}
