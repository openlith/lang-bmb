//! BMB Grammar Export
//!
//! Export BMB grammar to standard formats for external tool integration.
//!
//! "Omission is guessing, and guessing is error."
//! - Precise grammar definitions enable reliable code generation.

use std::collections::HashMap;

/// Grammar version for compatibility tracking
pub const GRAMMAR_VERSION: &str = "0.1.0";

/// Grammar rule representation
#[derive(Debug, Clone)]
pub struct GrammarRule {
    pub name: String,
    pub definition: String,
    pub description: Option<String>,
}

/// Complete BMB grammar definition
#[derive(Debug, Clone)]
pub struct BmbGrammar {
    pub version: String,
    pub rules: Vec<GrammarRule>,
}

impl Default for BmbGrammar {
    fn default() -> Self {
        Self::new()
    }
}

impl BmbGrammar {
    /// Create the complete BMB grammar
    pub fn new() -> Self {
        let rules = vec![
            // Program structure
            GrammarRule {
                name: "program".to_string(),
                definition: "node*".to_string(),
                description: Some("A BMB program consists of zero or more node definitions".to_string()),
            },
            GrammarRule {
                name: "node".to_string(),
                definition: "'@node' IDENT params returns contracts body".to_string(),
                description: Some("A node (function) definition with contracts".to_string()),
            },
            // Parameters
            GrammarRule {
                name: "params".to_string(),
                definition: "'@params' param*".to_string(),
                description: Some("Parameter declarations".to_string()),
            },
            GrammarRule {
                name: "param".to_string(),
                definition: "IDENT ':' type_name".to_string(),
                description: Some("A single parameter with type".to_string()),
            },
            // Returns
            GrammarRule {
                name: "returns".to_string(),
                definition: "'@returns' type_name".to_string(),
                description: Some("Return type declaration".to_string()),
            },
            // Contracts
            GrammarRule {
                name: "contracts".to_string(),
                definition: "(pre | post)*".to_string(),
                description: Some("Pre and post condition contracts".to_string()),
            },
            GrammarRule {
                name: "pre".to_string(),
                definition: "'@pre' expr".to_string(),
                description: Some("Precondition contract".to_string()),
            },
            GrammarRule {
                name: "post".to_string(),
                definition: "'@post' expr".to_string(),
                description: Some("Postcondition contract".to_string()),
            },
            // Body
            GrammarRule {
                name: "body".to_string(),
                definition: "(label | stmt)+".to_string(),
                description: Some("Function body with labels and statements".to_string()),
            },
            GrammarRule {
                name: "label".to_string(),
                definition: "'_' (ALPHA | DIGIT | '_')+ ':'".to_string(),
                description: Some("Label for jump targets".to_string()),
            },
            GrammarRule {
                name: "stmt".to_string(),
                definition: "opcode operand*".to_string(),
                description: Some("An instruction statement".to_string()),
            },
            // Opcodes
            GrammarRule {
                name: "opcode".to_string(),
                definition: "'add' | 'sub' | 'mul' | 'div' | 'mod' | 'eq' | 'ne' | 'lt' | 'le' | 'gt' | 'ge' | 'ret' | 'jmp' | 'jif' | 'call' | 'mov' | 'load' | 'store'".to_string(),
                description: Some("Available opcodes".to_string()),
            },
            // Operands
            GrammarRule {
                name: "operand".to_string(),
                definition: "register | label_ref | float_literal | int_literal | IDENT".to_string(),
                description: Some("Instruction operand".to_string()),
            },
            GrammarRule {
                name: "register".to_string(),
                definition: "'%' (ALPHA | DIGIT | '_')+".to_string(),
                description: Some("Register reference".to_string()),
            },
            GrammarRule {
                name: "label_ref".to_string(),
                definition: "'_' (ALPHA | DIGIT | '_')+".to_string(),
                description: Some("Label reference (without colon)".to_string()),
            },
            // Types
            GrammarRule {
                name: "type_name".to_string(),
                definition: "'i32' | 'i64' | 'f32' | 'f64' | 'bool'".to_string(),
                description: Some("Available types".to_string()),
            },
            // Expressions
            GrammarRule {
                name: "expr".to_string(),
                definition: "or_expr".to_string(),
                description: Some("Contract expression".to_string()),
            },
            GrammarRule {
                name: "or_expr".to_string(),
                definition: "and_expr ('||' and_expr)*".to_string(),
                description: Some("Logical OR expression".to_string()),
            },
            GrammarRule {
                name: "and_expr".to_string(),
                definition: "comparison ('&&' comparison)*".to_string(),
                description: Some("Logical AND expression".to_string()),
            },
            GrammarRule {
                name: "comparison".to_string(),
                definition: "term (comp_op term)?".to_string(),
                description: Some("Comparison expression".to_string()),
            },
            GrammarRule {
                name: "comp_op".to_string(),
                definition: "'==' | '!=' | '<=' | '>=' | '<' | '>'".to_string(),
                description: Some("Comparison operators".to_string()),
            },
            GrammarRule {
                name: "term".to_string(),
                definition: "factor (('+' | '-') factor)*".to_string(),
                description: Some("Additive term".to_string()),
            },
            GrammarRule {
                name: "factor".to_string(),
                definition: "unary (('*' | '/' | '%') unary)*".to_string(),
                description: Some("Multiplicative factor".to_string()),
            },
            GrammarRule {
                name: "unary".to_string(),
                definition: "('!' | '-')? primary".to_string(),
                description: Some("Unary expression".to_string()),
            },
            GrammarRule {
                name: "primary".to_string(),
                definition: "'(' expr ')' | float_literal | int_literal | bool_literal | 'ret' | IDENT".to_string(),
                description: Some("Primary expression".to_string()),
            },
            // Literals
            GrammarRule {
                name: "float_literal".to_string(),
                definition: "'-'? DIGIT+ '.' DIGIT+".to_string(),
                description: Some("Floating-point literal".to_string()),
            },
            GrammarRule {
                name: "int_literal".to_string(),
                definition: "'-'? DIGIT+".to_string(),
                description: Some("Integer literal".to_string()),
            },
            GrammarRule {
                name: "bool_literal".to_string(),
                definition: "'true' | 'false'".to_string(),
                description: Some("Boolean literal".to_string()),
            },
            // Terminals
            GrammarRule {
                name: "IDENT".to_string(),
                definition: "ALPHA (ALPHA | DIGIT | '_')*".to_string(),
                description: Some("Identifier (not starting with underscore)".to_string()),
            },
            GrammarRule {
                name: "ALPHA".to_string(),
                definition: "[a-zA-Z]".to_string(),
                description: Some("Alphabetic character".to_string()),
            },
            GrammarRule {
                name: "DIGIT".to_string(),
                definition: "[0-9]".to_string(),
                description: Some("Numeric digit".to_string()),
            },
            GrammarRule {
                name: "WHITESPACE".to_string(),
                definition: "' ' | '\\t' | '\\r' | '\\n'".to_string(),
                description: Some("Whitespace (ignored)".to_string()),
            },
            GrammarRule {
                name: "COMMENT".to_string(),
                definition: "'#' (!NEWLINE ANY)*".to_string(),
                description: Some("Comment (to end of line)".to_string()),
            },
        ];

        BmbGrammar {
            version: GRAMMAR_VERSION.to_string(),
            rules,
        }
    }

    /// Export grammar to EBNF format
    pub fn to_ebnf(&self) -> String {
        let mut output = String::new();

        output.push_str("(* BMB Grammar - Extended Backus-Naur Form *)\n");
        output.push_str(&format!("(* Version: {} *)\n", self.version));
        output.push_str("(* \"Omission is guessing, and guessing is error.\" *)\n\n");

        for rule in &self.rules {
            if let Some(ref desc) = rule.description {
                output.push_str(&format!("(* {} *)\n", desc));
            }
            output.push_str(&format!("{} = {} ;\n\n", rule.name, rule.definition));
        }

        output
    }

    /// Export grammar to JSON Schema format
    pub fn to_json_schema(&self) -> String {
        let mut schema = serde_json::json!({
            "$schema": "http://json-schema.org/draft-07/schema#",
            "title": "BMB Grammar",
            "version": self.version,
            "description": "BMB (Bare-Metal-Banter) grammar definition",
            "definitions": {}
        });

        let definitions = schema.get_mut("definitions").unwrap();

        for rule in &self.rules {
            let mut rule_obj = serde_json::json!({
                "definition": rule.definition
            });
            if let Some(ref desc) = rule.description {
                rule_obj["description"] = serde_json::Value::String(desc.clone());
            }
            definitions[&rule.name] = rule_obj;
        }

        serde_json::to_string_pretty(&schema).unwrap_or_else(|_| "{}".to_string())
    }

    /// Export grammar to GBNF format (llama.cpp compatible)
    pub fn to_gbnf(&self) -> String {
        let mut output = String::new();

        output.push_str("# BMB Grammar - GBNF (llama.cpp compatible)\n");
        output.push_str(&format!("# Version: {}\n", self.version));
        output.push_str("# \"Omission is guessing, and guessing is error.\"\n\n");

        // Root rule
        output.push_str("root ::= program\n\n");

        // Convert each rule to GBNF format
        for rule in &self.rules {
            let gbnf_def = self.convert_to_gbnf(&rule.definition);
            output.push_str(&format!("{} ::= {}\n", rule.name, gbnf_def));
        }

        // Add whitespace handling
        output.push_str("\n# Implicit whitespace\n");
        output.push_str("ws ::= [ \\t\\r\\n]*\n");

        output
    }

    /// Convert EBNF-style definition to GBNF format
    fn convert_to_gbnf(&self, definition: &str) -> String {
        definition
            // Handle repetition
            .replace("*", " *")
            .replace("+", " +")
            .replace("?", " ?")
            // Handle character classes
            .replace("[a-zA-Z]", "[a-zA-Z]")
            .replace("[0-9]", "[0-9]")
            // Handle string literals - wrap in quotes for GBNF
            .replace("'@node'", "\"@node\"")
            .replace("'@params'", "\"@params\"")
            .replace("'@returns'", "\"@returns\"")
            .replace("'@pre'", "\"@pre\"")
            .replace("'@post'", "\"@post\"")
            .replace("'%'", "\"%\"")
            .replace("'_'", "\"_\"")
            .replace("':'", "\":\"")
            .replace("'||'", "\"||\"")
            .replace("'&&'", "\"&&\"")
            .replace("'=='", "\"==\"")
            .replace("'!='", "\"!=\"")
            .replace("'<='", "\"<=\"")
            .replace("'>='", "\">=\"")
            .replace("'<'", "\"<\"")
            .replace("'>'", "\">\"")
            .replace("'+'", "\"+\"")
            .replace("'-'", "\"-\"")
            .replace("'*'", "\"*\"")
            .replace("'/'", "\"/\"")
            .replace("'!'", "\"!\"")
            .replace("'('", "\"(\"")
            .replace("')'", "\")\"")
            .replace("'.'", "\".\"")
            .replace("' '", "\" \"")
            .replace("'\\t'", "\"\\t\"")
            .replace("'\\r'", "\"\\r\"")
            .replace("'\\n'", "\"\\n\"")
            .replace("'#'", "\"#\"")
            // Handle keywords
            .replace("'add'", "\"add\"")
            .replace("'sub'", "\"sub\"")
            .replace("'mul'", "\"mul\"")
            .replace("'div'", "\"div\"")
            .replace("'mod'", "\"mod\"")
            .replace("'eq'", "\"eq\"")
            .replace("'ne'", "\"ne\"")
            .replace("'lt'", "\"lt\"")
            .replace("'le'", "\"le\"")
            .replace("'gt'", "\"gt\"")
            .replace("'ge'", "\"ge\"")
            .replace("'ret'", "\"ret\"")
            .replace("'jmp'", "\"jmp\"")
            .replace("'jif'", "\"jif\"")
            .replace("'call'", "\"call\"")
            .replace("'mov'", "\"mov\"")
            .replace("'load'", "\"load\"")
            .replace("'store'", "\"store\"")
            .replace("'i32'", "\"i32\"")
            .replace("'i64'", "\"i64\"")
            .replace("'f32'", "\"f32\"")
            .replace("'f64'", "\"f64\"")
            .replace("'bool'", "\"bool\"")
            .replace("'true'", "\"true\"")
            .replace("'false'", "\"false\"")
    }

    /// Export grammar to a map of all formats
    pub fn export_all(&self) -> HashMap<String, String> {
        let mut exports = HashMap::new();
        exports.insert("ebnf".to_string(), self.to_ebnf());
        exports.insert("json".to_string(), self.to_json_schema());
        exports.insert("gbnf".to_string(), self.to_gbnf());
        exports
    }
}

/// Validate BMB source code quickly (for external tools)
pub fn validate(source: &str) -> ValidationResult {
    use crate::contracts;
    use crate::parser;
    use crate::types;

    // Parse
    let ast = match parser::parse(source) {
        Ok(ast) => ast,
        Err(e) => {
            return ValidationResult {
                valid: false,
                level: ValidationLevel::None,
                errors: vec![e.to_string()],
                warnings: vec![],
            }
        }
    };

    // Typecheck
    let typed = match types::typecheck(&ast) {
        Ok(typed) => typed,
        Err(e) => {
            return ValidationResult {
                valid: false,
                level: ValidationLevel::Stone,
                errors: vec![e.to_string()],
                warnings: vec![],
            }
        }
    };

    // Contract verification
    match contracts::verify(&typed) {
        Ok(_) => ValidationResult {
            valid: true,
            level: ValidationLevel::Silver,
            errors: vec![],
            warnings: vec![],
        },
        Err(e) => ValidationResult {
            valid: false,
            level: ValidationLevel::Bronze,
            errors: vec![e.to_string()],
            warnings: vec![],
        },
    }
}

/// Validation result for external tools
#[derive(Debug, Clone)]
pub struct ValidationResult {
    pub valid: bool,
    pub level: ValidationLevel,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

/// Validation level achieved
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValidationLevel {
    /// No validation passed
    None,
    /// Parsing succeeded
    Stone,
    /// Type checking passed
    Bronze,
    /// Contract verification passed
    Silver,
}

impl std::fmt::Display for ValidationLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationLevel::None => write!(f, "None"),
            ValidationLevel::Stone => write!(f, "Stone (Level 0)"),
            ValidationLevel::Bronze => write!(f, "Bronze (Level 1)"),
            ValidationLevel::Silver => write!(f, "Silver (Level 2)"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_grammar_creation() {
        let grammar = BmbGrammar::new();
        assert_eq!(grammar.version, GRAMMAR_VERSION);
        assert!(!grammar.rules.is_empty());
    }

    #[test]
    fn test_ebnf_export() {
        let grammar = BmbGrammar::new();
        let ebnf = grammar.to_ebnf();

        assert!(ebnf.contains("BMB Grammar"));
        assert!(ebnf.contains("program ="));
        assert!(ebnf.contains("node ="));
        assert!(ebnf.contains("opcode ="));
    }

    #[test]
    fn test_json_schema_export() {
        let grammar = BmbGrammar::new();
        let json = grammar.to_json_schema();

        assert!(json.contains("$schema"));
        assert!(json.contains("BMB Grammar"));
        assert!(json.contains("definitions"));
        assert!(json.contains("program"));
    }

    #[test]
    fn test_gbnf_export() {
        let grammar = BmbGrammar::new();
        let gbnf = grammar.to_gbnf();

        assert!(gbnf.contains("root ::= program"));
        assert!(gbnf.contains("node ::="));
        assert!(gbnf.contains("opcode ::="));
    }

    #[test]
    fn test_validation_valid_code() {
        let source = r#"
@node sum
@params a:i32 b:i32
@returns i32
@pre true
@post true

  add %r a b
  ret %r
"#;
        let result = validate(source);
        assert!(result.valid, "Validation failed: {:?}", result.errors);
        assert_eq!(result.level, ValidationLevel::Silver);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_validation_parse_error() {
        let source = "@node @invalid";
        let result = validate(source);
        assert!(!result.valid);
        assert_eq!(result.level, ValidationLevel::None);
        assert!(!result.errors.is_empty());
    }

    #[test]
    fn test_export_all() {
        let grammar = BmbGrammar::new();
        let exports = grammar.export_all();

        assert!(exports.contains_key("ebnf"));
        assert!(exports.contains_key("json"));
        assert!(exports.contains_key("gbnf"));
    }
}
