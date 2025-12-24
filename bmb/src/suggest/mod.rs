//! Contract Inference Module (v0.14.0)
//!
//! This module provides "suggest-then-confirm" contract inference
//! to reduce boilerplate while preserving the "Omission is guessing" philosophy.
//!
//! ## Design Principle
//!
//! Inference generates **suggestions**, developer explicitly confirms.
//! This maintains BMB's explicit contract philosophy while reducing manual effort.
//!
//! ## Features
//!
//! - **Frame Inference**: Detect memory modifications → suggest `@modifies`
//! - **Postcondition Inference**: Compute strongest postcondition → suggest `@post`
//!
//! ## Usage
//!
//! ```bash
//! bmbc suggest --frame input.bmb      # Suggest @modifies clauses
//! bmbc suggest --post input.bmb       # Suggest @post conditions
//! bmbc suggest --all input.bmb        # Suggest all contracts
//! ```

pub mod frame;
pub mod postcondition;

use crate::ast::{BinaryOp, Expr, UnaryOp};
use crate::types::TypedProgram;

/// A contract suggestion with source location and confidence
#[derive(Debug, Clone)]
pub struct Suggestion {
    /// The node (function) this suggestion applies to
    pub node_name: String,
    /// Type of suggestion
    pub kind: SuggestionKind,
    /// The suggested contract expression
    pub expr: SuggestedExpr,
    /// Confidence level (0.0 - 1.0)
    pub confidence: f64,
    /// Human-readable explanation
    pub explanation: String,
}

/// Kind of contract suggestion
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SuggestionKind {
    /// Frame condition: @modifies
    Frame,
    /// Postcondition: @post
    Postcondition,
    /// Precondition: @pre (future)
    Precondition,
    /// Invariant: @invariant (future)
    Invariant,
}

impl std::fmt::Display for SuggestionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SuggestionKind::Frame => write!(f, "@modifies"),
            SuggestionKind::Postcondition => write!(f, "@post"),
            SuggestionKind::Precondition => write!(f, "@pre"),
            SuggestionKind::Invariant => write!(f, "@invariant"),
        }
    }
}

/// A suggested contract expression
#[derive(Debug, Clone)]
pub enum SuggestedExpr {
    /// Frame: list of modified memory locations
    ModifiesSet(Vec<MemoryLocation>),
    /// Boolean expression for pre/post conditions
    BoolExpr(Expr),
    /// Multiple conjuncted conditions
    Conjunction(Vec<Expr>),
    /// Raw text (for display when AST is complex)
    Text(String),
}

impl SuggestedExpr {
    /// Format the suggestion as BMB code
    pub fn to_bmb_string(&self) -> String {
        match self {
            SuggestedExpr::ModifiesSet(locs) => {
                if locs.is_empty() {
                    "nothing".to_string()
                } else {
                    locs.iter()
                        .map(|l| l.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                }
            }
            SuggestedExpr::BoolExpr(expr) => format_expr(expr),
            SuggestedExpr::Conjunction(exprs) => {
                if exprs.is_empty() {
                    "true".to_string()
                } else {
                    exprs
                        .iter()
                        .map(format_expr)
                        .collect::<Vec<_>>()
                        .join(" && ")
                }
            }
            SuggestedExpr::Text(s) => s.clone(),
        }
    }
}

/// A memory location that may be modified
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MemoryLocation {
    /// A register: %name
    Register(String),
    /// A parameter (by reference): param_name
    Parameter(String),
    /// An array element: arr[idx]
    ArrayElement { base: String, index: String },
    /// A struct field: struct.field
    StructField { base: String, field: String },
    /// Heap memory via Box pointer
    HeapLocation(String),
    /// Global memory (future)
    Global(String),
}

impl std::fmt::Display for MemoryLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemoryLocation::Register(name) => write!(f, "%{}", name),
            MemoryLocation::Parameter(name) => write!(f, "{}", name),
            MemoryLocation::ArrayElement { base, index } => write!(f, "{}[{}]", base, index),
            MemoryLocation::StructField { base, field } => write!(f, "{}.{}", base, field),
            MemoryLocation::HeapLocation(ptr) => write!(f, "*{}", ptr),
            MemoryLocation::Global(name) => write!(f, "global:{}", name),
        }
    }
}

/// Options for contract suggestion
#[derive(Debug, Clone, Default)]
pub struct SuggestOptions {
    /// Suggest frame conditions (@modifies)
    pub frame: bool,
    /// Suggest postconditions (@post)
    pub postcondition: bool,
    /// Suggest preconditions (@pre) - future
    pub precondition: bool,
    /// Minimum confidence threshold (0.0 - 1.0)
    pub min_confidence: f64,
    /// Include explanations in output
    pub verbose: bool,
}

impl SuggestOptions {
    /// Enable all suggestion types
    pub fn all() -> Self {
        Self {
            frame: true,
            postcondition: true,
            precondition: false, // not yet implemented
            min_confidence: 0.5,
            verbose: true,
        }
    }

    /// Enable only frame inference
    pub fn frame_only() -> Self {
        Self {
            frame: true,
            ..Default::default()
        }
    }

    /// Enable only postcondition inference
    pub fn postcondition_only() -> Self {
        Self {
            postcondition: true,
            ..Default::default()
        }
    }
}

/// Result of suggestion analysis
#[derive(Debug, Clone)]
pub struct SuggestResult {
    /// All generated suggestions
    pub suggestions: Vec<Suggestion>,
    /// Nodes that were analyzed
    pub analyzed_nodes: Vec<String>,
    /// Any warnings during analysis
    pub warnings: Vec<String>,
}

impl SuggestResult {
    pub fn new() -> Self {
        Self {
            suggestions: Vec::new(),
            analyzed_nodes: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Filter suggestions by minimum confidence
    pub fn filter_by_confidence(&self, min: f64) -> Vec<&Suggestion> {
        self.suggestions
            .iter()
            .filter(|s| s.confidence >= min)
            .collect()
    }

    /// Get suggestions for a specific node
    pub fn for_node(&self, name: &str) -> Vec<&Suggestion> {
        self.suggestions
            .iter()
            .filter(|s| s.node_name == name)
            .collect()
    }

    /// Format suggestions as BMB code comments
    pub fn format_as_comments(&self) -> String {
        let mut output = String::new();
        let mut current_node = String::new();

        for s in &self.suggestions {
            if s.node_name != current_node {
                if !current_node.is_empty() {
                    output.push('\n');
                }
                output.push_str(&format!("// Suggestions for @node {}\n", s.node_name));
                current_node = s.node_name.clone();
            }

            output.push_str(&format!(
                "// {} {} (confidence: {:.0}%)\n",
                s.kind,
                s.expr.to_bmb_string(),
                s.confidence * 100.0
            ));
        }

        output
    }

    /// Format suggestions as insertable BMB directives
    pub fn format_as_directives(&self) -> String {
        let mut output = String::new();
        let mut current_node = String::new();

        for s in &self.suggestions {
            if s.node_name != current_node {
                if !current_node.is_empty() {
                    output.push('\n');
                }
                output.push_str(&format!("// For @node {}\n", s.node_name));
                current_node = s.node_name.clone();
            }

            match s.kind {
                SuggestionKind::Frame => {
                    // Frame conditions aren't standard BMB yet, show as comment
                    output.push_str(&format!(
                        "// @modifies {}\n",
                        s.expr.to_bmb_string()
                    ));
                }
                SuggestionKind::Postcondition => {
                    output.push_str(&format!(
                        "@post {}\n",
                        s.expr.to_bmb_string()
                    ));
                }
                SuggestionKind::Precondition => {
                    output.push_str(&format!(
                        "@pre {}\n",
                        s.expr.to_bmb_string()
                    ));
                }
                SuggestionKind::Invariant => {
                    output.push_str(&format!(
                        "@invariant {} {}\n",
                        s.node_name,
                        s.expr.to_bmb_string()
                    ));
                }
            }
        }

        output
    }
}

impl Default for SuggestResult {
    fn default() -> Self {
        Self::new()
    }
}

/// Main entry point: analyze a program and generate suggestions
pub fn suggest_contracts(program: &TypedProgram, options: &SuggestOptions) -> SuggestResult {
    let mut result = SuggestResult::new();

    for typed_node in &program.nodes {
        let node = &typed_node.node;
        result.analyzed_nodes.push(node.name.name.clone());

        // Frame inference
        if options.frame {
            let frame_suggestions = frame::analyze_frame(node, typed_node);
            result.suggestions.extend(frame_suggestions);
        }

        // Postcondition inference
        if options.postcondition {
            let post_suggestions = postcondition::infer_postcondition(node, typed_node);
            result.suggestions.extend(post_suggestions);
        }
    }

    // Filter by confidence
    if options.min_confidence > 0.0 {
        result.suggestions.retain(|s| s.confidence >= options.min_confidence);
    }

    result
}

/// Format an expression as BMB code
fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::IntLit(n) => n.to_string(),
        Expr::FloatLit(f) => f.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Var(id) => id.name.clone(),
        Expr::Ret => "ret".to_string(),
        Expr::SelfRef => "self".to_string(),
        Expr::Old(inner) => format!("old({})", format_expr(inner)),
        Expr::Binary { op, left, right } => {
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
            format!("({} {} {})", format_expr(left), op_str, format_expr(right))
        }
        Expr::Unary { op, operand } => {
            let op_str = match op {
                UnaryOp::Not => "!",
                UnaryOp::Neg => "-",
            };
            format!("{}{}", op_str, format_expr(operand))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_suggestion_kind_display() {
        assert_eq!(SuggestionKind::Frame.to_string(), "@modifies");
        assert_eq!(SuggestionKind::Postcondition.to_string(), "@post");
    }

    #[test]
    fn test_memory_location_display() {
        assert_eq!(MemoryLocation::Register("x".to_string()).to_string(), "%x");
        assert_eq!(
            MemoryLocation::ArrayElement {
                base: "arr".to_string(),
                index: "i".to_string()
            }
            .to_string(),
            "arr[i]"
        );
    }

    #[test]
    fn test_suggested_expr_to_bmb_string() {
        let empty = SuggestedExpr::ModifiesSet(vec![]);
        assert_eq!(empty.to_bmb_string(), "nothing");

        let single = SuggestedExpr::ModifiesSet(vec![MemoryLocation::Register("x".to_string())]);
        assert_eq!(single.to_bmb_string(), "%x");
    }

    #[test]
    fn test_suggest_options() {
        let all = SuggestOptions::all();
        assert!(all.frame);
        assert!(all.postcondition);

        let frame = SuggestOptions::frame_only();
        assert!(frame.frame);
        assert!(!frame.postcondition);
    }
}
