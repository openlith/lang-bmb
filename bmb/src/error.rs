//! BMB Error System
//!
//! Enhanced error handling with source context, error codes, and suggestions.
//!
//! "Omission is guessing, and guessing is error." - Error messages should be
//! precise and actionable.

use crate::ast::Span;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

/// Error codes for BMB compilation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ErrorCode {
    // Parse errors (E001-E099)
    E001, // Unexpected token
    E002, // Invalid syntax
    E003, // Unclosed delimiter
    E004, // Invalid type name
    E005, // Invalid identifier

    // Type errors (E100-E199)
    E100, // Type mismatch
    E101, // Unknown variable
    E102, // Unknown register
    E103, // Unknown function
    E104, // Argument count mismatch
    E105, // Return type mismatch
    E106, // Invalid operand count
    E107, // Invalid operand type
    E108, // Label used as value

    // Contract errors (E200-E249)
    E200, // Contract verification failed
    E201, // Invalid precondition
    E202, // Invalid postcondition
    E203, // Ret used outside function

    // Verification errors with counterexamples (E250-E269)
    E250, // Precondition violation with counterexample
    E251, // Postcondition violation with counterexample
    E252, // Invariant violation with counterexample
    E253, // Assertion violation with counterexample

    // Linear type errors (E270-E279)
    E270, // Linear value never used
    E271, // Linear value used multiple times
    E272, // Linear value escapes scope

    // Invariant suggestion info (I300-I399)
    I300, // Missing loop invariant
    I301, // Suggested invariant available

    // Codegen errors (E300-E399)
    E300, // Unknown local variable
    E301, // Unsupported operation
    E302, // Invalid control flow

    // Module errors (E400-E499)
    E400, // Module not found
    E401, // Circular dependency
    E402, // Module load error
}

impl ErrorCode {
    /// Get the numeric code string (e.g., "E001")
    pub fn code(&self) -> &'static str {
        match self {
            // Parse errors
            ErrorCode::E001 => "E001",
            ErrorCode::E002 => "E002",
            ErrorCode::E003 => "E003",
            ErrorCode::E004 => "E004",
            ErrorCode::E005 => "E005",
            // Type errors
            ErrorCode::E100 => "E100",
            ErrorCode::E101 => "E101",
            ErrorCode::E102 => "E102",
            ErrorCode::E103 => "E103",
            ErrorCode::E104 => "E104",
            ErrorCode::E105 => "E105",
            ErrorCode::E106 => "E106",
            ErrorCode::E107 => "E107",
            ErrorCode::E108 => "E108",
            // Contract errors
            ErrorCode::E200 => "E200",
            ErrorCode::E201 => "E201",
            ErrorCode::E202 => "E202",
            ErrorCode::E203 => "E203",
            // Verification with counterexamples
            ErrorCode::E250 => "E250",
            ErrorCode::E251 => "E251",
            ErrorCode::E252 => "E252",
            ErrorCode::E253 => "E253",
            // Linear type errors
            ErrorCode::E270 => "E270",
            ErrorCode::E271 => "E271",
            ErrorCode::E272 => "E272",
            // Invariant suggestions
            ErrorCode::I300 => "I300",
            ErrorCode::I301 => "I301",
            // Codegen errors
            ErrorCode::E300 => "E300",
            ErrorCode::E301 => "E301",
            ErrorCode::E302 => "E302",
            // Module errors
            ErrorCode::E400 => "E400",
            ErrorCode::E401 => "E401",
            ErrorCode::E402 => "E402",
        }
    }

    /// Get a brief description of the error category
    pub fn category(&self) -> &'static str {
        match self {
            ErrorCode::E001
            | ErrorCode::E002
            | ErrorCode::E003
            | ErrorCode::E004
            | ErrorCode::E005 => "parse error",
            ErrorCode::E100
            | ErrorCode::E101
            | ErrorCode::E102
            | ErrorCode::E103
            | ErrorCode::E104
            | ErrorCode::E105
            | ErrorCode::E106
            | ErrorCode::E107
            | ErrorCode::E108 => "type error",
            ErrorCode::E200 | ErrorCode::E201 | ErrorCode::E202 | ErrorCode::E203 => {
                "contract error"
            }
            ErrorCode::E250 | ErrorCode::E251 | ErrorCode::E252 | ErrorCode::E253 => {
                "verification error"
            }
            ErrorCode::E270 | ErrorCode::E271 | ErrorCode::E272 => "linear type error",
            ErrorCode::I300 | ErrorCode::I301 => "invariant suggestion",
            ErrorCode::E300 | ErrorCode::E301 | ErrorCode::E302 => "codegen error",
            ErrorCode::E400 | ErrorCode::E401 | ErrorCode::E402 => "module error",
        }
    }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.code())
    }
}

/// Enhanced error with full context
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    /// Error code for categorization
    pub code: ErrorCode,
    /// Primary error message
    pub message: String,
    /// Source location (if available)
    pub span: Option<Span>,
    /// Suggestion for fixing the error (if available)
    pub suggestion: Option<String>,
    /// Additional notes
    pub notes: Vec<String>,
}

impl Diagnostic {
    /// Create a new diagnostic
    pub fn new(code: ErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            span: None,
            suggestion: None,
            notes: Vec::new(),
        }
    }

    /// Add source span
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Add a suggestion for fixing the error
    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestion = Some(suggestion.into());
        self
    }

    /// Add a note
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Format the error with source context
    pub fn format_with_source(&self, source: &str) -> String {
        let mut output = String::new();

        // Error header
        output.push_str(&format!("error[{}]: {}\n", self.code, self.message));

        // Source context (if span is available)
        if let Some(span) = &self.span {
            let lines: Vec<&str> = source.lines().collect();
            if span.line > 0 && span.line <= lines.len() {
                let line_content = lines[span.line - 1];
                let line_num_width = span.line.to_string().len();

                // Empty line with pipe
                output.push_str(&format!("{:>width$} |\n", "", width = line_num_width));

                // Line with content
                output.push_str(&format!(
                    "{:>width$} | {}\n",
                    span.line,
                    line_content,
                    width = line_num_width
                ));

                // Underline pointer
                let pointer_start = span.column.saturating_sub(1);
                let pointer_len = (span.end - span.start).max(1);
                output.push_str(&format!(
                    "{:>width$} | {:>start$}{}\n",
                    "",
                    "",
                    "^".repeat(pointer_len.min(line_content.len().saturating_sub(pointer_start))),
                    width = line_num_width,
                    start = pointer_start,
                ));
            }
        }

        // Suggestion
        if let Some(suggestion) = &self.suggestion {
            output.push_str(&format!("  = help: {}\n", suggestion));
        }

        // Notes
        for note in &self.notes {
            output.push_str(&format!("  = note: {}\n", note));
        }

        output
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error[{}]", self.code)?;
        if let Some(span) = &self.span {
            write!(f, " at {}:{}", span.line, span.column)?;
        }
        write!(f, ": {}", self.message)?;
        if let Some(suggestion) = &self.suggestion {
            write!(f, " (help: {})", suggestion)?;
        }
        Ok(())
    }
}

// ============================================================================
// v0.11.0: Enhanced Diagnostics with Counterexamples and JSON Output
// ============================================================================

/// SMT counterexample with source-level variable values
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Counterexample {
    /// Source-level variable names to their values
    pub variables: HashMap<String, String>,
    /// Which assertion/contract failed
    pub failed_assertion: String,
    /// Human-readable explanation
    pub explanation: Option<String>,
}

impl Counterexample {
    /// Create a new counterexample
    pub fn new(failed_assertion: impl Into<String>) -> Self {
        Self {
            variables: HashMap::new(),
            failed_assertion: failed_assertion.into(),
            explanation: None,
        }
    }

    /// Add a variable value
    pub fn with_variable(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        self.variables.insert(name.into(), value.into());
        self
    }

    /// Add explanation
    pub fn with_explanation(mut self, explanation: impl Into<String>) -> Self {
        self.explanation = Some(explanation.into());
        self
    }

    /// Format as readable string (compact)
    pub fn format(&self) -> String {
        let mut output = String::new();
        output.push_str("  = counterexample:\n");
        for (name, value) in &self.variables {
            output.push_str(&format!("      {} = {}\n", name, value));
        }
        if let Some(exp) = &self.explanation {
            output.push_str(&format!("    → {}\n", exp));
        }
        output
    }

    /// Format as multi-line box for CLI output
    pub fn format_cli(&self) -> String {
        let mut output = String::new();
        output.push_str("┌─ Counterexample ─────────────────────────────\n");
        output.push_str(&format!("│ Failed: {}\n", self.failed_assertion));
        output.push_str("│\n");
        output.push_str("│ Variable values:\n");

        // Sort variables for consistent output
        let mut vars: Vec<_> = self.variables.iter().collect();
        vars.sort_by(|a, b| a.0.cmp(b.0));

        for (name, value) in vars {
            output.push_str(&format!("│   {} = {}\n", name, value));
        }

        if let Some(exp) = &self.explanation {
            output.push_str("│\n");
            output.push_str(&format!("│ → {}\n", exp));
        }
        output.push_str("└──────────────────────────────────────────────\n");
        output
    }

    /// Format as inline annotation (for source visualization)
    pub fn format_inline(&self) -> String {
        if self.variables.is_empty() {
            return "counterexample exists".to_string();
        }

        let vars: Vec<_> = self
            .variables
            .iter()
            .map(|(n, v)| format!("{} = {}", n, v))
            .collect();
        format!("counterexample: {}", vars.join(", "))
    }

    /// Generate LSP-style inlay hint text
    pub fn to_inlay_hint(&self) -> String {
        if self.variables.is_empty() {
            return "⚠️ counterexample".to_string();
        }

        let mut parts = Vec::new();
        for (name, value) in &self.variables {
            parts.push(format!("{}={}", name, value));
        }
        format!("⚠️ {{{}}}", parts.join(", "))
    }

    /// Check if the counterexample has any variable values
    pub fn has_values(&self) -> bool {
        !self.variables.is_empty()
    }

    /// Get value for a specific variable
    pub fn get_variable(&self, name: &str) -> Option<&str> {
        self.variables.get(name).map(|s| s.as_str())
    }
}

impl std::fmt::Display for Counterexample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Counterexample for '{}': ", self.failed_assertion)?;
        if self.variables.is_empty() {
            write!(f, "(no specific values)")?;
        } else {
            let vars: Vec<_> = self
                .variables
                .iter()
                .map(|(n, v)| format!("{} = {}", n, v))
                .collect();
            write!(f, "{}", vars.join(", "))?;
        }
        Ok(())
    }
}

/// Related location for multi-span diagnostics (LSP compatible)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelatedLocation {
    /// File path (relative or absolute)
    pub file: String,
    /// Source location
    pub span: Span,
    /// Message for this location
    pub message: String,
}

/// LSP-compatible diagnostic severity
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
}

/// Extended diagnostic with counterexample support (v0.11.0+)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtendedDiagnostic {
    /// Base diagnostic
    #[serde(flatten)]
    pub base: Diagnostic,
    /// Counterexample if verification failed
    pub counterexample: Option<Counterexample>,
    /// Related locations (for multi-file errors)
    pub related_locations: Vec<RelatedLocation>,
    /// LSP severity level
    pub severity: DiagnosticSeverity,
    /// Source file path
    pub file: Option<String>,
}

impl ExtendedDiagnostic {
    /// Create from base diagnostic
    pub fn from_diagnostic(diag: Diagnostic) -> Self {
        let severity = match diag.code {
            ErrorCode::I300 | ErrorCode::I301 => DiagnosticSeverity::Information,
            _ => DiagnosticSeverity::Error,
        };
        Self {
            base: diag,
            counterexample: None,
            related_locations: Vec::new(),
            severity,
            file: None,
        }
    }

    /// Add counterexample
    pub fn with_counterexample(mut self, cex: Counterexample) -> Self {
        self.counterexample = Some(cex);
        self
    }

    /// Add related location
    pub fn with_related(mut self, loc: RelatedLocation) -> Self {
        self.related_locations.push(loc);
        self
    }

    /// Set file path
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// Convert to JSON string
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap_or_else(|_| "{}".to_string())
    }

    /// Convert to pretty JSON string
    pub fn to_json_pretty(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_else(|_| "{}".to_string())
    }

    /// Format with source including counterexample
    pub fn format_with_source(&self, source: &str) -> String {
        let mut output = self.base.format_with_source(source);
        if let Some(cex) = &self.counterexample {
            output.push_str(&cex.format());
        }
        output
    }
}

/// Loop invariant suggestion (v0.11.0+)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InvariantSuggestion {
    /// Loop label
    pub loop_label: String,
    /// Source location of the loop
    pub span: Span,
    /// Suggested invariant expression
    pub invariant: String,
    /// Confidence score (0.0 - 1.0)
    pub confidence: f64,
    /// Which verification conditions this satisfies
    pub satisfies: Vec<String>,
}

impl InvariantSuggestion {
    /// Create new suggestion
    pub fn new(loop_label: impl Into<String>, invariant: impl Into<String>, confidence: f64) -> Self {
        Self {
            loop_label: loop_label.into(),
            span: Span::default(),
            invariant: invariant.into(),
            confidence,
            satisfies: Vec::new(),
        }
    }

    /// Add span
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = span;
        self
    }

    /// Add satisfied condition
    pub fn with_satisfies(mut self, cond: impl Into<String>) -> Self {
        self.satisfies.push(cond.into());
        self
    }

    /// Format as suggestion message
    pub fn format(&self) -> String {
        let conf_marker = if self.confidence >= 0.8 {
            "[✓✓✓]"
        } else if self.confidence >= 0.6 {
            "[✓✓✗]"
        } else {
            "[✓✗✗]"
        };
        format!(
            "  {} @invariant {} {}",
            conf_marker, self.loop_label, self.invariant
        )
    }
}

/// Helper functions for creating common diagnostics
pub mod diagnostics {
    use super::*;

    /// Create a type mismatch error
    pub fn type_mismatch(expected: &str, got: &str, span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(
            ErrorCode::E100,
            format!("type mismatch: expected {}, got {}", expected, got),
        );
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag.with_note("all operands must have the same type")
    }

    /// Create an unknown variable error
    pub fn unknown_variable(name: &str, span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(ErrorCode::E101, format!("unknown variable: {}", name));
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag.with_suggestion(format!("check if '{}' is declared as a parameter", name))
    }

    /// Create an unknown register error
    pub fn unknown_register(name: &str, span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(ErrorCode::E102, format!("unknown register: %{}", name));
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag.with_suggestion("registers must be assigned before use with 'mov'")
    }

    /// Create an unknown function error
    pub fn unknown_function(name: &str, span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(ErrorCode::E103, format!("unknown function: {}", name));
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag.with_suggestion("check if the function is defined in this program")
    }

    /// Create an argument count mismatch error
    pub fn argument_count_mismatch(
        func: &str,
        expected: usize,
        got: usize,
        span: Option<Span>,
    ) -> Diagnostic {
        let mut diag = Diagnostic::new(
            ErrorCode::E104,
            format!(
                "function '{}' expects {} arguments, got {}",
                func, expected, got
            ),
        );
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag
    }

    /// Create a return type mismatch error
    pub fn return_type_mismatch(expected: &str, got: &str, span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(
            ErrorCode::E105,
            format!("return type mismatch: expected {}, got {}", expected, got),
        );
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag.with_note("return type must match the declared @returns type")
    }

    /// Create an invalid operand count error
    pub fn invalid_operand_count(
        opcode: &str,
        expected: &str,
        got: usize,
        span: Option<Span>,
    ) -> Diagnostic {
        let mut diag = Diagnostic::new(
            ErrorCode::E106,
            format!("'{}' requires {} operands, got {}", opcode, expected, got),
        );
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag
    }

    /// Create an invalid operand type error
    pub fn invalid_operand_type(
        opcode: &str,
        expected: &str,
        got: &str,
        span: Option<Span>,
    ) -> Diagnostic {
        let mut diag = Diagnostic::new(
            ErrorCode::E107,
            format!("'{}' expects {} operand, got {}", opcode, expected, got),
        );
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag
    }

    /// Create a label used as value error
    pub fn label_as_value(span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(ErrorCode::E108, "label cannot be used as value");
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag.with_suggestion("labels can only be used with jmp and jif instructions")
    }

    /// Create an unsupported operation error
    pub fn unsupported_operation(operation: &str, context: &str, span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(
            ErrorCode::E301,
            format!("{} not supported for {}", operation, context),
        );
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag
    }

    /// Create an unknown local error
    pub fn unknown_local(name: &str, span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(ErrorCode::E300, format!("unknown local: {}", name));
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag
    }

    /// Create a 'ret' outside function error
    pub fn ret_outside_function(span: Option<Span>) -> Diagnostic {
        let mut diag = Diagnostic::new(ErrorCode::E203, "'ret' used outside of function context");
        if let Some(s) = span {
            diag = diag.with_span(s);
        }
        diag.with_note("'ret' keyword is only valid in postconditions")
    }
}


// ============================================================================
// LSP (Language Server Protocol) Compatibility Layer - v0.11.0
// ============================================================================

/// LSP position (0-based line and character)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct LspPosition {
    pub line: u32,
    pub character: u32,
}

impl LspPosition {
    pub fn new(line: u32, character: u32) -> Self {
        Self { line, character }
    }

    pub fn from_span_start(span: &Span) -> Self {
        Self {
            line: span.line.saturating_sub(1) as u32,
            character: span.column.saturating_sub(1) as u32,
        }
    }
}

/// LSP range (start and end positions)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct LspRange {
    pub start: LspPosition,
    pub end: LspPosition,
}

impl LspRange {
    pub fn new(start: LspPosition, end: LspPosition) -> Self {
        Self { start, end }
    }

    pub fn from_span(span: &Span, source: Option<&str>) -> Self {
        let start = LspPosition::from_span_start(span);
        let end = if let Some(src) = source {
            Self::offset_to_position(src, span.end)
        } else {
            LspPosition::new(start.line, start.character + (span.end - span.start) as u32)
        };
        Self { start, end }
    }

    fn offset_to_position(source: &str, offset: usize) -> LspPosition {
        let mut line = 0u32;
        let mut character = 0u32;
        for (i, ch) in source.char_indices() {
            if i >= offset {
                break;
            }
            if ch == '\n' {
                line += 1;
                character = 0;
            } else {
                character += ch.len_utf16() as u32;
            }
        }
        LspPosition::new(line, character)
    }
}

/// LSP diagnostic tags
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LspDiagnosticTag {
    Unnecessary = 1,
    Deprecated = 2,
}

/// LSP related diagnostic information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspRelatedInformation {
    pub location: LspLocation,
    pub message: String,
}

/// LSP location (URI + range)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspLocation {
    pub uri: String,
    pub range: LspRange,
}

impl LspLocation {
    pub fn new(uri: String, range: LspRange) -> Self {
        Self { uri, range }
    }

    pub fn from_path_and_span(path: &str, span: &Span, source: Option<&str>) -> Self {
        let uri = if path.starts_with("file://") {
            path.to_string()
        } else {
            format!("file://{}", path.replace('\\', "/"))
        };
        Self {
            uri,
            range: LspRange::from_span(span, source),
        }
    }
}

/// LSP code action kind
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LspCodeActionKind {
    #[serde(rename = "quickfix")]
    QuickFix,
    #[serde(rename = "refactor")]
    Refactor,
    #[serde(rename = "source")]
    Source,
}

/// LSP text edit
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspTextEdit {
    pub range: LspRange,
    #[serde(rename = "newText")]
    pub new_text: String,
}

/// LSP workspace edit
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspWorkspaceEdit {
    pub changes: HashMap<String, Vec<LspTextEdit>>,
}

/// LSP code action
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspCodeAction {
    pub title: String,
    pub kind: LspCodeActionKind,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<LspDiagnostic>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub edit: Option<LspWorkspaceEdit>,
    #[serde(rename = "isPreferred", skip_serializing_if = "Option::is_none")]
    pub is_preferred: Option<bool>,
}

/// Full LSP-compatible diagnostic (LSP 3.17)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspDiagnostic {
    pub range: LspRange,
    pub severity: u8,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub source: String,
    pub message: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub tags: Vec<LspDiagnosticTag>,
    #[serde(rename = "relatedInformation", skip_serializing_if = "Vec::is_empty")]
    pub related_information: Vec<LspRelatedInformation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
}

impl LspDiagnostic {
    pub fn from_extended(diag: &ExtendedDiagnostic, source: Option<&str>) -> Self {
        let span = diag.base.span.unwrap_or_default();
        let range = LspRange::from_span(&span, source);
        let related_information: Vec<LspRelatedInformation> = diag
            .related_locations
            .iter()
            .map(|rel| LspRelatedInformation {
                location: LspLocation::from_path_and_span(rel.file.as_str(), &rel.span, None),
                message: rel.message.clone(),
            })
            .collect();
        let data = diag.counterexample.as_ref().map(|ce| {
            serde_json::json!({"counterexample": ce, "type": "verification_failure"})
        });
        Self {
            range,
            severity: diag.severity as u8,
            code: Some(diag.base.code.code().to_string()),
            source: "bmb".to_string(),
            message: diag.base.message.clone(),
            tags: Vec::new(),
            related_information,
            data,
        }
    }

    pub fn from_diagnostic(diag: &Diagnostic, source: Option<&str>) -> Self {
        let span = diag.span.unwrap_or_default();
        let range = LspRange::from_span(&span, source);
        let severity = if diag.code.code().starts_with('E') {
            1
        } else if diag.code.code().starts_with('W') {
            2
        } else if diag.code.code().starts_with('I') {
            3
        } else {
            4
        };
        Self {
            range,
            severity,
            code: Some(diag.code.code().to_string()),
            source: "bmb".to_string(),
            message: diag.message.clone(),
            tags: Vec::new(),
            related_information: Vec::new(),
            data: None,
        }
    }

    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    pub fn to_json_pretty(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    pub fn with_deprecated(mut self) -> Self {
        self.tags.push(LspDiagnosticTag::Deprecated);
        self
    }

    pub fn with_unnecessary(mut self) -> Self {
        self.tags.push(LspDiagnosticTag::Unnecessary);
        self
    }
}

/// Builder for LSP code actions
pub struct LspCodeActionBuilder {
    title: String,
    kind: LspCodeActionKind,
    diagnostics: Vec<LspDiagnostic>,
    edits: HashMap<String, Vec<LspTextEdit>>,
    is_preferred: bool,
}

impl LspCodeActionBuilder {
    pub fn quick_fix(title: impl Into<String>) -> Self {
        Self {
            title: title.into(),
            kind: LspCodeActionKind::QuickFix,
            diagnostics: Vec::new(),
            edits: HashMap::new(),
            is_preferred: false,
        }
    }

    pub fn refactor(title: impl Into<String>) -> Self {
        Self {
            title: title.into(),
            kind: LspCodeActionKind::Refactor,
            diagnostics: Vec::new(),
            edits: HashMap::new(),
            is_preferred: false,
        }
    }

    pub fn for_diagnostic(mut self, diag: LspDiagnostic) -> Self {
        self.diagnostics.push(diag);
        self
    }

    pub fn add_edit(
        mut self,
        uri: impl Into<String>,
        range: LspRange,
        new_text: impl Into<String>,
    ) -> Self {
        self.edits
            .entry(uri.into())
            .or_default()
            .push(LspTextEdit {
                range,
                new_text: new_text.into(),
            });
        self
    }

    pub fn preferred(mut self) -> Self {
        self.is_preferred = true;
        self
    }

    pub fn build(self) -> LspCodeAction {
        LspCodeAction {
            title: self.title,
            kind: self.kind,
            diagnostics: self.diagnostics,
            edit: if self.edits.is_empty() {
                None
            } else {
                Some(LspWorkspaceEdit {
                    changes: self.edits,
                })
            },
            is_preferred: if self.is_preferred { Some(true) } else { None },
        }
    }
}


/// Create quick fix for adding missing invariant
pub fn create_add_invariant_action(
    suggestion: &InvariantSuggestion,
    file_uri: &str,
    source: Option<&str>,
) -> LspCodeAction {
    let range = LspRange::from_span(&suggestion.span, source);
    let invariant_text = format!("@invariant {}\n", suggestion.invariant);
    LspCodeActionBuilder::quick_fix(format!("Add invariant: {}", suggestion.invariant))
        .add_edit(
            file_uri,
            LspRange::new(range.start, range.start),
            invariant_text,
        )
        .preferred()
        .build()
}


/// Error accumulator for collecting multiple diagnostics (v0.13+)
///
/// Enables "recoverable" compilation phases that can continue after errors,
/// collecting all problems for comprehensive error reporting.
///
/// # Example
/// ```ignore
/// let mut errors = ErrorCollector::new();
///
/// // Collect errors without returning early
/// if let Err(e) = check_type(expr1) {
///     errors.push_error(e);
/// }
/// if let Err(e) = check_type(expr2) {
///     errors.push_error(e);
/// }
///
/// // Report all errors or proceed if none
/// errors.into_result(())?;
/// ```
#[derive(Debug, Clone, Default)]
pub struct ErrorCollector {
    /// Collected errors
    errors: Vec<Diagnostic>,
    /// Collected warnings (non-fatal)
    warnings: Vec<Diagnostic>,
}

impl ErrorCollector {
    /// Create a new empty error collector
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an error diagnostic
    pub fn push_error(&mut self, diagnostic: impl Into<Diagnostic>) {
        self.errors.push(diagnostic.into());
    }

    /// Add a warning diagnostic
    pub fn push_warning(&mut self, diagnostic: impl Into<Diagnostic>) {
        self.warnings.push(diagnostic.into());
    }

    /// Add error from a Result, returning the Ok value if present
    pub fn check<T, E: Into<Diagnostic>>(&mut self, result: Result<T, E>) -> Option<T> {
        match result {
            Ok(v) => Some(v),
            Err(e) => {
                self.push_error(e);
                None
            }
        }
    }

    /// Check if any errors have been collected
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Check if any warnings have been collected
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    /// Get number of errors
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Get number of warnings
    pub fn warning_count(&self) -> usize {
        self.warnings.len()
    }

    /// Get all errors
    pub fn errors(&self) -> &[Diagnostic] {
        &self.errors
    }

    /// Get all warnings
    pub fn warnings(&self) -> &[Diagnostic] {
        &self.warnings
    }

    /// Take all errors, leaving an empty collector
    pub fn take_errors(&mut self) -> Vec<Diagnostic> {
        std::mem::take(&mut self.errors)
    }

    /// Merge another collector into this one
    pub fn merge(&mut self, other: ErrorCollector) {
        self.errors.extend(other.errors);
        self.warnings.extend(other.warnings);
    }

    /// Convert to Result: Ok if no errors, Err with first error otherwise
    pub fn into_result<T>(self, ok_value: T) -> Result<T, Diagnostic> {
        if self.errors.is_empty() {
            Ok(ok_value)
        } else {
            Err(self.errors.into_iter().next().unwrap())
        }
    }

    /// Convert to Result with all errors in a combined diagnostic
    pub fn into_combined_result<T>(self, ok_value: T) -> Result<T, Diagnostic> {
        if self.errors.is_empty() {
            Ok(ok_value)
        } else if self.errors.len() == 1 {
            Err(self.errors.into_iter().next().unwrap())
        } else {
            let count = self.errors.len();
            let first = self.errors.into_iter().next().unwrap();
            let combined = Diagnostic::new(
                first.code,
                format!("{} ({} more errors)", first.message, count - 1),
            )
            .with_span(first.span.unwrap_or_default());
            Err(combined)
        }
    }

    /// Format all errors with source context
    pub fn format_all(&self, source: &str) -> String {
        let mut output = String::new();
        for diag in &self.errors {
            output.push_str(&diag.format_with_source(source));
            output.push('\n');
        }
        for diag in &self.warnings {
            output.push_str(&format!("warning[{}]: {}\n", diag.code, diag.message));
        }
        if !self.errors.is_empty() {
            output.push_str(&format!(
                "\nerror: could not compile, {} error(s) found\n",
                self.errors.len()
            ));
        }
        output
    }

    /// Create collector from an iterator of results
    pub fn collect_results<T, E, I>(iter: I) -> (Vec<T>, Self)
    where
        I: IntoIterator<Item = Result<T, E>>,
        E: Into<Diagnostic>,
    {
        let mut collector = Self::new();
        let mut successes = Vec::new();
        for result in iter {
            if let Some(v) = collector.check(result) {
                successes.push(v);
            }
        }
        (successes, collector)
    }
}

impl From<Diagnostic> for ErrorCollector {
    fn from(diag: Diagnostic) -> Self {
        let mut collector = Self::new();
        collector.push_error(diag);
        collector
    }
}

impl std::iter::FromIterator<Diagnostic> for ErrorCollector {
    fn from_iter<I: IntoIterator<Item = Diagnostic>>(iter: I) -> Self {
        let mut collector = Self::new();
        for diag in iter {
            collector.push_error(diag);
        }
        collector
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_code_display() {
        assert_eq!(ErrorCode::E001.code(), "E001");
        assert_eq!(ErrorCode::E100.code(), "E100");
        assert_eq!(ErrorCode::E200.code(), "E200");
        assert_eq!(ErrorCode::E300.code(), "E300");
    }

    #[test]
    fn test_error_categories() {
        assert_eq!(ErrorCode::E001.category(), "parse error");
        assert_eq!(ErrorCode::E100.category(), "type error");
        assert_eq!(ErrorCode::E200.category(), "contract error");
        assert_eq!(ErrorCode::E300.category(), "codegen error");
    }

    #[test]
    fn test_diagnostic_display() {
        let diag = Diagnostic::new(ErrorCode::E100, "type mismatch")
            .with_span(Span::new(0, 5, 1, 1))
            .with_suggestion("use the same type");

        let display = format!("{}", diag);
        assert!(display.contains("E100"));
        assert!(display.contains("type mismatch"));
        assert!(display.contains("help:"));
    }

    #[test]
    fn test_diagnostic_format_with_source() {
        let source = "add %result $x $y";
        let diag = Diagnostic::new(ErrorCode::E100, "type mismatch: expected i32, got f32")
            .with_span(Span::new(12, 14, 1, 13))
            .with_suggestion("ensure both operands have the same type");

        let formatted = diag.format_with_source(source);
        assert!(formatted.contains("error[E100]"));
        assert!(formatted.contains("type mismatch"));
        assert!(formatted.contains("add %result $x $y"));
        assert!(formatted.contains("help:"));
    }

    #[test]
    fn test_helper_functions() {
        let diag = diagnostics::unknown_register("foo", None);
        assert_eq!(diag.code, ErrorCode::E102);
        assert!(diag.message.contains("foo"));
        assert!(diag.suggestion.is_some());

        let diag = diagnostics::type_mismatch("i32", "f32", None);
        assert_eq!(diag.code, ErrorCode::E100);
        assert!(diag.message.contains("i32"));
        assert!(diag.message.contains("f32"));
    }

    // ========== v0.11.0 Tests ==========

    #[test]
    fn test_verification_error_codes() {
        assert_eq!(ErrorCode::E250.code(), "E250");
        assert_eq!(ErrorCode::E251.code(), "E251");
        assert_eq!(ErrorCode::E270.category(), "linear type error");
        assert_eq!(ErrorCode::I300.category(), "invariant suggestion");
    }

    #[test]
    fn test_counterexample_creation() {
        let cex = Counterexample::new("postcondition: ret > 0")
            .with_variable("x", "-5")
            .with_variable("ret", "-10")
            .with_explanation("When x is negative, ret becomes negative");

        assert_eq!(cex.failed_assertion, "postcondition: ret > 0");
        assert_eq!(cex.variables.get("x"), Some(&"-5".to_string()));
        assert_eq!(cex.variables.get("ret"), Some(&"-10".to_string()));
        assert!(cex.explanation.is_some());
    }

    #[test]
    fn test_counterexample_format() {
        let cex = Counterexample::new("ret >= 0")
            .with_variable("n", "-3")
            .with_explanation("n cannot be negative");

        let formatted = cex.format();
        assert!(formatted.contains("counterexample:"));
        assert!(formatted.contains("n = -3"));
        assert!(formatted.contains("n cannot be negative"));
    }

    #[test]
    fn test_extended_diagnostic_json() {
        let diag = Diagnostic::new(ErrorCode::E251, "postcondition violation")
            .with_span(Span::new(10, 20, 5, 1));

        let cex = Counterexample::new("ret > 0")
            .with_variable("x", "-1");

        let extended = ExtendedDiagnostic::from_diagnostic(diag)
            .with_counterexample(cex)
            .with_file("test.bmb");

        let json = extended.to_json();
        assert!(json.contains("E251"));
        assert!(json.contains("postcondition violation"));
        assert!(json.contains("ret > 0"));
        assert!(json.contains("test.bmb"));
    }

    #[test]
    fn test_extended_diagnostic_severity() {
        let error_diag = ExtendedDiagnostic::from_diagnostic(
            Diagnostic::new(ErrorCode::E200, "error")
        );
        assert_eq!(error_diag.severity, DiagnosticSeverity::Error);

        let info_diag = ExtendedDiagnostic::from_diagnostic(
            Diagnostic::new(ErrorCode::I300, "suggestion")
        );
        assert_eq!(info_diag.severity, DiagnosticSeverity::Information);
    }

    #[test]
    fn test_invariant_suggestion() {
        let suggestion = InvariantSuggestion::new("_loop", "i >= 0 && i <= n", 0.85)
            .with_span(Span::new(100, 150, 10, 1))
            .with_satisfies("initialization")
            .with_satisfies("induction");

        assert_eq!(suggestion.loop_label, "_loop");
        assert!(suggestion.confidence >= 0.8);
        assert_eq!(suggestion.satisfies.len(), 2);

        let formatted = suggestion.format();
        assert!(formatted.contains("[✓✓✓]"));
        assert!(formatted.contains("@invariant _loop i >= 0 && i <= n"));
    }

    #[test]
    fn test_invariant_suggestion_confidence_markers() {
        let high = InvariantSuggestion::new("l", "x > 0", 0.9);
        assert!(high.format().contains("[✓✓✓]"));

        let medium = InvariantSuggestion::new("l", "x > 0", 0.7);
        assert!(medium.format().contains("[✓✓✗]"));

        let low = InvariantSuggestion::new("l", "x > 0", 0.4);
        assert!(low.format().contains("[✓✗✗]"));
    }

    #[test]
    fn test_diagnostic_serialization() {
        let diag = Diagnostic::new(ErrorCode::E100, "test")
            .with_span(Span::new(0, 10, 1, 1))
            .with_suggestion("fix it");

        let json = serde_json::to_string(&diag).unwrap();
        assert!(json.contains("E100"));
        assert!(json.contains("test"));

        // Verify round-trip
        let deserialized: Diagnostic = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.code, ErrorCode::E100);
        assert_eq!(deserialized.message, "test");
    }

    // ========== v0.11.0 LSP Tests ==========

    #[test]
    fn test_lsp_position_conversion() {
        let span = Span::new(10, 20, 5, 8);
        let pos = LspPosition::from_span_start(&span);
        assert_eq!(pos.line, 4); // 0-based
        assert_eq!(pos.character, 7); // 0-based
    }

    #[test]
    fn test_lsp_range_from_span() {
        let span = Span::new(0, 10, 1, 1);
        let range = LspRange::from_span(&span, None);
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 0);
        assert_eq!(range.end.character, 10);
    }

    #[test]
    fn test_lsp_range_with_source() {
        let source = "line1\nline2\n";
        let span = Span::new(0, 11, 1, 1);
        let range = LspRange::from_span(&span, Some(source));
        assert_eq!(range.start.line, 0);
        assert_eq!(range.end.line, 1); // spans to line 2
    }

    #[test]
    fn test_lsp_location_uri() {
        let span = Span::default();
        let loc = LspLocation::from_path_and_span("C:\\path\\file.bmb", &span, None);
        assert!(loc.uri.starts_with("file://"));
        assert!(loc.uri.contains("/path/file.bmb"));
    }

    #[test]
    fn test_lsp_diagnostic_from_diagnostic() {
        let diag = Diagnostic::new(ErrorCode::E100, "type error")
            .with_span(Span::new(5, 10, 2, 3));
        let lsp_diag = LspDiagnostic::from_diagnostic(&diag, None);

        assert_eq!(lsp_diag.severity, 1); // Error
        assert_eq!(lsp_diag.code, Some("E100".to_string()));
        assert_eq!(lsp_diag.source, "bmb");
        assert_eq!(lsp_diag.message, "type error");
        assert_eq!(lsp_diag.range.start.line, 1); // 0-based
    }

    #[test]
    fn test_lsp_diagnostic_severity_inference() {
        let error = LspDiagnostic::from_diagnostic(
            &Diagnostic::new(ErrorCode::E100, "error"), None);
        assert_eq!(error.severity, 1);

        let info = LspDiagnostic::from_diagnostic(
            &Diagnostic::new(ErrorCode::I300, "info"), None);
        assert_eq!(info.severity, 3);
    }

    #[test]
    fn test_lsp_diagnostic_json_output() {
        let diag = Diagnostic::new(ErrorCode::E200, "contract error")
            .with_span(Span::new(0, 5, 1, 1));
        let lsp_diag = LspDiagnostic::from_diagnostic(&diag, None);

        let json = lsp_diag.to_json().unwrap();
        assert!(json.contains("\"range\""));
        assert!(json.contains("\"severity\":1"));
        assert!(json.contains("\"code\":\"E200\""));
        assert!(json.contains("\"source\":\"bmb\""));
    }

    #[test]
    fn test_lsp_diagnostic_tags() {
        let diag = Diagnostic::new(ErrorCode::E100, "unused");
        let lsp_diag = LspDiagnostic::from_diagnostic(&diag, None)
            .with_unnecessary()
            .with_deprecated();

        assert_eq!(lsp_diag.tags.len(), 2);
        assert!(lsp_diag.tags.contains(&LspDiagnosticTag::Unnecessary));
        assert!(lsp_diag.tags.contains(&LspDiagnosticTag::Deprecated));
    }

    #[test]
    fn test_lsp_diagnostic_from_extended() {
        let base = Diagnostic::new(ErrorCode::E251, "postcondition failed")
            .with_span(Span::new(10, 20, 5, 1));
        let cex = Counterexample::new("ret > 0").with_variable("x", "-1");
        let extended = ExtendedDiagnostic::from_diagnostic(base)
            .with_counterexample(cex);

        let lsp_diag = LspDiagnostic::from_extended(&extended, None);
        assert!(lsp_diag.data.is_some());
        let data = lsp_diag.data.unwrap();
        assert!(data.get("counterexample").is_some());
    }

    #[test]
    fn test_lsp_code_action_builder() {
        let action = LspCodeActionBuilder::quick_fix("Fix error")
            .add_edit("file://test.bmb", LspRange::default(), "new code")
            .preferred()
            .build();

        assert_eq!(action.title, "Fix error");
        assert_eq!(action.kind, LspCodeActionKind::QuickFix);
        assert!(action.edit.is_some());
        assert_eq!(action.is_preferred, Some(true));
    }


    #[test]
    fn test_create_add_invariant_action() {
        let suggestion = InvariantSuggestion::new("_loop", "i >= 0", 0.9)
            .with_span(Span::new(50, 60, 10, 5));
        let action = create_add_invariant_action(&suggestion, "file://test.bmb", None);

        assert!(action.title.contains("Add invariant"));
        assert!(action.edit.is_some());
        let edit = action.edit.unwrap();
        assert!(edit.changes.contains_key("file://test.bmb"));
    }

    // ========== v0.11.0 Counterexample Visualization Tests ==========

    #[test]
    fn test_counterexample_format_cli() {
        let cex = Counterexample::new("postcondition: ret > 0")
            .with_variable("x", "-5")
            .with_variable("ret", "-10")
            .with_explanation("Negative input produces negative result");

        let cli_output = cex.format_cli();
        assert!(cli_output.contains("┌─ Counterexample"));
        assert!(cli_output.contains("Failed: postcondition: ret > 0"));
        assert!(cli_output.contains("Variable values:"));
        assert!(cli_output.contains("ret = -10"));
        assert!(cli_output.contains("x = -5"));
        assert!(cli_output.contains("Negative input produces negative result"));
        assert!(cli_output.contains("└─"));
    }

    #[test]
    fn test_counterexample_format_inline() {
        let cex = Counterexample::new("ret >= 0")
            .with_variable("x", "-1")
            .with_variable("y", "5");

        let inline = cex.format_inline();
        assert!(inline.contains("counterexample:"));
        assert!(inline.contains("x = -1"));
        assert!(inline.contains("y = 5"));
    }

    #[test]
    fn test_counterexample_format_inline_empty() {
        let cex = Counterexample::new("ret >= 0");
        let inline = cex.format_inline();
        assert_eq!(inline, "counterexample exists");
    }

    #[test]
    fn test_counterexample_inlay_hint() {
        let cex = Counterexample::new("ret > 0")
            .with_variable("n", "-3");

        let hint = cex.to_inlay_hint();
        assert!(hint.starts_with("⚠️"));
        assert!(hint.contains("n=-3"));
    }

    #[test]
    fn test_counterexample_inlay_hint_empty() {
        let cex = Counterexample::new("ret > 0");
        let hint = cex.to_inlay_hint();
        assert_eq!(hint, "⚠️ counterexample");
    }

    #[test]
    fn test_counterexample_has_values() {
        let empty = Counterexample::new("test");
        assert!(!empty.has_values());

        let with_var = Counterexample::new("test").with_variable("x", "1");
        assert!(with_var.has_values());
    }

    #[test]
    fn test_counterexample_get_variable() {
        let cex = Counterexample::new("test")
            .with_variable("x", "42")
            .with_variable("old(y)", "-1");

        assert_eq!(cex.get_variable("x"), Some("42"));
        assert_eq!(cex.get_variable("old(y)"), Some("-1"));
        assert_eq!(cex.get_variable("z"), None);
    }

    #[test]
    fn test_counterexample_display() {
        let cex = Counterexample::new("ret > 0")
            .with_variable("x", "-5");

        let display = format!("{}", cex);
        assert!(display.contains("Counterexample for 'ret > 0'"));
        assert!(display.contains("x = -5"));
    }

    #[test]
    fn test_counterexample_display_empty() {
        let cex = Counterexample::new("test");
        let display = format!("{}", cex);
        assert!(display.contains("(no specific values)"));
    }


    #[test]
    fn test_error_collector_new() {
        let collector = ErrorCollector::new();
        assert!(!collector.has_errors());
        assert!(!collector.has_warnings());
        assert_eq!(collector.error_count(), 0);
    }

    #[test]
    fn test_error_collector_push_error() {
        let mut collector = ErrorCollector::new();
        collector.push_error(Diagnostic::new(ErrorCode::E100, "test error"));
        assert!(collector.has_errors());
        assert_eq!(collector.error_count(), 1);
    }

    #[test]
    fn test_error_collector_push_warning() {
        let mut collector = ErrorCollector::new();
        collector.push_warning(Diagnostic::new(ErrorCode::E100, "test warning"));
        assert!(!collector.has_errors());
        assert!(collector.has_warnings());
        assert_eq!(collector.warning_count(), 1);
    }

    #[test]
    fn test_error_collector_check_ok() {
        let mut collector = ErrorCollector::new();
        let result: Result<i32, Diagnostic> = Ok(42);
        let value = collector.check(result);
        assert_eq!(value, Some(42));
        assert!(!collector.has_errors());
    }

    #[test]
    fn test_error_collector_check_err() {
        let mut collector = ErrorCollector::new();
        let result: Result<i32, Diagnostic> = Err(Diagnostic::new(ErrorCode::E100, "error"));
        let value = collector.check(result);
        assert_eq!(value, None);
        assert!(collector.has_errors());
    }

    #[test]
    fn test_error_collector_merge() {
        let mut c1 = ErrorCollector::new();
        c1.push_error(Diagnostic::new(ErrorCode::E100, "error 1"));

        let mut c2 = ErrorCollector::new();
        c2.push_error(Diagnostic::new(ErrorCode::E101, "error 2"));
        c2.push_warning(Diagnostic::new(ErrorCode::E100, "warning 1"));

        c1.merge(c2);
        assert_eq!(c1.error_count(), 2);
        assert_eq!(c1.warning_count(), 1);
    }

    #[test]
    fn test_error_collector_into_result() {
        let collector = ErrorCollector::new();
        let result: Result<(), Diagnostic> = collector.into_result(());
        assert!(result.is_ok());

        let mut collector2 = ErrorCollector::new();
        collector2.push_error(Diagnostic::new(ErrorCode::E100, "error"));
        let result2: Result<(), Diagnostic> = collector2.into_result(());
        assert!(result2.is_err());
    }

    #[test]
    fn test_error_collector_format_all() {
        let mut collector = ErrorCollector::new();
        collector.push_error(
            Diagnostic::new(ErrorCode::E100, "first error")
                .with_span(crate::ast::Span::new(0, 5, 1, 1)),
        );
        collector.push_error(Diagnostic::new(ErrorCode::E101, "second error"));

        let source = "let x = 42;";
        let formatted = collector.format_all(source);
        assert!(formatted.contains("first error"));
        assert!(formatted.contains("second error"));
        assert!(formatted.contains("2 error(s) found"));
    }
}
