//! BMB Error System
//!
//! Enhanced error handling with source context, error codes, and suggestions.
//!
//! "Omission is guessing, and guessing is error." - Error messages should be
//! precise and actionable.

use crate::ast::Span;
use std::fmt;

/// Error codes for BMB compilation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    // Contract errors (E200-E299)
    E200, // Contract verification failed
    E201, // Invalid precondition
    E202, // Invalid postcondition
    E203, // Ret used outside function

    // Codegen errors (E300-E399)
    E300, // Unknown local variable
    E301, // Unsupported operation
    E302, // Invalid control flow
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
            // Codegen errors
            ErrorCode::E300 => "E300",
            ErrorCode::E301 => "E301",
            ErrorCode::E302 => "E302",
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
            ErrorCode::E300 | ErrorCode::E301 | ErrorCode::E302 => "codegen error",
        }
    }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.code())
    }
}

/// Enhanced error with full context
#[derive(Debug, Clone)]
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
}
