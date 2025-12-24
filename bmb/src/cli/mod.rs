//! CLI argument parsing abstraction for v0.13+ self-hosting preparation
//!
//! This module provides a platform-independent argument parsing interface
//! that can be implemented in BMB for the self-hosted compiler.
//!
//! The design is intentionally simple to enable BMB reimplementation:
//! - No complex lifetime relationships
//! - Simple string-based interface
//! - Clear error types
//! - Predictable parsing behavior

use std::collections::HashMap;

pub mod args;
pub mod parser;

pub use args::*;
pub use parser::*;

/// CLI parsing error types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CliError {
    /// Missing required argument
    MissingRequired(String),
    /// Unknown option/flag
    UnknownOption(String),
    /// Invalid value for option
    InvalidValue { option: String, value: String, expected: String },
    /// Missing value for option that requires one
    MissingValue(String),
    /// Duplicate option provided
    DuplicateOption(String),
    /// Invalid subcommand
    InvalidSubcommand(String),
    /// General parse error
    ParseError(String),
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::MissingRequired(name) => write!(f, "missing required argument: {}", name),
            CliError::UnknownOption(opt) => write!(f, "unknown option: {}", opt),
            CliError::InvalidValue { option, value, expected } => {
                write!(f, "invalid value '{}' for option '{}': expected {}", value, option, expected)
            }
            CliError::MissingValue(opt) => write!(f, "option '{}' requires a value", opt),
            CliError::DuplicateOption(opt) => write!(f, "duplicate option: {}", opt),
            CliError::InvalidSubcommand(cmd) => write!(f, "invalid subcommand: {}", cmd),
            CliError::ParseError(msg) => write!(f, "parse error: {}", msg),
        }
    }
}

impl std::error::Error for CliError {}

/// Result type for CLI operations
pub type CliResult<T> = Result<T, CliError>;

/// Parsed command-line arguments
#[derive(Debug, Clone, Default)]
pub struct ParsedArgs {
    /// The subcommand (e.g., "compile", "check", "run")
    pub subcommand: Option<String>,
    /// Positional arguments (files, etc.)
    pub positional: Vec<String>,
    /// Named options with values (e.g., --output=foo.wasm)
    pub options: HashMap<String, String>,
    /// Boolean flags (e.g., --verbose, -v)
    pub flags: HashMap<String, bool>,
    /// Multiple values for an option (e.g., -I path1 -I path2)
    pub multi_options: HashMap<String, Vec<String>>,
    /// Trailing arguments after --
    pub trailing: Vec<String>,
}

impl ParsedArgs {
    /// Create empty parsed args
    pub fn new() -> Self {
        Self::default()
    }

    /// Get a single option value
    pub fn get_option(&self, name: &str) -> Option<&str> {
        self.options.get(name).map(|s| s.as_str())
    }

    /// Get option with default value
    pub fn get_option_or(&self, name: &str, default: &str) -> String {
        self.options.get(name).cloned().unwrap_or_else(|| default.to_string())
    }

    /// Check if a flag is set
    pub fn has_flag(&self, name: &str) -> bool {
        self.flags.get(name).copied().unwrap_or(false)
    }

    /// Get multiple option values
    pub fn get_multi_option(&self, name: &str) -> &[String] {
        self.multi_options.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Get the first positional argument
    pub fn first_positional(&self) -> Option<&str> {
        self.positional.first().map(|s| s.as_str())
    }

    /// Check if subcommand matches
    pub fn is_subcommand(&self, cmd: &str) -> bool {
        self.subcommand.as_deref() == Some(cmd)
    }
}

/// Simple help generator for commands
#[derive(Debug, Clone)]
pub struct HelpInfo {
    pub name: String,
    pub version: String,
    pub description: String,
    pub usage: String,
    pub subcommands: Vec<SubcommandHelp>,
    pub global_options: Vec<OptionHelp>,
}

/// Help info for a subcommand
#[derive(Debug, Clone)]
pub struct SubcommandHelp {
    pub name: String,
    pub description: String,
    pub options: Vec<OptionHelp>,
}

/// Help info for an option
#[derive(Debug, Clone)]
pub struct OptionHelp {
    pub short: Option<char>,
    pub long: String,
    pub description: String,
    pub takes_value: bool,
    pub default: Option<String>,
}

impl HelpInfo {
    /// Generate help text
    pub fn to_help_text(&self) -> String {
        let mut lines = Vec::new();

        // Header
        lines.push(format!("{} {}", self.name, self.version));
        lines.push(self.description.clone());
        lines.push(String::new());

        // Usage
        lines.push(format!("USAGE: {}", self.usage));
        lines.push(String::new());

        // Subcommands
        if !self.subcommands.is_empty() {
            lines.push("COMMANDS:".to_string());
            for cmd in &self.subcommands {
                lines.push(format!("    {:12} {}", cmd.name, cmd.description));
            }
            lines.push(String::new());
        }

        // Global options
        if !self.global_options.is_empty() {
            lines.push("OPTIONS:".to_string());
            for opt in &self.global_options {
                let short = opt.short.map(|c| format!("-{}, ", c)).unwrap_or_default();
                let value_hint = if opt.takes_value { " <value>" } else { "" };
                lines.push(format!("    {}--{}{}", short, opt.long, value_hint));
                lines.push(format!("            {}", opt.description));
            }
        }

        lines.join("\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cli_error_display() {
        let err = CliError::MissingRequired("file".to_string());
        assert_eq!(err.to_string(), "missing required argument: file");

        let err = CliError::InvalidValue {
            option: "level".to_string(),
            value: "invalid".to_string(),
            expected: "stone, bronze, silver, or gold".to_string(),
        };
        assert!(err.to_string().contains("invalid value"));
    }

    #[test]
    fn test_parsed_args_accessors() {
        let mut args = ParsedArgs::new();
        args.subcommand = Some("compile".to_string());
        args.positional.push("input.bmb".to_string());
        args.options.insert("output".to_string(), "output.wasm".to_string());
        args.flags.insert("verbose".to_string(), true);
        args.multi_options.insert("include".to_string(), vec!["./lib".to_string(), "./src".to_string()]);

        assert!(args.is_subcommand("compile"));
        assert!(!args.is_subcommand("check"));
        assert_eq!(args.first_positional(), Some("input.bmb"));
        assert_eq!(args.get_option("output"), Some("output.wasm"));
        assert_eq!(args.get_option_or("missing", "default"), "default");
        assert!(args.has_flag("verbose"));
        assert!(!args.has_flag("quiet"));
        assert_eq!(args.get_multi_option("include").len(), 2);
    }

    #[test]
    fn test_help_generation() {
        let help = HelpInfo {
            name: "bmbc".to_string(),
            version: "0.13.0".to_string(),
            description: "BMB Compiler".to_string(),
            usage: "bmbc <command> [options] <file>".to_string(),
            subcommands: vec![
                SubcommandHelp {
                    name: "compile".to_string(),
                    description: "Compile BMB source".to_string(),
                    options: vec![],
                },
            ],
            global_options: vec![
                OptionHelp {
                    short: Some('o'),
                    long: "output".to_string(),
                    description: "Output file path".to_string(),
                    takes_value: true,
                    default: None,
                },
            ],
        };

        let text = help.to_help_text();
        assert!(text.contains("bmbc 0.13.0"));
        assert!(text.contains("COMMANDS:"));
        assert!(text.contains("compile"));
        assert!(text.contains("OPTIONS:"));
        assert!(text.contains("--output"));
    }
}
