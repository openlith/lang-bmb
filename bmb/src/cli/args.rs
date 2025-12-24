//! Argument type definitions for CLI parsing
//!
//! Defines the structured argument types that the BMB compiler expects.
//! These types are designed to be easily serializable and reconstructable
//! for self-hosted compiler scenarios.

use super::{CliError, CliResult, ParsedArgs};

/// Output format for compiled code
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// WebAssembly binary (.wasm)
    #[default]
    Wasm,
    /// WebAssembly text format (.wat)
    Wat,
    /// AST debug output
    Ast,
    /// Linux ELF64 executable
    Elf,
    /// Windows PE64 executable
    Pe,
    /// macOS Mach-O 64-bit executable
    MachO,
    /// Linux ARM64 ELF executable
    Arm64,
}

impl OutputFormat {
    /// Parse from string (case-insensitive)
    pub fn from_str(s: &str) -> CliResult<Self> {
        match s.to_lowercase().as_str() {
            "wasm" => Ok(OutputFormat::Wasm),
            "wat" => Ok(OutputFormat::Wat),
            "ast" => Ok(OutputFormat::Ast),
            "elf" | "x64" | "linux" => Ok(OutputFormat::Elf),
            "pe" | "exe" | "win" | "windows" => Ok(OutputFormat::Pe),
            "macho" | "mac" | "macos" => Ok(OutputFormat::MachO),
            "arm64" | "aarch64" | "arm" => Ok(OutputFormat::Arm64),
            _ => Err(CliError::InvalidValue {
                option: "emit".to_string(),
                value: s.to_string(),
                expected: "wasm, wat, ast, elf, pe, macho, or arm64".to_string(),
            }),
        }
    }

    /// Get the default file extension for this format
    pub fn default_extension(&self) -> &'static str {
        match self {
            OutputFormat::Wasm => "wasm",
            OutputFormat::Wat => "wat",
            OutputFormat::Ast => "ast",
            OutputFormat::Elf => "elf",
            OutputFormat::Pe => "exe",
            OutputFormat::MachO => "",
            OutputFormat::Arm64 => "arm64",
        }
    }

    /// Human-readable description
    pub fn description(&self) -> &'static str {
        match self {
            OutputFormat::Wasm => "WebAssembly binary",
            OutputFormat::Wat => "WebAssembly text format",
            OutputFormat::Ast => "AST debug output",
            OutputFormat::Elf => "Linux ELF64 executable",
            OutputFormat::Pe => "Windows PE64 executable",
            OutputFormat::MachO => "macOS Mach-O 64-bit executable",
            OutputFormat::Arm64 => "Linux ARM64 executable",
        }
    }
}

/// Verification level
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum VerifyLevel {
    /// Level 0: Parsing only
    Stone = 0,
    /// Level 1: Type checking
    #[default]
    Bronze = 1,
    /// Level 2: Runtime contract verification
    Silver = 2,
    /// Level 3: SMT-based static verification
    Gold = 3,
}

impl VerifyLevel {
    /// Parse from string (case-insensitive)
    pub fn from_str(s: &str) -> CliResult<Self> {
        match s.to_lowercase().as_str() {
            "stone" | "0" => Ok(VerifyLevel::Stone),
            "bronze" | "1" => Ok(VerifyLevel::Bronze),
            "silver" | "2" => Ok(VerifyLevel::Silver),
            "gold" | "3" => Ok(VerifyLevel::Gold),
            _ => Err(CliError::InvalidValue {
                option: "level".to_string(),
                value: s.to_string(),
                expected: "stone, bronze, silver, or gold".to_string(),
            }),
        }
    }
}

/// Optimization level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OptLevel {
    /// No optimizations
    None = 0,
    /// Basic optimizations (constant folding, dead code elimination)
    #[default]
    Basic = 1,
    /// Aggressive optimizations
    Aggressive = 2,
}

impl OptLevel {
    /// Parse from string (case-insensitive)
    pub fn from_str(s: &str) -> CliResult<Self> {
        match s.to_lowercase().as_str() {
            "none" | "0" => Ok(OptLevel::None),
            "basic" | "1" => Ok(OptLevel::Basic),
            "aggressive" | "full" | "2" => Ok(OptLevel::Aggressive),
            _ => Err(CliError::InvalidValue {
                option: "opt".to_string(),
                value: s.to_string(),
                expected: "none, basic, or aggressive".to_string(),
            }),
        }
    }

    /// Convert to library OptLevel
    pub fn to_lib_opt_level(self) -> crate::optimize::OptLevel {
        match self {
            OptLevel::None => crate::optimize::OptLevel::None,
            OptLevel::Basic => crate::optimize::OptLevel::Basic,
            OptLevel::Aggressive => crate::optimize::OptLevel::Aggressive,
        }
    }
}

/// Compile command arguments
#[derive(Debug, Clone, Default)]
pub struct CompileArgs {
    /// Input file path
    pub input: String,
    /// Output file path (optional, derived from input if not specified)
    pub output: Option<String>,
    /// Output format
    pub format: OutputFormat,
    /// Verification level
    pub level: VerifyLevel,
    /// Optimization level
    pub opt: OptLevel,
    /// Include paths for module resolution
    pub include_paths: Vec<String>,
    /// Verbose output
    pub verbose: bool,
    /// Quiet mode (minimal output)
    pub quiet: bool,
}

impl CompileArgs {
    /// Build from parsed args
    pub fn from_parsed(args: &ParsedArgs) -> CliResult<Self> {
        let input = args.first_positional()
            .ok_or_else(|| CliError::MissingRequired("input file".to_string()))?
            .to_string();

        let format = match args.get_option("emit") {
            Some(fmt) => OutputFormat::from_str(fmt)?,
            None => OutputFormat::Wasm,
        };

        let level = match args.get_option("level") {
            Some(lvl) => VerifyLevel::from_str(lvl)?,
            None => VerifyLevel::Silver,
        };

        let opt = match args.get_option("opt") {
            Some(o) => OptLevel::from_str(o)?,
            None => OptLevel::Basic,
        };

        Ok(Self {
            input,
            output: args.get_option("output").map(|s| s.to_string()),
            format,
            level,
            opt,
            include_paths: args.get_multi_option("include").to_vec(),
            verbose: args.has_flag("verbose"),
            quiet: args.has_flag("quiet"),
        })
    }

    /// Get the output path (derived from input if not specified)
    pub fn output_path(&self) -> String {
        if let Some(ref out) = self.output {
            out.clone()
        } else {
            // Replace extension with format's default
            let ext = self.format.default_extension();
            if ext.is_empty() {
                // For macOS, strip extension
                self.input.rsplit_once('.').map(|(base, _)| base.to_string())
                    .unwrap_or_else(|| self.input.clone())
            } else {
                self.input.rsplit_once('.').map(|(base, _)| format!("{}.{}", base, ext))
                    .unwrap_or_else(|| format!("{}.{}", self.input, ext))
            }
        }
    }
}

/// Check command arguments
#[derive(Debug, Clone, Default)]
pub struct CheckArgs {
    /// Input file path
    pub input: String,
    /// Verification level
    pub level: VerifyLevel,
    /// Include paths
    pub include_paths: Vec<String>,
}

impl CheckArgs {
    /// Build from parsed args
    pub fn from_parsed(args: &ParsedArgs) -> CliResult<Self> {
        let input = args.first_positional()
            .ok_or_else(|| CliError::MissingRequired("input file".to_string()))?
            .to_string();

        let level = match args.get_option("level") {
            Some(lvl) => VerifyLevel::from_str(lvl)?,
            None => VerifyLevel::Silver,
        };

        Ok(Self {
            input,
            level,
            include_paths: args.get_multi_option("include").to_vec(),
        })
    }
}

/// Run command arguments
#[derive(Debug, Clone, Default)]
pub struct RunArgs {
    /// Input file path
    pub input: String,
    /// Function to execute (default: first exported function)
    pub func: Option<String>,
    /// Arguments to pass to the function
    pub args: Vec<String>,
}

impl RunArgs {
    /// Build from parsed args
    pub fn from_parsed(args: &ParsedArgs) -> CliResult<Self> {
        let input = args.first_positional()
            .ok_or_else(|| CliError::MissingRequired("input file".to_string()))?
            .to_string();

        Ok(Self {
            input,
            func: args.get_option("func").map(|s| s.to_string()),
            args: args.trailing.clone(),
        })
    }
}

/// Grammar export command arguments
#[derive(Debug, Clone, Default)]
pub struct GrammarArgs {
    /// Output format: ebnf, json, or gbnf
    pub format: String,
    /// Output file path
    pub output: Option<String>,
}

impl GrammarArgs {
    /// Build from parsed args
    pub fn from_parsed(args: &ParsedArgs) -> CliResult<Self> {
        Ok(Self {
            format: args.get_option_or("format", "ebnf"),
            output: args.get_option("output").map(|s| s.to_string()),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_output_format_parsing() {
        assert_eq!(OutputFormat::from_str("wasm").unwrap(), OutputFormat::Wasm);
        assert_eq!(OutputFormat::from_str("WASM").unwrap(), OutputFormat::Wasm);
        assert_eq!(OutputFormat::from_str("elf").unwrap(), OutputFormat::Elf);
        assert_eq!(OutputFormat::from_str("x64").unwrap(), OutputFormat::Elf);
        assert_eq!(OutputFormat::from_str("pe").unwrap(), OutputFormat::Pe);
        assert_eq!(OutputFormat::from_str("windows").unwrap(), OutputFormat::Pe);
        assert!(OutputFormat::from_str("invalid").is_err());
    }

    #[test]
    fn test_verify_level_parsing() {
        assert_eq!(VerifyLevel::from_str("stone").unwrap(), VerifyLevel::Stone);
        assert_eq!(VerifyLevel::from_str("0").unwrap(), VerifyLevel::Stone);
        assert_eq!(VerifyLevel::from_str("gold").unwrap(), VerifyLevel::Gold);
        assert_eq!(VerifyLevel::from_str("3").unwrap(), VerifyLevel::Gold);
        assert!(VerifyLevel::from_str("invalid").is_err());
    }

    #[test]
    fn test_opt_level_parsing() {
        assert_eq!(OptLevel::from_str("none").unwrap(), OptLevel::None);
        assert_eq!(OptLevel::from_str("aggressive").unwrap(), OptLevel::Aggressive);
        assert_eq!(OptLevel::from_str("full").unwrap(), OptLevel::Aggressive);
        assert!(OptLevel::from_str("invalid").is_err());
    }

    #[test]
    fn test_compile_args_from_parsed() {
        let mut args = ParsedArgs::new();
        args.positional.push("input.bmb".to_string());
        args.options.insert("emit".to_string(), "elf".to_string());
        args.options.insert("opt".to_string(), "aggressive".to_string());

        let compile = CompileArgs::from_parsed(&args).unwrap();
        assert_eq!(compile.input, "input.bmb");
        assert_eq!(compile.format, OutputFormat::Elf);
        assert_eq!(compile.opt, OptLevel::Aggressive);
        assert_eq!(compile.output_path(), "input.elf");
    }

    #[test]
    fn test_compile_args_output_path() {
        let mut args = CompileArgs::default();
        args.input = "program.bmb".to_string();

        args.format = OutputFormat::Wasm;
        assert_eq!(args.output_path(), "program.wasm");

        args.format = OutputFormat::Pe;
        assert_eq!(args.output_path(), "program.exe");

        args.format = OutputFormat::MachO;
        assert_eq!(args.output_path(), "program");

        args.output = Some("custom.bin".to_string());
        assert_eq!(args.output_path(), "custom.bin");
    }
}
