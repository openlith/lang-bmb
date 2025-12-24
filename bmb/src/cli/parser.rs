//! Simple argument parser implementation
//!
//! A minimal argument parser that can be reimplemented in BMB for self-hosting.
//! Follows POSIX-like conventions:
//! - Short options: -v, -o value
//! - Long options: --verbose, --output=value, --output value
//! - Positional arguments collected in order
//! - -- to separate trailing arguments

use super::{CliError, CliResult, ParsedArgs};
use std::collections::HashSet;

/// Argument parser builder for configuring expected arguments
#[derive(Debug, Clone, Default)]
pub struct ArgParser {
    /// Valid subcommands
    subcommands: HashSet<String>,
    /// Short-to-long option mapping
    short_to_long: std::collections::HashMap<char, String>,
    /// Options that take values
    value_options: HashSet<String>,
    /// Options that can appear multiple times
    multi_options: HashSet<String>,
    /// Required positional count
    required_positional: usize,
    /// Whether to allow unknown options
    allow_unknown: bool,
}

impl ArgParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a subcommand
    pub fn subcommand(mut self, name: &str) -> Self {
        self.subcommands.insert(name.to_string());
        self
    }

    /// Add a short/long option pair
    pub fn option(mut self, short: Option<char>, long: &str, takes_value: bool) -> Self {
        if let Some(c) = short {
            self.short_to_long.insert(c, long.to_string());
        }
        if takes_value {
            self.value_options.insert(long.to_string());
        }
        self
    }

    /// Add a multi-value option
    pub fn multi_option(mut self, short: Option<char>, long: &str) -> Self {
        if let Some(c) = short {
            self.short_to_long.insert(c, long.to_string());
        }
        self.multi_options.insert(long.to_string());
        self.value_options.insert(long.to_string());
        self
    }

    /// Set required positional argument count
    pub fn positional(mut self, count: usize) -> Self {
        self.required_positional = count;
        self
    }

    /// Allow unknown options (don't error on them)
    pub fn allow_unknown(mut self, allow: bool) -> Self {
        self.allow_unknown = allow;
        self
    }

    /// Parse arguments from iterator
    pub fn parse<I, S>(&self, args: I) -> CliResult<ParsedArgs>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let args: Vec<String> = args.into_iter().map(|s| s.as_ref().to_string()).collect();
        self.parse_vec(&args)
    }

    /// Parse from string vector
    pub fn parse_vec(&self, args: &[String]) -> CliResult<ParsedArgs> {
        let mut result = ParsedArgs::new();
        let mut i = 0;
        let mut past_separator = false;
        let mut subcommand_found = false;

        while i < args.len() {
            let arg = &args[i];

            // After --, everything is trailing
            if past_separator {
                result.trailing.push(arg.clone());
                i += 1;
                continue;
            }

            // Separator
            if arg == "--" {
                past_separator = true;
                i += 1;
                continue;
            }

            // Long option with =
            if arg.starts_with("--") && arg.contains('=') {
                let (opt, val) = arg[2..].split_once('=').unwrap();
                self.handle_long_option(&mut result, opt, Some(val.to_string()))?;
                i += 1;
                continue;
            }

            // Long option
            if arg.starts_with("--") {
                let opt = &arg[2..];
                let needs_value = self.value_options.contains(opt);

                if needs_value {
                    if i + 1 >= args.len() {
                        return Err(CliError::MissingValue(opt.to_string()));
                    }
                    let val = args[i + 1].clone();
                    self.handle_long_option(&mut result, opt, Some(val))?;
                    i += 2;
                } else {
                    self.handle_long_option(&mut result, opt, None)?;
                    i += 1;
                }
                continue;
            }

            // Short option(s)
            if arg.starts_with('-') && arg.len() > 1 && !arg.starts_with("--") {
                let chars: Vec<char> = arg[1..].chars().collect();

                for (j, c) in chars.iter().enumerate() {
                    let long_name = self.short_to_long.get(c).cloned()
                        .unwrap_or_else(|| c.to_string());

                    let needs_value = self.value_options.contains(&long_name);

                    if needs_value {
                        // Value can be rest of this arg or next arg
                        if j + 1 < chars.len() {
                            let val: String = chars[j + 1..].iter().collect();
                            self.handle_long_option(&mut result, &long_name, Some(val))?;
                            break;
                        } else if i + 1 < args.len() {
                            let val = args[i + 1].clone();
                            self.handle_long_option(&mut result, &long_name, Some(val))?;
                            i += 1;
                            break;
                        } else {
                            return Err(CliError::MissingValue(long_name));
                        }
                    } else {
                        self.handle_long_option(&mut result, &long_name, None)?;
                    }
                }
                i += 1;
                continue;
            }

            // Check for subcommand (first positional if matches)
            if !subcommand_found && self.subcommands.contains(arg) {
                result.subcommand = Some(arg.clone());
                subcommand_found = true;
                i += 1;
                continue;
            }

            // Positional argument
            result.positional.push(arg.clone());
            i += 1;
        }

        // Check required positionals
        if result.positional.len() < self.required_positional {
            return Err(CliError::MissingRequired(format!(
                "{} positional argument(s)",
                self.required_positional
            )));
        }

        Ok(result)
    }

    /// Handle a long option
    fn handle_long_option(
        &self,
        result: &mut ParsedArgs,
        name: &str,
        value: Option<String>,
    ) -> CliResult<()> {
        if self.multi_options.contains(name) {
            if let Some(val) = value {
                result.multi_options.entry(name.to_string())
                    .or_default()
                    .push(val);
            }
        } else if self.value_options.contains(name) {
            if let Some(val) = value {
                result.options.insert(name.to_string(), val);
            }
        } else {
            // Boolean flag
            result.flags.insert(name.to_string(), true);
        }
        Ok(())
    }
}

/// Convenience function to parse from environment args
pub fn parse_env_args() -> CliResult<ParsedArgs> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    ArgParser::new()
        .allow_unknown(true)
        .parse_vec(&args)
}

/// Create a parser configured for the bmbc CLI
pub fn bmbc_parser() -> ArgParser {
    ArgParser::new()
        // Subcommands
        .subcommand("compile")
        .subcommand("check")
        .subcommand("run")
        .subcommand("fmt")
        .subcommand("lint")
        .subcommand("grammar")
        .subcommand("validate")
        .subcommand("test")
        .subcommand("verify")
        // Common options
        .option(Some('o'), "output", true)
        .option(Some('l'), "level", true)
        .option(Some('e'), "emit", true)
        .option(None, "opt", true)
        .option(Some('v'), "verbose", false)
        .option(Some('q'), "quiet", false)
        .option(Some('h'), "help", false)
        .option(None, "version", false)
        // Multi-value options
        .multi_option(Some('I'), "include")
        // Command-specific
        .option(None, "func", true)
        .option(None, "format", true)
        .option(None, "solver", true)
        .option(None, "write", false)
        .option(None, "check", false)
        .option(None, "json", false)
        .option(None, "emit-smt", false)
        .option(None, "suggest-invariants", false)
        .option(None, "deny-warnings", false)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_parsing() {
        let parser = ArgParser::new()
            .option(Some('v'), "verbose", false)
            .option(Some('o'), "output", true);

        let args = vec!["-v", "-o", "out.wasm", "input.bmb"];
        let result = parser.parse(args).unwrap();

        assert!(result.has_flag("verbose"));
        assert_eq!(result.get_option("output"), Some("out.wasm"));
        assert_eq!(result.first_positional(), Some("input.bmb"));
    }

    #[test]
    fn test_long_options() {
        let parser = ArgParser::new()
            .option(None, "verbose", false)
            .option(None, "output", true);

        let args = vec!["--verbose", "--output=file.wasm", "input.bmb"];
        let result = parser.parse(args).unwrap();

        assert!(result.has_flag("verbose"));
        assert_eq!(result.get_option("output"), Some("file.wasm"));
    }

    #[test]
    fn test_subcommand() {
        let parser = ArgParser::new()
            .subcommand("compile")
            .subcommand("check")
            .option(None, "emit", true);

        let args = vec!["compile", "--emit", "elf", "input.bmb"];
        let result = parser.parse(args).unwrap();

        assert!(result.is_subcommand("compile"));
        assert_eq!(result.get_option("emit"), Some("elf"));
        assert_eq!(result.first_positional(), Some("input.bmb"));
    }

    #[test]
    fn test_multi_option() {
        let parser = ArgParser::new()
            .multi_option(Some('I'), "include");

        let args = vec!["-I", "lib/", "-I", "src/", "input.bmb"];
        let result = parser.parse(args).unwrap();

        let includes = result.get_multi_option("include");
        assert_eq!(includes.len(), 2);
        assert_eq!(includes[0], "lib/");
        assert_eq!(includes[1], "src/");
    }

    #[test]
    fn test_trailing_args() {
        let parser = ArgParser::new()
            .subcommand("run");

        let args = vec!["run", "prog.bmb", "--", "arg1", "arg2"];
        let result = parser.parse(args).unwrap();

        assert!(result.is_subcommand("run"));
        assert_eq!(result.first_positional(), Some("prog.bmb"));
        assert_eq!(result.trailing.len(), 2);
        assert_eq!(result.trailing[0], "arg1");
    }

    #[test]
    fn test_combined_short_options() {
        let parser = ArgParser::new()
            .option(Some('v'), "verbose", false)
            .option(Some('q'), "quiet", false)
            .option(Some('o'), "output", true);

        // -vq should set both verbose and quiet
        let args = vec!["-vq", "input.bmb"];
        let result = parser.parse(args).unwrap();

        assert!(result.has_flag("verbose"));
        assert!(result.has_flag("quiet"));

        // -ofile.wasm should work
        let args2 = vec!["-ofile.wasm", "input.bmb"];
        let result2 = parser.parse(args2).unwrap();
        assert_eq!(result2.get_option("output"), Some("file.wasm"));
    }

    #[test]
    fn test_missing_value_error() {
        let parser = ArgParser::new()
            .option(Some('o'), "output", true);

        let args = vec!["-o"];
        let result = parser.parse(args);

        assert!(matches!(result, Err(CliError::MissingValue(_))));
    }

    #[test]
    fn test_bmbc_parser() {
        let parser = bmbc_parser();

        let args = vec!["compile", "-e", "elf", "-o", "prog", "--opt", "aggressive", "-v", "input.bmb"];
        let result = parser.parse(args).unwrap();

        assert!(result.is_subcommand("compile"));
        assert_eq!(result.get_option("emit"), Some("elf"));
        assert_eq!(result.get_option("output"), Some("prog"));
        assert_eq!(result.get_option("opt"), Some("aggressive"));
        assert!(result.has_flag("verbose"));
        assert_eq!(result.first_positional(), Some("input.bmb"));
    }
}
