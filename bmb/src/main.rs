//! BMB Compiler CLI
//!
//! "Omission is guessing, and guessing is error."
//!
//! A command-line interface for the BMB compiler.

use clap::{Parser, Subcommand};
use colored::Colorize;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use bmb::{
    compile, compile_to_macho_with_opt, compile_to_pe_with_opt, compile_to_x64_with_opt,
    compile_with_opt, VerificationLevel,
};

#[derive(Parser)]
#[command(name = "bmbc")]
#[command(author = "AILL Project")]
#[command(version)]
#[command(about = "BMB Compiler - Bare-Metal-Banter", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Compile a BMB source file to WebAssembly or native x64
    Compile {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Verification level: stone, bronze, or silver
        #[arg(long, default_value = "silver")]
        level: String,

        /// Output format: wasm, wat, ast, elf (Linux x64), pe (Windows x64), or macho (macOS x64)
        #[arg(long)]
        emit: Option<String>,

        /// Output file path
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Optimization level: none, basic, or aggressive
        #[arg(long, default_value = "basic")]
        opt: String,
    },

    /// Type-check a BMB source file without generating code
    Check {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Verification level: stone, bronze, or silver
        #[arg(long, default_value = "silver")]
        level: String,
    },

    /// Compile and run a BMB source file
    Run {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Function to execute (default: first function)
        #[arg(long)]
        func: Option<String>,

        /// Arguments to pass to the function
        #[arg(last = true)]
        args: Vec<String>,
    },

    /// Format a BMB source file
    Fmt {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Write formatted output back to the file
        #[arg(long)]
        write: bool,

        /// Check if the file is formatted (exit with error if not)
        #[arg(long)]
        check: bool,
    },

    /// Lint a BMB source file for style and potential issues
    Lint {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Treat warnings as errors
        #[arg(long)]
        deny_warnings: bool,
    },

    /// Export BMB grammar to external formats
    Grammar {
        /// Output format: ebnf, json, or gbnf
        #[arg(long, default_value = "ebnf")]
        format: String,

        /// Output file path (defaults to stdout)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Validate BMB source code (quick validation API for external tools)
    Validate {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Output validation result as JSON
        #[arg(long)]
        json: bool,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    match cli.command {
        Commands::Compile {
            file,
            level,
            emit,
            output,
            opt,
        } => cmd_compile(file, level, emit, output, opt),
        Commands::Check { file, level } => cmd_check(file, level),
        Commands::Run { file, func, args } => cmd_run(file, func, args),
        Commands::Fmt { file, write, check } => cmd_fmt(file, write, check),
        Commands::Lint {
            file,
            deny_warnings,
        } => cmd_lint(file, deny_warnings),
        Commands::Grammar { format, output } => cmd_grammar(format, output),
        Commands::Validate { file, json } => cmd_validate(file, json),
    }
}

fn parse_level(level: &str) -> Option<VerificationLevel> {
    match level.to_lowercase().as_str() {
        "stone" => Some(VerificationLevel::Stone),
        "bronze" => Some(VerificationLevel::Bronze),
        "silver" => Some(VerificationLevel::Silver),
        _ => None,
    }
}

fn parse_opt_level(opt: &str) -> Option<bmb::optimize::OptLevel> {
    match opt.to_lowercase().as_str() {
        "none" | "0" => Some(bmb::optimize::OptLevel::None),
        "basic" | "1" => Some(bmb::optimize::OptLevel::Basic),
        "aggressive" | "2" => Some(bmb::optimize::OptLevel::Aggressive),
        _ => None,
    }
}

fn cmd_compile(
    file: PathBuf,
    level: String,
    emit: Option<String>,
    output: Option<PathBuf>,
    opt: String,
) -> ExitCode {
    // Validate the requested level (for future use)
    let _requested_level = match parse_level(&level) {
        Some(l) => l,
        None => {
            eprintln!(
                "{}: invalid verification level '{}'. Use: stone, bronze, or silver",
                "error".red().bold(),
                level
            );
            return ExitCode::FAILURE;
        }
    };

    let opt_level = match parse_opt_level(&opt) {
        Some(l) => l,
        None => {
            eprintln!(
                "{}: invalid optimization level '{}'. Use: none, basic, or aggressive",
                "error".red().bold(),
                opt
            );
            return ExitCode::FAILURE;
        }
    };

    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "{}: could not read '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    // Handle elf/x64 output separately since it doesn't go through WASM
    if matches!(emit.as_deref(), Some("elf") | Some("x64")) {
        match compile_to_x64_with_opt(&source, opt_level) {
            Ok((elf, level)) => {
                let output_path = output.unwrap_or_else(|| {
                    let mut p = file.clone();
                    p.set_extension("elf");
                    p
                });
                if let Err(e) = fs::write(&output_path, &elf) {
                    eprintln!(
                        "{}: could not write '{}': {}",
                        "error".red().bold(),
                        output_path.display(),
                        e
                    );
                    return ExitCode::FAILURE;
                }
                println!(
                    "{} {} -> {} ({}, native x64 Linux)",
                    "Compiled".green().bold(),
                    file.display(),
                    output_path.display(),
                    level
                );
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                print_error(&e, &source);
                return ExitCode::FAILURE;
            }
        }
    }

    // Handle pe/exe output for Windows
    if matches!(
        emit.as_deref(),
        Some("pe") | Some("exe") | Some("win") | Some("windows")
    ) {
        match compile_to_pe_with_opt(&source, opt_level) {
            Ok((pe, level)) => {
                let output_path = output.unwrap_or_else(|| {
                    let mut p = file.clone();
                    p.set_extension("exe");
                    p
                });
                if let Err(e) = fs::write(&output_path, &pe) {
                    eprintln!(
                        "{}: could not write '{}': {}",
                        "error".red().bold(),
                        output_path.display(),
                        e
                    );
                    return ExitCode::FAILURE;
                }
                println!(
                    "{} {} -> {} ({}, native x64 Windows)",
                    "Compiled".green().bold(),
                    file.display(),
                    output_path.display(),
                    level
                );
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                print_error(&e, &source);
                return ExitCode::FAILURE;
            }
        }
    }

    // Handle macho output for macOS
    if matches!(emit.as_deref(), Some("macho") | Some("mac") | Some("macos")) {
        match compile_to_macho_with_opt(&source, opt_level) {
            Ok((macho, level)) => {
                let output_path = output.unwrap_or_else(|| {
                    let mut p = file.clone();
                    p.set_extension("");
                    p
                });
                if let Err(e) = fs::write(&output_path, &macho) {
                    eprintln!(
                        "{}: could not write '{}': {}",
                        "error".red().bold(),
                        output_path.display(),
                        e
                    );
                    return ExitCode::FAILURE;
                }
                println!(
                    "{} {} -> {} ({}, native x64 macOS)",
                    "Compiled".green().bold(),
                    file.display(),
                    output_path.display(),
                    level
                );
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                print_error(&e, &source);
                return ExitCode::FAILURE;
            }
        }
    }

    match compile_with_opt(&source, opt_level) {
        Ok((wasm, achieved_level)) => {
            match emit.as_deref() {
                Some("wat") => {
                    // Convert WASM binary to WAT text format
                    match wasmprinter::print_bytes(&wasm) {
                        Ok(wat) => {
                            let output_path = output.unwrap_or_else(|| file.with_extension("wat"));
                            if let Err(e) = fs::write(&output_path, &wat) {
                                eprintln!(
                                    "{}: could not write '{}': {}",
                                    "error".red().bold(),
                                    output_path.display(),
                                    e
                                );
                                return ExitCode::FAILURE;
                            }
                            println!(
                                "{} {} -> {} ({})",
                                "Compiled".green().bold(),
                                file.display(),
                                output_path.display(),
                                achieved_level
                            );
                        }
                        Err(e) => {
                            eprintln!("{}: failed to convert to WAT: {}", "error".red().bold(), e);
                            return ExitCode::FAILURE;
                        }
                    }
                }
                Some("ast") => {
                    // Print AST in debug format
                    // Re-parse to get the AST (compile already consumed it)
                    match bmb::parser::parse(&source) {
                        Ok(ast) => {
                            println!("{:#?}", ast);
                        }
                        Err(e) => {
                            print_error(&e, &source);
                            return ExitCode::FAILURE;
                        }
                    }
                }
                Some("wasm") | None => {
                    let output_path = output.unwrap_or_else(|| file.with_extension("wasm"));
                    if let Err(e) = fs::write(&output_path, &wasm) {
                        eprintln!(
                            "{}: could not write '{}': {}",
                            "error".red().bold(),
                            output_path.display(),
                            e
                        );
                        return ExitCode::FAILURE;
                    }
                    println!(
                        "{} {} -> {} ({})",
                        "Compiled".green().bold(),
                        file.display(),
                        output_path.display(),
                        achieved_level
                    );
                }
                Some(other) => {
                    eprintln!(
                        "{}: unknown emit format '{}'. Use: wasm, wat, ast, elf (Linux), pe (Windows), or macho (macOS)",
                        "error".red().bold(),
                        other
                    );
                    return ExitCode::FAILURE;
                }
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            print_error(&e, &source);
            ExitCode::FAILURE
        }
    }
}

/// Print a compilation error with source context
fn print_error(e: &bmb::BmbError, source: &str) {
    let formatted = e.format_with_source(source);
    for line in formatted.lines() {
        if line.starts_with("error") {
            eprintln!("{}", line.red().bold());
        } else if line.contains("help:") {
            eprintln!("{}", line.cyan());
        } else if line.contains("note:") {
            eprintln!("{}", line.yellow());
        } else {
            eprintln!("{}", line);
        }
    }
}

fn cmd_check(file: PathBuf, level: String) -> ExitCode {
    // Validate the requested level (for future use)
    let _requested_level = match parse_level(&level) {
        Some(l) => l,
        None => {
            eprintln!(
                "{}: invalid verification level '{}'. Use: stone, bronze, or silver",
                "error".red().bold(),
                level
            );
            return ExitCode::FAILURE;
        }
    };

    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "{}: could not read '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    // For check, we compile but don't write output
    match compile(&source) {
        Ok((_wasm, achieved_level)) => {
            println!(
                "{} {} ({})",
                "Verified".green().bold(),
                file.display(),
                achieved_level
            );
            ExitCode::SUCCESS
        }
        Err(e) => {
            print_error(&e, &source);
            ExitCode::FAILURE
        }
    }
}

fn cmd_run(file: PathBuf, func: Option<String>, args: Vec<String>) -> ExitCode {
    use wasmtime::*;

    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "{}: could not read '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    let (wasm, _level) = match compile(&source) {
        Ok(result) => result,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    let engine = Engine::default();
    let module = match Module::new(&engine, &wasm) {
        Ok(m) => m,
        Err(e) => {
            eprintln!(
                "{}: failed to create WASM module: {}",
                "error".red().bold(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    // Create linker with host functions
    let mut linker = Linker::new(&engine);

    // Register print_i32: prints an i32 value
    linker
        .func_wrap("env", "print_i32", |val: i32| {
            print!("{}", val);
        })
        .expect("failed to define print_i32");

    // Register print_i64: prints an i64 value
    linker
        .func_wrap("env", "print_i64", |val: i64| {
            print!("{}", val);
        })
        .expect("failed to define print_i64");

    // Register print_f32: prints an f32 value
    linker
        .func_wrap("env", "print_f32", |val: f32| {
            print!("{}", val);
        })
        .expect("failed to define print_f32");

    // Register print_f64: prints an f64 value
    linker
        .func_wrap("env", "print_f64", |val: f64| {
            print!("{}", val);
        })
        .expect("failed to define print_f64");

    // Register print_char: prints a character (i32 as ASCII)
    linker
        .func_wrap("env", "print_char", |val: i32| {
            if let Some(c) = char::from_u32(val as u32) {
                print!("{}", c);
            }
        })
        .expect("failed to define print_char");

    // Register print_newline: prints a newline
    linker
        .func_wrap("env", "print_newline", || {
            println!();
        })
        .expect("failed to define print_newline");

    let mut store = Store::new(&engine, ());
    let instance = match linker.instantiate(&mut store, &module) {
        Ok(i) => i,
        Err(e) => {
            eprintln!(
                "{}: failed to instantiate module: {}",
                "error".red().bold(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    // Get function name (use provided or find first export)
    let func_name = func.unwrap_or_else(|| {
        module
            .exports()
            .filter_map(|e| {
                if matches!(e.ty(), ExternType::Func(_)) {
                    Some(e.name().to_string())
                } else {
                    None
                }
            })
            .next()
            .unwrap_or_else(|| "main".to_string())
    });

    let exported_func = match instance.get_func(&mut store, &func_name) {
        Some(f) => f,
        None => {
            eprintln!(
                "{}: function '{}' not found in module",
                "error".red().bold(),
                func_name
            );
            return ExitCode::FAILURE;
        }
    };

    // Parse arguments and call function
    let func_ty = exported_func.ty(&store);
    let param_count = func_ty.params().len();

    if args.len() != param_count {
        eprintln!(
            "{}: function '{}' expects {} arguments, got {}",
            "error".red().bold(),
            func_name,
            param_count,
            args.len()
        );
        return ExitCode::FAILURE;
    }

    let mut wasm_args: Vec<Val> = Vec::new();
    for (arg, param_ty) in args.iter().zip(func_ty.params()) {
        let val = match param_ty {
            ValType::I32 => match arg.parse::<i32>() {
                Ok(v) => Val::I32(v),
                Err(_) => {
                    eprintln!("{}: cannot parse '{}' as i32", "error".red().bold(), arg);
                    return ExitCode::FAILURE;
                }
            },
            ValType::I64 => match arg.parse::<i64>() {
                Ok(v) => Val::I64(v),
                Err(_) => {
                    eprintln!("{}: cannot parse '{}' as i64", "error".red().bold(), arg);
                    return ExitCode::FAILURE;
                }
            },
            ValType::F32 => match arg.parse::<f32>() {
                Ok(v) => Val::F32(v.to_bits()),
                Err(_) => {
                    eprintln!("{}: cannot parse '{}' as f32", "error".red().bold(), arg);
                    return ExitCode::FAILURE;
                }
            },
            ValType::F64 => match arg.parse::<f64>() {
                Ok(v) => Val::F64(v.to_bits()),
                Err(_) => {
                    eprintln!("{}: cannot parse '{}' as f64", "error".red().bold(), arg);
                    return ExitCode::FAILURE;
                }
            },
            _ => {
                eprintln!("{}: unsupported parameter type", "error".red().bold());
                return ExitCode::FAILURE;
            }
        };
        wasm_args.push(val);
    }

    let result_count = func_ty.results().len();
    let mut results = vec![Val::I32(0); result_count];

    match exported_func.call(&mut store, &wasm_args, &mut results) {
        Ok(()) => {
            if results.is_empty() {
                println!("{}", "(no return value)".dimmed());
            } else {
                for (i, result) in results.iter().enumerate() {
                    let value_str = match result {
                        Val::I32(v) => format!("{}", v),
                        Val::I64(v) => format!("{}", v),
                        Val::F32(v) => format!("{}", f32::from_bits(*v)),
                        Val::F64(v) => format!("{}", f64::from_bits(*v)),
                        _ => format!("{:?}", result),
                    };
                    if results.len() == 1 {
                        println!("{}", value_str.green());
                    } else {
                        println!("result[{}] = {}", i, value_str.green());
                    }
                }
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{}: runtime error: {}", "error".red().bold(), e);
            ExitCode::FAILURE
        }
    }
}

fn cmd_fmt(file: PathBuf, write: bool, check: bool) -> ExitCode {
    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "{}: could not read '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    let ast = match bmb::parser::parse(&source) {
        Ok(a) => a,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    let formatted = bmb::fmt::format_program(&ast);

    if check {
        if source.trim() != formatted.trim() {
            eprintln!(
                "{}: {} would be reformatted",
                "error".red().bold(),
                file.display()
            );
            return ExitCode::FAILURE;
        }
        println!(
            "{} {} is correctly formatted",
            "OK".green().bold(),
            file.display()
        );
        return ExitCode::SUCCESS;
    }

    if write {
        if let Err(e) = fs::write(&file, &formatted) {
            eprintln!(
                "{}: could not write '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
        println!("{} {}", "Formatted".green().bold(), file.display());
    } else {
        print!("{}", formatted);
    }

    ExitCode::SUCCESS
}

fn cmd_lint(file: PathBuf, deny_warnings: bool) -> ExitCode {
    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "{}: could not read '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    let ast = match bmb::parser::parse(&source) {
        Ok(a) => a,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    let warnings = bmb::lint::lint(&ast);

    if warnings.is_empty() {
        println!(
            "{} {} - no issues found",
            "OK".green().bold(),
            file.display()
        );
        return ExitCode::SUCCESS;
    }

    let mut has_warnings = false;
    for warning in &warnings {
        has_warnings = true;
        let severity_str = match warning.severity {
            bmb::lint::Severity::Warning => "warning".yellow().bold(),
            bmb::lint::Severity::Style => "style".cyan().bold(),
            bmb::lint::Severity::Info => "info".blue().bold(),
        };

        eprint!("{}", severity_str);
        if let Some(line) = warning.line {
            eprint!(" at {}:{}", file.display(), line);
        }
        eprintln!(": [{}] {}", warning.code, warning.message);
        if let Some(ref suggestion) = warning.suggestion {
            eprintln!("  {} {}", "help:".cyan(), suggestion);
        }
    }

    println!(
        "\n{} {} warnings found in {}",
        if deny_warnings {
            "error:".red().bold()
        } else {
            "summary:".yellow().bold()
        },
        warnings.len(),
        file.display()
    );

    if deny_warnings && has_warnings {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn cmd_grammar(format: String, output: Option<PathBuf>) -> ExitCode {
    let grammar = bmb::grammar::BmbGrammar::new();

    let content = match format.to_lowercase().as_str() {
        "ebnf" => grammar.to_ebnf(),
        "json" => grammar.to_json_schema(),
        "gbnf" => grammar.to_gbnf(),
        other => {
            eprintln!(
                "{}: unknown format '{}'. Use: ebnf, json, or gbnf",
                "error".red().bold(),
                other
            );
            return ExitCode::FAILURE;
        }
    };

    if let Some(path) = output {
        if let Err(e) = fs::write(&path, &content) {
            eprintln!(
                "{}: could not write '{}': {}",
                "error".red().bold(),
                path.display(),
                e
            );
            return ExitCode::FAILURE;
        }
        println!(
            "{} grammar exported to {} ({})",
            "OK".green().bold(),
            path.display(),
            format
        );
    } else {
        print!("{}", content);
    }

    ExitCode::SUCCESS
}

fn cmd_validate(file: PathBuf, json: bool) -> ExitCode {
    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "{}: could not read '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    let result = bmb::grammar::validate(&source);

    if json {
        let json_output = serde_json::json!({
            "valid": result.valid,
            "level": result.level.to_string(),
            "errors": result.errors,
            "warnings": result.warnings
        });
        println!("{}", serde_json::to_string_pretty(&json_output).unwrap());
    } else {
        if result.valid {
            println!(
                "{} {} - validation passed ({})",
                "OK".green().bold(),
                file.display(),
                result.level
            );
        } else {
            eprintln!(
                "{} {} - validation failed at {}",
                "FAIL".red().bold(),
                file.display(),
                result.level
            );
            for error in &result.errors {
                eprintln!("  {}", error);
            }
        }
    }

    if result.valid {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
