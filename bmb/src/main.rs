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
    compile, compile_to_arm64_with_opt, compile_to_macho_with_opt, compile_to_pe_with_opt,
    compile_to_x64_with_opt, compile_with_opt, VerificationLevel,
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

        /// Output format: wasm, wat, ast, elf (Linux x64), pe (Windows x64), macho (macOS x64), or arm64 (Linux ARM64)
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

    /// Run tests defined with @test directives
    Test {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Output test results as JSON
        #[arg(long)]
        json: bool,
    },

    /// Verify contracts using SMT solver (Gold level verification)
    Verify {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// SMT solver to use: z3, cvc4, or cvc5
        #[arg(long)]
        solver: Option<String>,

        /// Output SMT-LIB2 script instead of running verification
        #[arg(long)]
        emit_smt: bool,

        /// Output verification results as JSON
        #[arg(long)]
        json: bool,

        /// Suggest loop invariants using heuristics and SMT verification
        #[arg(long)]
        suggest_invariants: bool,
    },

    /// Suggest contracts to reduce boilerplate (v0.14+)
    Suggest {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Suggest frame conditions (@modifies)
        #[arg(long)]
        frame: bool,

        /// Suggest postconditions (@post)
        #[arg(long, visible_alias = "post")]
        postcondition: bool,

        /// Suggest all contract types
        #[arg(long)]
        all: bool,

        /// Minimum confidence threshold (0.0-1.0)
        #[arg(long, default_value = "0.5")]
        min_confidence: f64,

        /// Output suggestions as JSON
        #[arg(long)]
        json: bool,

        /// Include explanations in output
        #[arg(long, short)]
        verbose: bool,
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
        Commands::Test { file, json } => cmd_test(file, json),
        Commands::Verify {
            file,
            solver,
            emit_smt,
            json,
            suggest_invariants,
        } => cmd_verify(file, solver, emit_smt, json, suggest_invariants),
        Commands::Suggest {
            file,
            frame,
            postcondition,
            all,
            min_confidence,
            json,
            verbose,
        } => cmd_suggest(file, frame, postcondition, all, min_confidence, json, verbose),
    }
}

fn parse_level(level: &str) -> Option<VerificationLevel> {
    match level.to_lowercase().as_str() {
        "stone" | "0" => Some(VerificationLevel::Stone),
        "bronze" | "1" => Some(VerificationLevel::Bronze),
        "silver" | "2" => Some(VerificationLevel::Silver),
        "gold" | "3" => Some(VerificationLevel::Gold),
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
                "{}: invalid verification level '{}'. Use: stone, bronze, silver, or gold",
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

    // Handle arm64/aarch64 output for Linux ARM64
    if matches!(
        emit.as_deref(),
        Some("arm64") | Some("aarch64") | Some("arm")
    ) {
        match compile_to_arm64_with_opt(&source, opt_level) {
            Ok((elf, level)) => {
                let output_path = output.unwrap_or_else(|| {
                    let mut p = file.clone();
                    p.set_extension("arm64");
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
                    "{} {} -> {} ({}, native ARM64 Linux)",
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
                        "{}: unknown emit format '{}'. Use: wasm, wat, ast, elf (Linux x64), pe (Windows x64), macho (macOS x64), or arm64 (Linux ARM64)",
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
                "{}: invalid verification level '{}'. Use: stone, bronze, silver, or gold",
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

fn cmd_test(file: PathBuf, json: bool) -> ExitCode {
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

    let suite = match bmb::testing::run_tests(&source) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: {}", "error".red().bold(), e);
            return ExitCode::FAILURE;
        }
    };

    if suite.total == 0 {
        println!(
            "{} {} - no tests found",
            "OK".yellow().bold(),
            file.display()
        );
        return ExitCode::SUCCESS;
    }

    if json {
        let json_output = serde_json::json!({
            "file": file.display().to_string(),
            "total": suite.total,
            "passed": suite.passed,
            "failed": suite.failed,
            "results": suite.results.iter().map(|r| {
                serde_json::json!({
                    "node": r.node_name,
                    "test_index": r.test_index,
                    "function": r.function,
                    "passed": r.passed,
                    "expected": r.expected.as_ref().map(|v| v.to_string()),
                    "actual": r.actual.as_ref().map(|v| v.to_string()),
                    "error": r.error
                })
            }).collect::<Vec<_>>()
        });
        println!("{}", serde_json::to_string_pretty(&json_output).unwrap());
    } else {
        println!(
            "{} Running {} tests from {}",
            "Testing".cyan().bold(),
            suite.total,
            file.display()
        );
        println!();

        for result in &suite.results {
            let status = if result.passed {
                "✓".green()
            } else {
                "✗".red()
            };

            print!(
                "{} {}::test_{} - {}",
                status,
                result.node_name.bold(),
                result.test_index,
                result.function
            );

            if !result.passed {
                if let (Some(expected), Some(actual)) = (&result.expected, &result.actual) {
                    println!(
                        " {} expected: {}, got: {}",
                        "→".dimmed(),
                        expected.to_string().green(),
                        actual.to_string().red()
                    );
                } else if let Some(err) = &result.error {
                    println!(" {} {}", "→".dimmed(), err.red());
                } else {
                    println!();
                }
            } else {
                println!();
            }
        }

        println!();
        if suite.all_passed() {
            println!(
                "{} {} tests passed",
                "OK".green().bold(),
                suite.passed
            );
        } else {
            println!(
                "{} {} passed, {} failed",
                "FAIL".red().bold(),
                suite.passed.to_string().green(),
                suite.failed.to_string().red()
            );
        }
    }

    if suite.all_passed() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

#[cfg(feature = "smt")]
fn cmd_verify(
    file: PathBuf,
    solver: Option<String>,
    emit_smt: bool,
    json: bool,
    suggest_invariants: bool,
) -> ExitCode {
    // Set solver if specified
    if let Some(ref s) = solver {
        std::env::set_var("BMB_SMT_SOLVER", s);
    }

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

    // Parse
    let ast = match bmb::parser::parse(&source) {
        Ok(a) => a,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    // Type check
    let typed_ast = match bmb::types::typecheck(&ast) {
        Ok(t) => t,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    // If emit_smt, output SMT-LIB2 script
    if emit_smt {
        for node in &typed_ast.nodes {
            match bmb::smt::generate_smtlib2(node) {
                Ok(script) => {
                    println!("; === {} ===", node.node.name.name);
                    println!("{}", script);
                }
                Err(e) => {
                    eprintln!(
                        "{}: failed to generate SMT for '{}': {}",
                        "error".red().bold(),
                        node.node.name.name,
                        e
                    );
                }
            }
        }
        return ExitCode::SUCCESS;
    }

    // If suggest_invariants, run invariant suggestion for loops
    if suggest_invariants {
        println!(
            "{} Analyzing loops in {} for invariant suggestions",
            "Invariants".cyan().bold(),
            file.display()
        );
        println!();

        let mut total_suggestions = 0;
        for node in &typed_ast.nodes {
            // Find loop labels in the node
            let loop_labels = find_loop_labels(node);

            for label in loop_labels {
                let candidates = bmb::smt::suggest_verified_invariants(node, &label);

                if candidates.is_empty() {
                    continue;
                }

                total_suggestions += candidates.len();

                if json {
                    let json_output = serde_json::json!({
                        "node": node.node.name.name,
                        "loop": label,
                        "candidates": candidates.iter().map(|c| {
                            serde_json::json!({
                                "invariant": c.candidate.readable.clone(),
                                "status": format!("{:?}", c.status),
                                "confidence": c.adjusted_confidence,
                                "rationale": c.candidate.rationale.clone()
                            })
                        }).collect::<Vec<_>>()
                    });
                    println!("{}", serde_json::to_string_pretty(&json_output).unwrap());
                } else {
                    println!("{} {} (loop _{})", "→".cyan(), node.node.name.name.bold(), label);
                    println!("{}", bmb::smt::format_verified_candidates(&candidates));
                }
            }
        }

        if total_suggestions == 0 {
            println!(
                "{} No loop invariant suggestions found",
                "Note".yellow().bold()
            );
        } else {
            println!(
                "{} Found {} invariant candidate(s)",
                "Summary".green().bold(),
                total_suggestions
            );
        }

        return ExitCode::SUCCESS;
    }

    // Run SMT verification
    let results = match bmb::smt::verify_program(&typed_ast) {
        Ok(r) => r,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    if json {
        let json_output = serde_json::json!({
            "file": file.display().to_string(),
            "nodes": results.iter().map(|r| {
                serde_json::json!({
                    "name": r.node_name,
                    "precondition": format_verification_result(&r.precondition),
                    "postcondition": format_verification_result(&r.postcondition),
                    "assertions": r.assertions.iter().map(|a| {
                        serde_json::json!({
                            "index": a.index,
                            "result": format_verification_result(&a.result)
                        })
                    }).collect::<Vec<_>>(),
                    "invariants": r.invariants.iter().map(|inv| {
                        serde_json::json!({
                            "label": inv.label,
                            "result": format_verification_result(&inv.result)
                        })
                    }).collect::<Vec<_>>(),
                    "all_proven": r.all_proven()
                })
            }).collect::<Vec<_>>()
        });
        println!("{}", serde_json::to_string_pretty(&json_output).unwrap());
    } else {
        println!(
            "{} Verifying contracts in {} (Gold level)",
            "SMT".cyan().bold(),
            file.display()
        );
        println!();

        let mut all_proven = true;
        for result in &results {
            let status = if result.all_proven() {
                "✓".green()
            } else {
                all_proven = false;
                "✗".red()
            };

            println!("{} {}", status, result.node_name.bold());

            // Show precondition result
            print!("  precondition:  ");
            print_verification_result(&result.precondition);

            // Show postcondition result
            print!("  postcondition: ");
            print_verification_result(&result.postcondition);

            // Show assertion results
            for assertion in &result.assertions {
                print!("  @assert [{}]:  ", assertion.index);
                print_verification_result(&assertion.result);
            }

            // Show invariant results
            for inv in &result.invariants {
                print!("  @invariant _{}: ", inv.label);
                print_verification_result(&inv.result);
            }
            println!();
        }

        if all_proven {
            println!(
                "{} All contracts verified (Gold level achieved)",
                "OK".green().bold()
            );
        } else {
            println!(
                "{} Some contracts could not be verified",
                "WARN".yellow().bold()
            );
        }
    }

    // Return success even if some contracts couldn't be proven
    // (SolverNotFound is not a failure of the program)
    ExitCode::SUCCESS
}

#[cfg(feature = "smt")]
fn format_verification_result(result: &bmb::smt::VerificationResult) -> serde_json::Value {
    match result {
        bmb::smt::VerificationResult::Proven => serde_json::json!({
            "status": "proven",
            "message": "Contract mathematically verified"
        }),
        bmb::smt::VerificationResult::CounterExample(model) => {
            if model.is_empty() {
                serde_json::json!({
                    "status": "counterexample",
                    "message": "Counterexample exists (values not extracted)"
                })
            } else {
                serde_json::json!({
                    "status": "counterexample",
                    "model": model
                })
            }
        }
        bmb::smt::VerificationResult::Unknown(msg) => serde_json::json!({
            "status": "unknown",
            "message": msg
        }),
        bmb::smt::VerificationResult::Unsupported(msg) => serde_json::json!({
            "status": "unsupported",
            "message": msg
        }),
        bmb::smt::VerificationResult::SolverNotFound(msg) => serde_json::json!({
            "status": "solver_not_found",
            "message": msg
        }),
    }
}

#[cfg(feature = "smt")]
fn print_verification_result(result: &bmb::smt::VerificationResult) {
    match result {
        bmb::smt::VerificationResult::Proven => {
            println!("{}", "proven".green());
        }
        bmb::smt::VerificationResult::CounterExample(model) => {
            if model.is_empty() {
                println!("{} (values not extracted)", "counterexample".red());
            } else {
                println!(
                    "{}: {:?}",
                    "counterexample".red(),
                    model
                );
            }
        }
        bmb::smt::VerificationResult::Unknown(msg) => {
            println!("{}: {}", "unknown".yellow(), msg);
        }
        bmb::smt::VerificationResult::Unsupported(msg) => {
            println!("{}: {}", "unsupported".yellow(), msg);
        }
        bmb::smt::VerificationResult::SolverNotFound(msg) => {
            println!("{}: {}", "no solver".dimmed(), msg);
        }
    }
}

#[cfg(not(feature = "smt"))]
fn cmd_verify(
    _file: PathBuf,
    _solver: Option<String>,
    _emit_smt: bool,
    _json: bool,
    _suggest_invariants: bool,
) -> ExitCode {
    eprintln!(
        "{}: SMT verification requires the 'smt' feature. Recompile with:",
        "error".red().bold()
    );
    eprintln!("  cargo build --features smt");
    ExitCode::FAILURE
}

/// Find loop labels in a typed node by scanning for label instructions
/// that are referenced by backward jumps (jmp/jif to earlier labels)
#[cfg(feature = "smt")]
fn find_loop_labels(node: &bmb::types::TypedNode) -> Vec<String> {
    let mut labels: Vec<String> = Vec::new();
    let mut label_indices: std::collections::HashMap<String, usize> = std::collections::HashMap::new();

    // First pass: record all label positions
    for (idx, instr) in node.node.body.iter().enumerate() {
        if let bmb::ast::Instruction::Label(ident) = instr {
            label_indices.insert(ident.name.clone(), idx);
        }
    }

    // Second pass: find backward jumps (indicating loops)
    for (idx, instr) in node.node.body.iter().enumerate() {
        if let bmb::ast::Instruction::Statement(stmt) = instr {
            let opcode_str = format!("{:?}", stmt.opcode).to_lowercase();
            if opcode_str.contains("jmp") || opcode_str.contains("jif") {
                // Check if any operand is a label that's before this instruction
                for operand in &stmt.operands {
                    if let bmb::ast::Operand::Label(label_ident) = operand {
                        if let Some(&label_idx) = label_indices.get(&label_ident.name) {
                            if label_idx < idx {
                                // This is a backward jump - it's a loop
                                if !labels.contains(&label_ident.name) {
                                    labels.push(label_ident.name.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    labels
}

/// Suggest contracts to reduce boilerplate
fn cmd_suggest(
    file: PathBuf,
    frame: bool,
    postcondition: bool,
    all: bool,
    min_confidence: f64,
    json: bool,
    verbose: bool,
) -> ExitCode {
    // Read source file
    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "{}: cannot read '{}': {}",
                "error".red().bold(),
                file.display(),
                e
            );
            return ExitCode::FAILURE;
        }
    };

    // Parse and typecheck
    let ast = match bmb::parser::parse(&source) {
        Ok(ast) => ast,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    let typed_program = match bmb::types::typecheck(&ast) {
        Ok(tp) => tp,
        Err(e) => {
            print_error(&e, &source);
            return ExitCode::FAILURE;
        }
    };

    // Configure suggestion options
    let mut options = if all {
        bmb::suggest::SuggestOptions::all()
    } else {
        bmb::suggest::SuggestOptions {
            frame,
            postcondition,
            precondition: false,
            min_confidence,
            verbose,
        }
    };

    // If neither --frame nor --post specified and not --all, enable both
    if !all && !frame && !postcondition {
        options.frame = true;
        options.postcondition = true;
    }

    options.min_confidence = min_confidence;
    options.verbose = verbose;

    // Run contract inference
    let result = bmb::suggest::suggest_contracts(&typed_program, &options);

    // Output results
    if json {
        output_suggestions_json(&result, &file);
    } else {
        output_suggestions_text(&result, &file, verbose);
    }

    if result.suggestions.is_empty() {
        println!(
            "\n{}: No suggestions generated (contracts may already be complete)",
            "info".blue()
        );
    }

    ExitCode::SUCCESS
}

/// Output suggestions in JSON format
fn output_suggestions_json(result: &bmb::suggest::SuggestResult, file: &PathBuf) {
    use serde_json::json;

    let suggestions: Vec<_> = result
        .suggestions
        .iter()
        .map(|s| {
            json!({
                "node": s.node_name,
                "kind": s.kind.to_string(),
                "suggestion": s.expr.to_bmb_string(),
                "confidence": s.confidence,
                "explanation": s.explanation
            })
        })
        .collect();

    let output = json!({
        "file": file.display().to_string(),
        "analyzed_nodes": result.analyzed_nodes,
        "suggestions": suggestions,
        "warnings": result.warnings
    });

    println!("{}", serde_json::to_string_pretty(&output).unwrap());
}

/// Output suggestions in human-readable text format
fn output_suggestions_text(result: &bmb::suggest::SuggestResult, file: &PathBuf, verbose: bool) {
    println!(
        "\n{} Contract suggestions for {}",
        "==>".green().bold(),
        file.display()
    );
    println!(
        "    Analyzed {} node(s)\n",
        result.analyzed_nodes.len()
    );

    if result.suggestions.is_empty() {
        return;
    }

    let mut current_node = String::new();

    for s in &result.suggestions {
        if s.node_name != current_node {
            if !current_node.is_empty() {
                println!();
            }
            println!("  {} @node {}", ">>".cyan(), s.node_name.bold());
            current_node = s.node_name.clone();
        }

        let confidence_color = if s.confidence >= 0.8 {
            "green"
        } else if s.confidence >= 0.5 {
            "yellow"
        } else {
            "red"
        };

        let conf_str = format!("{:.0}%", s.confidence * 100.0);
        let conf_display = match confidence_color {
            "green" => conf_str.green(),
            "yellow" => conf_str.yellow(),
            _ => conf_str.red(),
        };

        println!(
            "     {} {} [{}]",
            s.kind.to_string().blue(),
            s.expr.to_bmb_string(),
            conf_display
        );

        if verbose {
            println!("       {}", s.explanation.dimmed());
        }
    }

    // Print warnings
    if !result.warnings.is_empty() {
        println!("\n  {}", "Warnings:".yellow());
        for w in &result.warnings {
            println!("    - {}", w);
        }
    }

    // Print usage hint
    println!(
        "\n{}: Copy suggestions to your source file and verify correctness.",
        "tip".cyan()
    );
    println!(
        "    {}",
        "BMB philosophy: Inference suggests, developer confirms.".dimmed()
    );
}
