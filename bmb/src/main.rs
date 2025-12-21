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

use bmb::{compile, VerificationLevel};

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
    /// Compile a BMB source file to WebAssembly
    Compile {
        /// Input BMB source file
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Verification level: stone, bronze, or silver
        #[arg(long, default_value = "silver")]
        level: String,

        /// Output format: wasm, wat, or ast
        #[arg(long)]
        emit: Option<String>,

        /// Output file path
        #[arg(short, long)]
        output: Option<PathBuf>,
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
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    match cli.command {
        Commands::Compile { file, level, emit, output } => {
            cmd_compile(file, level, emit, output)
        }
        Commands::Check { file, level } => {
            cmd_check(file, level)
        }
        Commands::Run { file, func, args } => {
            cmd_run(file, func, args)
        }
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

fn cmd_compile(file: PathBuf, level: String, emit: Option<String>, output: Option<PathBuf>) -> ExitCode {
    // Validate the requested level (for future use)
    let _requested_level = match parse_level(&level) {
        Some(l) => l,
        None => {
            eprintln!("{}: invalid verification level '{}'. Use: stone, bronze, or silver",
                "error".red().bold(), level);
            return ExitCode::FAILURE;
        }
    };

    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: could not read '{}': {}",
                "error".red().bold(), file.display(), e);
            return ExitCode::FAILURE;
        }
    };

    match compile(&source) {
        Ok((wasm, achieved_level)) => {
            let output_path = output.unwrap_or_else(|| {
                file.with_extension("wasm")
            });

            match emit.as_deref() {
                Some("wat") => {
                    // For WAT output, we would need wasmprinter or similar
                    eprintln!("{}: WAT output not yet implemented",
                        "error".red().bold());
                    return ExitCode::FAILURE;
                }
                Some("ast") => {
                    // For AST output, we would need to serialize the AST
                    eprintln!("{}: AST output not yet implemented",
                        "error".red().bold());
                    return ExitCode::FAILURE;
                }
                Some(other) => {
                    eprintln!("{}: unknown emit format '{}'. Use: wasm, wat, or ast",
                        "error".red().bold(), other);
                    return ExitCode::FAILURE;
                }
                None => {
                    if let Err(e) = fs::write(&output_path, &wasm) {
                        eprintln!("{}: could not write '{}': {}",
                            "error".red().bold(), output_path.display(), e);
                        return ExitCode::FAILURE;
                    }
                    println!("{} {} -> {} ({})",
                        "Compiled".green().bold(),
                        file.display(),
                        output_path.display(),
                        achieved_level);
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
            eprintln!("{}: invalid verification level '{}'. Use: stone, bronze, or silver",
                "error".red().bold(), level);
            return ExitCode::FAILURE;
        }
    };

    let source = match fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: could not read '{}': {}",
                "error".red().bold(), file.display(), e);
            return ExitCode::FAILURE;
        }
    };

    // For check, we compile but don't write output
    match compile(&source) {
        Ok((_wasm, achieved_level)) => {
            println!("{} {} ({})",
                "Verified".green().bold(),
                file.display(),
                achieved_level);
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
            eprintln!("{}: could not read '{}': {}",
                "error".red().bold(), file.display(), e);
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
            eprintln!("{}: failed to create WASM module: {}",
                "error".red().bold(), e);
            return ExitCode::FAILURE;
        }
    };

    let mut store = Store::new(&engine, ());
    let instance = match Instance::new(&mut store, &module, &[]) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("{}: failed to instantiate module: {}",
                "error".red().bold(), e);
            return ExitCode::FAILURE;
        }
    };

    // Get function name (use provided or find first export)
    let func_name = func.unwrap_or_else(|| {
        module.exports()
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
            eprintln!("{}: function '{}' not found in module",
                "error".red().bold(), func_name);
            return ExitCode::FAILURE;
        }
    };

    // Parse arguments and call function
    let func_ty = exported_func.ty(&store);
    let param_count = func_ty.params().len();

    if args.len() != param_count {
        eprintln!("{}: function '{}' expects {} arguments, got {}",
            "error".red().bold(), func_name, param_count, args.len());
        return ExitCode::FAILURE;
    }

    let mut wasm_args: Vec<Val> = Vec::new();
    for (arg, param_ty) in args.iter().zip(func_ty.params()) {
        let val = match param_ty {
            ValType::I32 => {
                match arg.parse::<i32>() {
                    Ok(v) => Val::I32(v),
                    Err(_) => {
                        eprintln!("{}: cannot parse '{}' as i32", "error".red().bold(), arg);
                        return ExitCode::FAILURE;
                    }
                }
            }
            ValType::I64 => {
                match arg.parse::<i64>() {
                    Ok(v) => Val::I64(v),
                    Err(_) => {
                        eprintln!("{}: cannot parse '{}' as i64", "error".red().bold(), arg);
                        return ExitCode::FAILURE;
                    }
                }
            }
            ValType::F32 => {
                match arg.parse::<f32>() {
                    Ok(v) => Val::F32(v.to_bits()),
                    Err(_) => {
                        eprintln!("{}: cannot parse '{}' as f32", "error".red().bold(), arg);
                        return ExitCode::FAILURE;
                    }
                }
            }
            ValType::F64 => {
                match arg.parse::<f64>() {
                    Ok(v) => Val::F64(v.to_bits()),
                    Err(_) => {
                        eprintln!("{}: cannot parse '{}' as f64", "error".red().bold(), arg);
                        return ExitCode::FAILURE;
                    }
                }
            }
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
