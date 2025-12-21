//! Compile helloworld.bmb to a native x64 Linux executable
//!
//! Run with: cargo run --example hello_x64
//! This generates: helloworld.elf
//!
//! On Linux, run: ./helloworld.elf
//! Output: 42

use std::fs::{self, File};
use std::io::Write;

fn main() {
    println!("=== BMB to x64 Native Compiler ===\n");

    // Read the BMB source file
    let source_path = "tests/examples/helloworld.bmb";
    let source = match fs::read_to_string(source_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to read {}: {}", source_path, e);
            return;
        }
    };

    println!("Source file: {}", source_path);
    println!("---");
    println!("{}", source);
    println!("---\n");

    // Compile to x64 ELF
    println!("Compiling to x64...");
    let (elf_data, level) = match bmb::compile_to_x64(&source) {
        Ok(result) => result,
        Err(e) => {
            eprintln!("Compilation failed: {}", e);
            return;
        }
    };

    println!("Verification level: {}", level);
    println!("Generated {} bytes of ELF data", elf_data.len());

    // Print first 64 bytes (ELF header) in hex
    println!("\nELF Header (hex):");
    for (i, byte) in elf_data.iter().take(64).enumerate() {
        if i > 0 && i % 16 == 0 {
            println!();
        }
        print!("{:02x} ", byte);
    }
    println!("\n");

    // Write to file
    let output_path = "helloworld.elf";
    let mut file = File::create(output_path).expect("Failed to create file");
    file.write_all(&elf_data).expect("Failed to write file");

    println!("Written to: {}", output_path);
    println!("\nTo run on Linux:");
    println!("  chmod +x {}", output_path);
    println!("  ./{}", output_path);
    println!("\nExpected output: 42");
}
