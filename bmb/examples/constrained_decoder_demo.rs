//! Constrained Decoder Demo
//!
//! This example demonstrates how the AI integration module enables
//! grammar-constrained code generation - ensuring LLMs can only
//! produce syntactically valid BMB programs.
//!
//! Run with: cargo run --example constrained_decoder_demo

use bmb::ai::{
    valid_tokens, valid_keywords, valid_types, valid_opcodes,
    verify_partial, ConstrainedDecoder, GrammarState, TokenCategory,
};

fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║       BMB Constrained Decoder Demo                           ║");
    println!("║  \"Omission is guessing, and guessing is error.\"              ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    // Demo 1: Show valid tokens at each grammar state
    demo_grammar_states();

    // Demo 2: Build a complete program token by token
    demo_token_by_token_generation();

    // Demo 3: Verify partial programs
    demo_partial_verification();

    // Demo 4: Show how invalid tokens are rejected
    demo_invalid_token_rejection();
}

fn demo_grammar_states() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  DEMO 1: Valid Tokens at Each Grammar State");
    println!("═══════════════════════════════════════════════════════════════\n");

    let states = [
        (GrammarState::Start, "Start - Beginning of program"),
        (GrammarState::ExpectingNodeName, "After @node - Expecting function name"),
        (GrammarState::ExpectingParams, "After name - Expecting @params"),
        (GrammarState::InsideParams, "Inside @params - Expecting param or @returns"),
        (GrammarState::ExpectingParamType, "After param: - Expecting type"),
        (GrammarState::ExpectingReturnType, "After @returns - Expecting type"),
        (GrammarState::ExpectingContractOrBody, "After return type - @pre/@post or body"),
        (GrammarState::InsideBody, "Inside body - Expecting instruction"),
        (GrammarState::ExpectingOperand, "After opcode - Expecting operand"),
    ];

    for (state, description) in states {
        println!("📍 State: {}", description);
        let tokens = valid_tokens(&state);
        print!("   Valid categories: ");
        let cats: Vec<_> = tokens.iter().map(|t| format!("{:?}", t)).collect();
        println!("{}", cats.join(", "));

        // Show concrete tokens for some states
        match state {
            GrammarState::Start => {
                println!("   Concrete tokens: {:?}", valid_keywords(&state));
            }
            GrammarState::ExpectingParamType | GrammarState::ExpectingReturnType => {
                println!("   Concrete tokens: {:?}", valid_types());
            }
            GrammarState::InsideBody | GrammarState::ExpectingContractOrBody => {
                let opcodes = valid_opcodes();
                println!("   Concrete tokens: {:?}...", &opcodes[..5.min(opcodes.len())]);
            }
            _ => {}
        }
        println!();
    }
}

fn demo_token_by_token_generation() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  DEMO 2: Building a Program Token by Token");
    println!("═══════════════════════════════════════════════════════════════\n");

    let mut decoder = ConstrainedDecoder::new();

    // Tokens to generate: a simple addition function
    let tokens = [
        "@node", "sum",           // Function declaration
        "@params",                // Parameters
        "a", "i32",              // First param
        "b", "i32",              // Second param
        "@returns", "i32",       // Return type
        "add", "%r", "a", "b",   // add %r a b
        "ret", "%r",             // ret %r
    ];

    println!("🎯 Target: Build a simple addition function\n");
    println!("Step-by-step token addition:\n");

    for (i, token) in tokens.iter().enumerate() {
        // Show current state and valid options BEFORE adding token
        let state = decoder.state().clone();
        let valid = decoder.valid_concrete_tokens();

        println!("Step {}: Add token '{}'", i + 1, token);
        println!("   Current state: {:?}", state);
        if !valid.is_empty() {
            let display: Vec<_> = valid.iter().take(5).collect();
            if valid.len() > 5 {
                println!("   Valid options: {:?}... (+{} more)", display, valid.len() - 5);
            } else {
                println!("   Valid options: {:?}", display);
            }
        }

        // Add the token
        match decoder.add_token(token) {
            Ok(()) => println!("   ✅ Token accepted"),
            Err(e) => println!("   ❌ Error: {}", e),
        }
        println!();
    }

    // Show final result
    println!("📄 Generated source code:");
    println!("┌─────────────────────────────────────");
    for line in decoder.partial_source().lines() {
        println!("│ {}", line);
    }
    println!("└─────────────────────────────────────\n");

    // Validate the complete program
    match decoder.complete() {
        Ok(source) => {
            println!("✅ Program is syntactically valid!");
            println!("   Source length: {} bytes", source.len());
        }
        Err(e) => println!("❌ Validation failed: {}", e),
    }
    println!();
}

fn demo_partial_verification() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  DEMO 3: Partial Program Verification");
    println!("═══════════════════════════════════════════════════════════════\n");

    let partials = [
        ("", "Empty program"),
        ("@node", "Just @node keyword"),
        ("@node foo\n@params", "Node with params started"),
        ("@node foo\n@params x:i32\n@returns i32\n", "Complete header"),
        ("@node foo\n@params x:i32\n@returns i32\n  mul %r x x\n  ret %r\n", "Complete function"),
    ];

    for (source, description) in partials {
        let result = verify_partial(source);

        println!("📝 {}", description);
        if !source.is_empty() {
            println!("   Source: {:?}", source.replace('\n', "\\n"));
        }
        println!("   Completion: {:.0}%", result.completion * 100.0);
        println!("   Grammar state: {:?}", result.state);
        println!("   Syntax valid: {}", if result.syntax_valid { "✅" } else { "⚠️ (incomplete)" });

        let cats: Vec<_> = result.valid_next.iter().take(3).map(|t| format!("{:?}", t)).collect();
        println!("   Valid next: {}", cats.join(", "));
        println!();
    }
}

fn demo_invalid_token_rejection() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  DEMO 4: Invalid Token Rejection");
    println!("═══════════════════════════════════════════════════════════════\n");

    println!("🛡️ The constrained decoder PREVENTS syntax errors:\n");

    // Test 1: Wrong keyword at start
    {
        let mut decoder = ConstrainedDecoder::new();
        println!("Test 1: Try '@params' at start (should be '@node')");
        match decoder.add_token("@params") {
            Ok(()) => println!("   ❌ Unexpectedly accepted"),
            Err(e) => println!("   ✅ Rejected: {}", e),
        }
        println!();
    }

    // Test 2: Invalid type name
    {
        let mut decoder = ConstrainedDecoder::new();
        decoder.add_token("@node").unwrap();
        decoder.add_token("test").unwrap();
        decoder.add_token("@params").unwrap();
        decoder.add_token("x").unwrap();

        println!("Test 2: Try 'string' as type (invalid type)");
        match decoder.add_token("string") {
            Ok(()) => println!("   ❌ Unexpectedly accepted"),
            Err(e) => println!("   ✅ Rejected: {}", e),
        }
        println!();
    }

    // Test 3: Invalid identifier (starts with number)
    {
        let mut decoder = ConstrainedDecoder::new();
        decoder.add_token("@node").unwrap();

        println!("Test 3: Try '123func' as function name");
        match decoder.add_token("123func") {
            Ok(()) => println!("   ❌ Unexpectedly accepted"),
            Err(e) => println!("   ✅ Rejected: {}", e),
        }
        println!();
    }

    println!("═══════════════════════════════════════════════════════════════");
    println!("  Key Insight: By constraining the decoder, we guarantee");
    println!("  that AI-generated code is ALWAYS syntactically valid!");
    println!("═══════════════════════════════════════════════════════════════\n");
}
