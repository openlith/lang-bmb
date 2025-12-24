//! Exhaustiveness Checker for Pattern Matching
//!
//! Implements a simplified usefulness algorithm based on Maranget's work.
//! Reference: "Warnings for pattern matching" (Maranget, JFP 2007)
//!
//! ## Algorithm Overview
//!
//! For each match statement, we verify that:
//! 1. All enum variants are covered (for enum scrutinees)
//! 2. A @default arm exists for infinite domains (integers, etc.)
//! 3. Patterns are reachable (no dead code)
//!
//! ## Philosophy Alignment
//!
//! "Omission is guessing, and guessing is error."
//!
//! Exhaustiveness checking enforces that developers explicitly handle all cases.
//! Missing arms are compile-time errors, not runtime surprises.

use crate::ast::{EnumDef, LiteralValue, MatchStmt, Pattern, Span};
use crate::types::TypeRegistry;
use crate::BmbError;

/// Result of exhaustiveness analysis
#[derive(Debug, Clone)]
pub struct ExhaustivenessResult {
    /// Missing patterns (if any)
    pub missing_patterns: Vec<String>,
    /// Unreachable patterns (dead code)
    pub unreachable_patterns: Vec<UnreachablePattern>,
    /// Whether the match is exhaustive
    pub is_exhaustive: bool,
}

/// An unreachable pattern (dead code)
#[derive(Debug, Clone)]
pub struct UnreachablePattern {
    pub pattern_desc: String,
    pub span: Span,
}

/// Check exhaustiveness of a match statement
///
/// # Arguments
/// * `match_stmt` - The match statement to check
/// * `scrutinee_type` - The type of the scrutinee (e.g., "Status" for enum)
/// * `registry` - Type registry containing enum definitions
///
/// # Returns
/// * `Ok(ExhaustivenessResult)` - Analysis result
/// * `Err(BmbError)` - If analysis fails
pub fn check_exhaustiveness(
    match_stmt: &MatchStmt,
    scrutinee_type: &crate::ast::Type,
    registry: &TypeRegistry,
) -> Result<ExhaustivenessResult, BmbError> {
    let mut result = ExhaustivenessResult {
        missing_patterns: Vec::new(),
        unreachable_patterns: Vec::new(),
        is_exhaustive: false,
    };

    match scrutinee_type {
        // User-defined enum types (explicitly typed as Enum)
        crate::ast::Type::Enum(type_name) => {
            if let Some(enum_def) = registry.get_enum(type_name) {
                check_enum_exhaustiveness(match_stmt, enum_def, &mut result)?;
            } else {
                // Enum not found in registry - require default
                if match_stmt.default.is_none() {
                    result.missing_patterns.push("@default".to_string());
                } else {
                    result.is_exhaustive = true;
                }
            }
        }

        // User-defined types parsed as Struct (may actually be an enum)
        // Note: Parser creates Type::Struct for all user-defined types
        // since struct vs enum is determined at type-checking time
        crate::ast::Type::Struct(type_name) => {
            // Check if it's actually an enum in the registry
            if let Some(enum_def) = registry.get_enum(type_name) {
                check_enum_exhaustiveness(match_stmt, enum_def, &mut result)?;
            } else {
                // It's a struct or unknown type - require default
                if match_stmt.default.is_none() {
                    result.missing_patterns.push("@default".to_string());
                } else {
                    result.is_exhaustive = true;
                }
            }
        }

        // Bool has finite domain (true, false)
        crate::ast::Type::Bool => {
            check_bool_exhaustiveness(match_stmt, &mut result)?;
        }

        // Integer types have infinite domain - require default
        crate::ast::Type::I8
        | crate::ast::Type::I16
        | crate::ast::Type::I32
        | crate::ast::Type::I64
        | crate::ast::Type::U8
        | crate::ast::Type::U16
        | crate::ast::Type::U32
        | crate::ast::Type::U64 => {
            check_integer_exhaustiveness(match_stmt, &mut result)?;
        }

        // Other types - require default
        _ => {
            if match_stmt.default.is_none() {
                result.missing_patterns.push("@default".to_string());
            } else {
                result.is_exhaustive = true;
            }
        }
    }

    // Check for unreachable patterns (patterns after @default)
    check_unreachable_patterns(match_stmt, &mut result);

    Ok(result)
}

/// Check exhaustiveness for enum types
fn check_enum_exhaustiveness(
    match_stmt: &MatchStmt,
    enum_def: &EnumDef,
    result: &mut ExhaustivenessResult,
) -> Result<(), BmbError> {
    // Collect covered variants
    let mut covered_variants: std::collections::HashSet<String> = std::collections::HashSet::new();

    for arm in &match_stmt.arms {
        if let Pattern::Variant {
            variant_name, span, ..
        } = &arm.pattern
        {
            let variant = variant_name.name.clone();

            // Check for duplicate patterns
            if covered_variants.contains(&variant) {
                result.unreachable_patterns.push(UnreachablePattern {
                    pattern_desc: format!("{}::{}", enum_def.name.name, variant),
                    span: span.clone(),
                });
            } else {
                covered_variants.insert(variant);
            }
        }
    }

    // Check which variants are missing
    for variant in &enum_def.variants {
        if !covered_variants.contains(&variant.name.name) {
            // If there's a default, we're still exhaustive
            if match_stmt.default.is_none() {
                result
                    .missing_patterns
                    .push(format!("{}::{}", enum_def.name.name, variant.name.name));
            }
        }
    }

    // Determine exhaustiveness
    if match_stmt.default.is_some() {
        result.is_exhaustive = true;
    } else {
        result.is_exhaustive = result.missing_patterns.is_empty();
    }

    Ok(())
}

/// Check exhaustiveness for bool type
fn check_bool_exhaustiveness(
    match_stmt: &MatchStmt,
    result: &mut ExhaustivenessResult,
) -> Result<(), BmbError> {
    let mut has_true = false;
    let mut has_false = false;

    for arm in &match_stmt.arms {
        if let Pattern::Literal {
            value: LiteralValue::Bool(b),
            span,
        } = &arm.pattern
        {
            if *b {
                if has_true {
                    result.unreachable_patterns.push(UnreachablePattern {
                        pattern_desc: "true".to_string(),
                        span: span.clone(),
                    });
                }
                has_true = true;
            } else {
                if has_false {
                    result.unreachable_patterns.push(UnreachablePattern {
                        pattern_desc: "false".to_string(),
                        span: span.clone(),
                    });
                }
                has_false = true;
            }
        }
    }

    // Check missing patterns
    if match_stmt.default.is_none() {
        if !has_true {
            result.missing_patterns.push("true".to_string());
        }
        if !has_false {
            result.missing_patterns.push("false".to_string());
        }
    }

    result.is_exhaustive = match_stmt.default.is_some() || (has_true && has_false);

    Ok(())
}

/// Check exhaustiveness for integer types
fn check_integer_exhaustiveness(
    match_stmt: &MatchStmt,
    result: &mut ExhaustivenessResult,
) -> Result<(), BmbError> {
    // Integer domain is infinite, so we require @default
    if match_stmt.default.is_none() {
        result.missing_patterns.push("@default".to_string());
        result.is_exhaustive = false;
    } else {
        result.is_exhaustive = true;
    }

    // Check for duplicate literal patterns
    let mut seen_values: std::collections::HashSet<i64> = std::collections::HashSet::new();
    for arm in &match_stmt.arms {
        if let Pattern::Literal {
            value: LiteralValue::Int(n),
            span,
        } = &arm.pattern
        {
            if seen_values.contains(n) {
                result.unreachable_patterns.push(UnreachablePattern {
                    pattern_desc: n.to_string(),
                    span: span.clone(),
                });
            } else {
                seen_values.insert(*n);
            }
        }
    }

    Ok(())
}

/// Check for unreachable patterns (e.g., patterns after @default)
fn check_unreachable_patterns(_match_stmt: &MatchStmt, _result: &mut ExhaustivenessResult) {
    // Note: In BMB's current grammar, @default must come last,
    // so we don't need to check for arms after default.
    // This function is here for future extensions (guards, wildcards).
}

/// Format missing patterns for error message
pub fn format_missing_patterns(missing: &[String]) -> String {
    if missing.len() == 1 {
        format!("Missing pattern: {}", missing[0])
    } else {
        format!("Missing patterns: {}", missing.join(", "))
    }
}

/// Format unreachable patterns for warning message
pub fn format_unreachable_patterns(unreachable: &[UnreachablePattern]) -> String {
    let descriptions: Vec<&str> = unreachable.iter().map(|p| p.pattern_desc.as_str()).collect();
    if descriptions.len() == 1 {
        format!("Unreachable pattern: {}", descriptions[0])
    } else {
        format!("Unreachable patterns: {}", descriptions.join(", "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{EnumVariant, Identifier, MatchArm, MatchDefault, Span};

    fn make_span() -> Span {
        Span::new(0, 0, 1, 1)
    }

    fn make_id(name: &str) -> Identifier {
        Identifier::new(name, make_span())
    }

    fn make_enum_def(name: &str, variants: &[&str]) -> EnumDef {
        EnumDef {
            name: make_id(name),
            variants: variants
                .iter()
                .map(|v| EnumVariant {
                    name: make_id(v),
                    payload: None,
                    span: make_span(),
                })
                .collect(),
            span: make_span(),
        }
    }

    #[test]
    fn test_enum_exhaustive_all_variants() {
        let enum_def = make_enum_def("Status", &["Ok", "Err"]);
        let match_stmt = MatchStmt {
            scrutinee: "x".to_string(),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Variant {
                        enum_name: make_id("Status"),
                        variant_name: make_id("Ok"),
                        binding: None,
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
                MatchArm {
                    pattern: Pattern::Variant {
                        enum_name: make_id("Status"),
                        variant_name: make_id("Err"),
                        binding: None,
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
            ],
            default: None,
            span: make_span(),
        };

        let mut result = ExhaustivenessResult {
            missing_patterns: Vec::new(),
            unreachable_patterns: Vec::new(),
            is_exhaustive: false,
        };

        check_enum_exhaustiveness(&match_stmt, &enum_def, &mut result).unwrap();

        assert!(result.is_exhaustive);
        assert!(result.missing_patterns.is_empty());
    }

    #[test]
    fn test_enum_missing_variant() {
        let enum_def = make_enum_def("Status", &["Ok", "Err", "Pending"]);
        let match_stmt = MatchStmt {
            scrutinee: "x".to_string(),
            arms: vec![MatchArm {
                pattern: Pattern::Variant {
                    enum_name: make_id("Status"),
                    variant_name: make_id("Ok"),
                    binding: None,
                    span: make_span(),
                },
                body: vec![],
                span: make_span(),
            }],
            default: None,
            span: make_span(),
        };

        let mut result = ExhaustivenessResult {
            missing_patterns: Vec::new(),
            unreachable_patterns: Vec::new(),
            is_exhaustive: false,
        };

        check_enum_exhaustiveness(&match_stmt, &enum_def, &mut result).unwrap();

        assert!(!result.is_exhaustive);
        assert!(result.missing_patterns.contains(&"Status::Err".to_string()));
        assert!(result
            .missing_patterns
            .contains(&"Status::Pending".to_string()));
    }

    #[test]
    fn test_enum_with_default_is_exhaustive() {
        let enum_def = make_enum_def("Status", &["Ok", "Err", "Pending"]);
        let match_stmt = MatchStmt {
            scrutinee: "x".to_string(),
            arms: vec![MatchArm {
                pattern: Pattern::Variant {
                    enum_name: make_id("Status"),
                    variant_name: make_id("Ok"),
                    binding: None,
                    span: make_span(),
                },
                body: vec![],
                span: make_span(),
            }],
            default: Some(MatchDefault {
                body: vec![],
                span: make_span(),
            }),
            span: make_span(),
        };

        let mut result = ExhaustivenessResult {
            missing_patterns: Vec::new(),
            unreachable_patterns: Vec::new(),
            is_exhaustive: false,
        };

        check_enum_exhaustiveness(&match_stmt, &enum_def, &mut result).unwrap();

        assert!(result.is_exhaustive);
    }

    #[test]
    fn test_bool_exhaustive() {
        let match_stmt = MatchStmt {
            scrutinee: "b".to_string(),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal {
                        value: LiteralValue::Bool(true),
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
                MatchArm {
                    pattern: Pattern::Literal {
                        value: LiteralValue::Bool(false),
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
            ],
            default: None,
            span: make_span(),
        };

        let mut result = ExhaustivenessResult {
            missing_patterns: Vec::new(),
            unreachable_patterns: Vec::new(),
            is_exhaustive: false,
        };

        check_bool_exhaustiveness(&match_stmt, &mut result).unwrap();

        assert!(result.is_exhaustive);
        assert!(result.missing_patterns.is_empty());
    }

    #[test]
    fn test_integer_requires_default() {
        let match_stmt = MatchStmt {
            scrutinee: "n".to_string(),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal {
                        value: LiteralValue::Int(0),
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
                MatchArm {
                    pattern: Pattern::Literal {
                        value: LiteralValue::Int(1),
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
            ],
            default: None,
            span: make_span(),
        };

        let mut result = ExhaustivenessResult {
            missing_patterns: Vec::new(),
            unreachable_patterns: Vec::new(),
            is_exhaustive: false,
        };

        check_integer_exhaustiveness(&match_stmt, &mut result).unwrap();

        assert!(!result.is_exhaustive);
        assert!(result.missing_patterns.contains(&"@default".to_string()));
    }

    #[test]
    fn test_duplicate_pattern_detected() {
        let enum_def = make_enum_def("Status", &["Ok", "Err"]);
        let match_stmt = MatchStmt {
            scrutinee: "x".to_string(),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Variant {
                        enum_name: make_id("Status"),
                        variant_name: make_id("Ok"),
                        binding: None,
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
                MatchArm {
                    pattern: Pattern::Variant {
                        enum_name: make_id("Status"),
                        variant_name: make_id("Ok"),
                        binding: None,
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
                MatchArm {
                    pattern: Pattern::Variant {
                        enum_name: make_id("Status"),
                        variant_name: make_id("Err"),
                        binding: None,
                        span: make_span(),
                    },
                    body: vec![],
                    span: make_span(),
                },
            ],
            default: None,
            span: make_span(),
        };

        let mut result = ExhaustivenessResult {
            missing_patterns: Vec::new(),
            unreachable_patterns: Vec::new(),
            is_exhaustive: false,
        };

        check_enum_exhaustiveness(&match_stmt, &enum_def, &mut result).unwrap();

        assert_eq!(result.unreachable_patterns.len(), 1);
        assert_eq!(result.unreachable_patterns[0].pattern_desc, "Status::Ok");
    }
}
