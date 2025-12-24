//! Frame Inference Module
//!
//! Analyzes function bodies to detect memory modifications and suggest @modifies clauses.
//!
//! ## Algorithm (Based on SPARK Ada/Frama-C research)
//!
//! 1. Scan all `Store`, `Box` opcodes in function body
//! 2. Track destination registers/memory locations
//! 3. Perform simple alias analysis for pointers
//! 4. Generate @modifies suggestions with confidence scores
//!
//! ## Confidence Scoring
//!
//! - 1.0: Direct register assignment (mov, arithmetic)
//! - 0.9: Direct memory store to known location
//! - 0.7: Heap allocation (Box)
//! - 0.5: Aliased memory write
//! - 0.3: Indirect write via computed address

use crate::ast::{Instruction, Node, Opcode, Operand, Statement, Type};
use crate::types::TypedNode;

use super::{MemoryLocation, Suggestion, SuggestionKind, SuggestedExpr};
use std::collections::{HashMap, HashSet};

/// Frame analysis result for a single function
#[derive(Debug, Clone)]
pub struct FrameAnalysis {
    /// Memory locations that are definitely modified
    pub definitely_modified: HashSet<MemoryLocation>,
    /// Memory locations that may be modified (aliasing uncertainty)
    pub maybe_modified: HashSet<MemoryLocation>,
    /// Registers that are written to
    pub written_registers: HashSet<String>,
    /// Parameters that may be modified (if passed by reference)
    pub modified_params: HashSet<String>,
}

impl FrameAnalysis {
    pub fn new() -> Self {
        Self {
            definitely_modified: HashSet::new(),
            maybe_modified: HashSet::new(),
            written_registers: HashSet::new(),
            modified_params: HashSet::new(),
        }
    }

    /// Merge another analysis result into this one
    pub fn merge(&mut self, other: &FrameAnalysis) {
        self.definitely_modified
            .extend(other.definitely_modified.iter().cloned());
        self.maybe_modified
            .extend(other.maybe_modified.iter().cloned());
        self.written_registers
            .extend(other.written_registers.iter().cloned());
        self.modified_params
            .extend(other.modified_params.iter().cloned());
    }
}

impl Default for FrameAnalysis {
    fn default() -> Self {
        Self::new()
    }
}

/// Simple points-to analysis for alias tracking
#[derive(Debug, Clone, Default)]
struct PointsToGraph {
    /// Maps pointer registers to their possible targets
    points_to: HashMap<String, HashSet<String>>,
}

impl PointsToGraph {
    fn new() -> Self {
        Self::default()
    }

    /// Record that `ptr` may point to `target`
    fn add_points_to(&mut self, ptr: &str, target: &str) {
        self.points_to
            .entry(ptr.to_string())
            .or_default()
            .insert(target.to_string());
    }

    /// Get all possible targets of a pointer
    fn get_targets(&self, ptr: &str) -> Option<&HashSet<String>> {
        self.points_to.get(ptr)
    }

    /// Check if pointer may alias with another
    #[allow(dead_code)]
    fn may_alias(&self, ptr1: &str, ptr2: &str) -> bool {
        if ptr1 == ptr2 {
            return true;
        }
        if let (Some(t1), Some(t2)) = (self.points_to.get(ptr1), self.points_to.get(ptr2)) {
            return !t1.is_disjoint(t2);
        }
        // Conservative: unknown pointers may alias
        true
    }
}

/// Analyze a function to detect memory modifications
pub fn analyze_frame(node: &Node, _typed_node: &TypedNode) -> Vec<Suggestion> {
    let mut analysis = FrameAnalysis::new();
    let mut points_to = PointsToGraph::new();

    // Build parameter set for reference tracking
    let mut ref_params: HashSet<String> = HashSet::new();
    let mut ptr_params: HashSet<String> = HashSet::new();

    for param in &node.params {
        let is_ref = matches!(param.ty, Type::Ref(_));
        let is_ptr = matches!(param.ty, Type::Ptr(_));

        if is_ref {
            ref_params.insert(param.name.name.clone());
        }
        if is_ptr {
            ptr_params.insert(param.name.name.clone());
            // Initialize points-to for pointer params (they point to external memory)
            points_to.add_points_to(&param.name.name, &format!("*{}", param.name.name));
        }
    }

    // Analyze each instruction
    for instr in &node.body {
        analyze_instruction(instr, &mut analysis, &mut points_to, &ref_params, &ptr_params);
    }

    // Generate suggestions
    generate_suggestions(&node.name.name, &analysis, &ref_params)
}

/// Analyze a single instruction for frame effects
fn analyze_instruction(
    instr: &Instruction,
    analysis: &mut FrameAnalysis,
    points_to: &mut PointsToGraph,
    ref_params: &HashSet<String>,
    ptr_params: &HashSet<String>,
) {
    match instr {
        Instruction::Statement(stmt) => {
            analyze_statement(stmt, analysis, points_to, ref_params, ptr_params);
        }
        Instruction::Match(match_stmt) => {
            // Analyze all arms
            for arm in &match_stmt.arms {
                for instr in &arm.body {
                    analyze_instruction(instr, analysis, points_to, ref_params, ptr_params);
                }
            }
            if let Some(default) = &match_stmt.default {
                for instr in &default.body {
                    analyze_instruction(instr, analysis, points_to, ref_params, ptr_params);
                }
            }
        }
        Instruction::Label(_) => {
            // Labels don't modify memory
        }
    }
}

/// Analyze a single statement for frame effects
fn analyze_statement(
    stmt: &Statement,
    analysis: &mut FrameAnalysis,
    points_to: &mut PointsToGraph,
    ref_params: &HashSet<String>,
    ptr_params: &HashSet<String>,
) {
    match stmt.opcode {
        // Register writes (internal, usually not part of @modifies)
        Opcode::Mov | Opcode::Add | Opcode::Sub | Opcode::Mul | Opcode::Div | Opcode::Mod
        | Opcode::And | Opcode::Or | Opcode::Xor | Opcode::Shl | Opcode::Shr | Opcode::Not
        | Opcode::Eq | Opcode::Ne | Opcode::Lt | Opcode::Le | Opcode::Gt | Opcode::Ge => {
            // These write to a destination register
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                analysis.written_registers.insert(dest_id.name.clone());

                // Track if mov copies a pointer
                if stmt.opcode == Opcode::Mov && stmt.operands.len() >= 2 {
                    if let Some(Operand::Identifier(src)) = stmt.operands.get(1) {
                        if ptr_params.contains(&src.name) {
                            // dest now points to same location as src
                            if let Some(targets) = points_to.get_targets(&src.name).cloned() {
                                for t in targets {
                                    points_to.add_points_to(&dest_id.name, &t);
                                }
                            }
                        }
                    }
                }
            }
        }

        // Memory store - this IS a frame effect
        Opcode::Store => {
            // store %ptr %value - writes to memory at ptr
            if let Some(operand) = stmt.operands.first() {
                let loc = operand_to_memory_location(operand, ref_params, points_to);
                analysis.definitely_modified.insert(loc);
            }
        }

        // Load doesn't modify memory (reads only)
        Opcode::Load => {
            // Track destination register
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                analysis.written_registers.insert(dest_id.name.clone());
            }
        }

        // Heap allocation - modifies heap memory
        Opcode::Box => {
            // box %dest %src - allocates and returns pointer in dest
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                analysis.written_registers.insert(dest_id.name.clone());
                // Record heap modification
                let loc = MemoryLocation::HeapLocation(dest_id.name.clone());
                analysis.definitely_modified.insert(loc);
                // dest points to new heap location
                points_to.add_points_to(&dest_id.name, &format!("heap:{}", dest_id.name));
            }
        }

        // Unbox reads from heap
        Opcode::Unbox => {
            if let Some(Operand::Register(dest_id)) = stmt.operands.first() {
                analysis.written_registers.insert(dest_id.name.clone());
            }
        }

        // Drop marks memory as freed (frame effect for completeness)
        Opcode::Drop => {
            // Currently no-op with bump allocator
            // Future: track deallocation
        }

        // Function calls may have side effects
        Opcode::Call | Opcode::Xcall => {
            // Conservative: mark as potentially modifying anything passed by ref
            for operand in stmt.operands.iter().skip(1) {
                // Skip return register for Call
                if let Operand::Identifier(id) = operand {
                    if ref_params.contains(&id.name) || ptr_params.contains(&id.name) {
                        analysis.modified_params.insert(id.name.clone());
                        analysis
                            .maybe_modified
                            .insert(MemoryLocation::Parameter(id.name.clone()));
                    }
                }
            }
        }

        // Print is I/O, not memory modification (but has side effects)
        Opcode::Print => {
            // Frame doesn't track I/O effects
        }

        // Control flow doesn't modify memory directly
        Opcode::Ret | Opcode::Jmp | Opcode::Jif => {}
    }
}

/// Convert an operand to a memory location
fn operand_to_memory_location(
    operand: &Operand,
    ref_params: &HashSet<String>,
    points_to: &PointsToGraph,
) -> MemoryLocation {
    match operand {
        Operand::Register(id) => {
            // Check if this register points to something
            if let Some(targets) = points_to.get_targets(&id.name) {
                if targets.len() == 1 {
                    let target = targets.iter().next().unwrap();
                    if target.starts_with("heap:") {
                        return MemoryLocation::HeapLocation(id.name.clone());
                    }
                    if target.starts_with('*') {
                        return MemoryLocation::Parameter(target[1..].to_string());
                    }
                }
            }
            MemoryLocation::Register(id.name.clone())
        }
        Operand::Identifier(id) => {
            if ref_params.contains(&id.name) {
                MemoryLocation::Parameter(id.name.clone())
            } else {
                MemoryLocation::Register(id.name.clone())
            }
        }
        Operand::ArrayAccess { base, index } => {
            let index_str = operand_to_string(index);
            MemoryLocation::ArrayElement {
                base: base.name.clone(),
                index: index_str,
            }
        }
        Operand::FieldAccess { base, field } => {
            MemoryLocation::StructField {
                base: base.name.clone(),
                field: field.name.clone(),
            }
        }
        _ => MemoryLocation::Register("<unknown>".to_string()),
    }
}

/// Convert an operand to a string for display
fn operand_to_string(operand: &Operand) -> String {
    match operand {
        Operand::Register(id) => format!("%{}", id.name),
        Operand::Identifier(id) => id.name.clone(),
        Operand::IntLiteral(n) => n.to_string(),
        Operand::FloatLiteral(f) => f.to_string(),
        Operand::Label(id) => format!("_{}", id.name),
        _ => "<complex>".to_string(),
    }
}

/// Generate suggestions from the analysis
fn generate_suggestions(
    node_name: &str,
    analysis: &FrameAnalysis,
    ref_params: &HashSet<String>,
) -> Vec<Suggestion> {
    let mut suggestions = Vec::new();

    // Collect all frame modifications (excluding internal registers)
    let mut frame_locations: Vec<MemoryLocation> = Vec::new();

    // Definitely modified locations
    for loc in &analysis.definitely_modified {
        match loc {
            // Skip internal registers (they're not observable externally)
            MemoryLocation::Register(name) if !ref_params.contains(name) => continue,
            _ => frame_locations.push(loc.clone()),
        }
    }

    // Maybe modified locations (lower confidence)
    for loc in &analysis.maybe_modified {
        if !frame_locations.contains(loc) {
            frame_locations.push(loc.clone());
        }
    }

    // Modified reference parameters
    for param in &analysis.modified_params {
        let loc = MemoryLocation::Parameter(param.clone());
        if !frame_locations.contains(&loc) {
            frame_locations.push(loc);
        }
    }

    // Calculate confidence based on analysis certainty
    let confidence = if analysis.maybe_modified.is_empty() {
        0.95 // High confidence if no aliasing uncertainty
    } else {
        0.7 // Lower if there's aliasing
    };

    // Generate suggestion
    let explanation = if frame_locations.is_empty() {
        "Function is pure (no memory modifications detected)".to_string()
    } else {
        format!(
            "Detected {} memory location(s) modified",
            frame_locations.len()
        )
    };

    suggestions.push(Suggestion {
        node_name: node_name.to_string(),
        kind: SuggestionKind::Frame,
        expr: SuggestedExpr::ModifiesSet(frame_locations),
        confidence,
        explanation,
    });

    suggestions
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Identifier, Span};

    fn make_span() -> Span {
        Span::new(0, 0, 1, 1)
    }

    fn make_id(name: &str) -> Identifier {
        Identifier::new(name, make_span())
    }

    fn make_stmt(opcode: Opcode, operands: Vec<Operand>) -> Statement {
        Statement {
            opcode,
            operands,
            span: make_span(),
        }
    }

    #[test]
    fn test_frame_analysis_store() {
        let mut analysis = FrameAnalysis::new();
        let mut points_to = PointsToGraph::new();
        let ref_params = HashSet::new();
        let ptr_params = HashSet::new();

        let store_stmt = make_stmt(
            Opcode::Store,
            vec![Operand::Register(make_id("ptr"))],
        );

        analyze_statement(
            &store_stmt,
            &mut analysis,
            &mut points_to,
            &ref_params,
            &ptr_params,
        );

        assert!(analysis.definitely_modified.contains(&MemoryLocation::Register("ptr".to_string())));
    }

    #[test]
    fn test_frame_analysis_box() {
        let mut analysis = FrameAnalysis::new();
        let mut points_to = PointsToGraph::new();
        let ref_params = HashSet::new();
        let ptr_params = HashSet::new();

        let box_stmt = make_stmt(
            Opcode::Box,
            vec![
                Operand::Register(make_id("dest")),
                Operand::Register(make_id("src")),
            ],
        );

        analyze_statement(
            &box_stmt,
            &mut analysis,
            &mut points_to,
            &ref_params,
            &ptr_params,
        );

        assert!(analysis.written_registers.contains("dest"));
        assert!(analysis.definitely_modified.contains(&MemoryLocation::HeapLocation("dest".to_string())));
    }

    #[test]
    fn test_points_to_tracking() {
        let mut graph = PointsToGraph::new();
        graph.add_points_to("p1", "x");
        graph.add_points_to("p2", "y");

        assert!(!graph.may_alias("p1", "p2"));

        graph.add_points_to("p2", "x");
        assert!(graph.may_alias("p1", "p2"));
    }
}
