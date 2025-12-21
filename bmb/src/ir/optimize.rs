//! IR Optimization Passes
//!
//! Optimizations performed on the IR representation:
//! - Function inlining
//! - Dead code elimination
//! - Constant propagation
//! - Copy propagation

use std::collections::{HashMap, HashSet};

use super::types::*;

/// Default inline threshold (max instructions to inline)
const DEFAULT_INLINE_THRESHOLD: usize = 10;

/// Maximum inlining depth to prevent infinite recursion
const MAX_INLINE_DEPTH: usize = 3;

/// Run all IR optimizations
pub fn optimize_ir(program: &mut IrProgram, aggressive: bool) {
    // First pass: inline small functions
    let threshold = if aggressive {
        DEFAULT_INLINE_THRESHOLD * 2
    } else {
        DEFAULT_INLINE_THRESHOLD
    };

    inline_functions(program, threshold);

    // Second pass: clean up after inlining
    for func in &mut program.functions {
        remove_nops(func);
        eliminate_dead_code(func);
        if aggressive {
            propagate_constants(func);
            propagate_copies(func);
        }
    }
}

/// Inline function calls for small functions
pub fn inline_functions(program: &mut IrProgram, threshold: usize) {
    // Build map of inlinable functions
    let inline_candidates: HashMap<String, IrFunction> = program
        .functions
        .iter()
        .filter(|f| f.should_inline(threshold))
        .map(|f| (f.name.clone(), f.clone()))
        .collect();

    // Inline into each function
    for func in &mut program.functions {
        inline_calls_in_function(func, &inline_candidates, 0);
    }
}

/// Inline calls within a single function
fn inline_calls_in_function(
    func: &mut IrFunction,
    candidates: &HashMap<String, IrFunction>,
    depth: usize,
) {
    if depth >= MAX_INLINE_DEPTH {
        return;
    }

    let mut i = 0;
    let mut label_counter = 0;

    while i < func.body.len() {
        if let IrInst::Call { dest, func: callee, args } = &func.body[i] {
            // Don't inline recursive calls
            if callee == &func.name {
                i += 1;
                continue;
            }

            if let Some(inline_func) = candidates.get(callee) {
                // Inline the function
                let inlined = inline_call(
                    dest.clone(),
                    args,
                    inline_func,
                    &mut label_counter,
                    &func.name,
                );

                // Replace call with inlined body
                func.body.remove(i);
                for (j, inst) in inlined.into_iter().enumerate() {
                    func.body.insert(i + j, inst);
                }

                // Don't increment i, check the newly inserted instructions
                continue;
            }
        }
        i += 1;
    }
}

/// Generate inlined code for a function call
fn inline_call(
    dest: Option<Reg>,
    args: &[Reg],
    callee: &IrFunction,
    label_counter: &mut usize,
    caller_name: &str,
) -> Vec<IrInst> {
    let mut result = Vec::new();
    let suffix = format!("_inline_{}_{}", caller_name, *label_counter);
    *label_counter += 1;

    // Create register renaming map
    let mut reg_map: HashMap<String, Reg> = HashMap::new();

    // Map parameters to arguments
    for (param, arg) in callee.params.iter().zip(args.iter()) {
        reg_map.insert(param.name.clone(), arg.clone());
    }

    // Create fresh names for local registers
    let mut temp_counter = 0;
    for inst in &callee.body {
        if let Some(def) = inst.dest() {
            if !reg_map.contains_key(&def.0) {
                let fresh = Reg::new(format!("{}_{}{}", def.0, suffix, temp_counter));
                reg_map.insert(def.0.clone(), fresh);
                temp_counter += 1;
            }
        }
    }

    // Map result register if needed
    if let Some(ref d) = dest {
        reg_map.insert("result".to_string(), d.clone());
    }

    // Rename labels to avoid conflicts
    let mut label_map: HashMap<String, Label> = HashMap::new();
    for inst in &callee.body {
        if let IrInst::Label { name } = inst {
            let fresh = Label::new(format!("{}{}", name.0, suffix));
            label_map.insert(name.0.clone(), fresh);
        }
    }

    // Generate inlined instructions
    for inst in &callee.body {
        let renamed = rename_instruction(inst, &reg_map, &label_map);

        // Handle return specially - convert to move + jump to end
        match renamed {
            IrInst::Ret { value: Some(val) } => {
                if let Some(ref d) = dest {
                    if val != *d {
                        result.push(IrInst::MovReg {
                            dest: d.clone(),
                            src: val,
                        });
                    }
                }
                // Returns become no-ops in inlined code
                // (control flow continues after inline site)
            }
            IrInst::Ret { value: None } => {
                // Void return - just continue
            }
            other => {
                result.push(other);
            }
        }
    }

    result
}

/// Rename registers and labels in an instruction
fn rename_instruction(
    inst: &IrInst,
    reg_map: &HashMap<String, Reg>,
    label_map: &HashMap<String, Label>,
) -> IrInst {
    let rename_reg = |r: &Reg| -> Reg {
        reg_map.get(&r.0).cloned().unwrap_or_else(|| r.clone())
    };

    let rename_label = |l: &Label| -> Label {
        label_map.get(&l.0).cloned().unwrap_or_else(|| l.clone())
    };

    match inst {
        IrInst::MovConst { dest, value } => IrInst::MovConst {
            dest: rename_reg(dest),
            value: value.clone(),
        },
        IrInst::MovReg { dest, src } => IrInst::MovReg {
            dest: rename_reg(dest),
            src: rename_reg(src),
        },
        IrInst::BinOp { dest, op, left, right } => IrInst::BinOp {
            dest: rename_reg(dest),
            op: *op,
            left: rename_reg(left),
            right: rename_reg(right),
        },
        IrInst::UnaryOp { dest, op, operand } => IrInst::UnaryOp {
            dest: rename_reg(dest),
            op: *op,
            operand: rename_reg(operand),
        },
        IrInst::Call { dest, func, args } => IrInst::Call {
            dest: dest.as_ref().map(rename_reg),
            func: func.clone(),
            args: args.iter().map(rename_reg).collect(),
        },
        IrInst::ExternCall { dest, module, func, args } => IrInst::ExternCall {
            dest: dest.as_ref().map(rename_reg),
            module: module.clone(),
            func: func.clone(),
            args: args.iter().map(rename_reg).collect(),
        },
        IrInst::Ret { value } => IrInst::Ret {
            value: value.as_ref().map(rename_reg),
        },
        IrInst::BranchIf { cond, target } => IrInst::BranchIf {
            cond: rename_reg(cond),
            target: rename_label(target),
        },
        IrInst::Jump { target } => IrInst::Jump {
            target: rename_label(target),
        },
        IrInst::Label { name } => IrInst::Label {
            name: rename_label(name),
        },
        IrInst::Nop => IrInst::Nop,
    }
}

/// Remove NOP instructions
fn remove_nops(func: &mut IrFunction) {
    func.body.retain(|inst| !matches!(inst, IrInst::Nop));
}

/// Eliminate dead code (unreachable instructions after returns/jumps)
fn eliminate_dead_code(func: &mut IrFunction) {
    // Find all labels that are jump targets
    let mut jump_targets: HashSet<String> = HashSet::new();
    for inst in &func.body {
        match inst {
            IrInst::Jump { target } | IrInst::BranchIf { target, .. } => {
                jump_targets.insert(target.0.clone());
            }
            _ => {}
        }
    }

    // Remove unreachable code after terminators (except labels)
    let mut i = 0;
    while i < func.body.len() {
        let is_terminator = func.body[i].is_terminator();

        if is_terminator && i + 1 < func.body.len() {
            // Check if next instruction is a reachable label
            if let IrInst::Label { name } = &func.body[i + 1] {
                if jump_targets.contains(&name.0) {
                    i += 1;
                    continue;
                }
            }

            // Remove unreachable instruction unless it's a label
            if !matches!(&func.body[i + 1], IrInst::Label { .. }) {
                func.body.remove(i + 1);
                continue;
            }
        }
        i += 1;
    }
}

/// Propagate constant values through the function
fn propagate_constants(func: &mut IrFunction) {
    // Track known constant values
    let mut constants: HashMap<String, IrConst> = HashMap::new();

    for i in 0..func.body.len() {
        let replacement = match &func.body[i] {
            IrInst::MovConst { dest, value } => {
                constants.insert(dest.0.clone(), value.clone());
                None
            }
            IrInst::MovReg { dest, src } => {
                // If source is constant, propagate it
                if let Some(val) = constants.get(&src.0) {
                    let new_inst = IrInst::MovConst {
                        dest: dest.clone(),
                        value: val.clone(),
                    };
                    constants.insert(dest.0.clone(), val.clone());
                    Some(new_inst)
                } else {
                    constants.remove(&dest.0);
                    None
                }
            }
            IrInst::BinOp { dest, op, left, right } => {
                // Try to fold if both operands are constants
                let folded = constants
                    .get(&left.0)
                    .and_then(|l| constants.get(&right.0).map(|r| (l, r)))
                    .and_then(|(l, r)| fold_binop(*op, l, r));

                if let Some(result) = folded {
                    let new_inst = IrInst::MovConst {
                        dest: dest.clone(),
                        value: result.clone(),
                    };
                    constants.insert(dest.0.clone(), result);
                    Some(new_inst)
                } else {
                    constants.remove(&dest.0);
                    None
                }
            }
            other => {
                // Other instructions that define registers invalidate constants
                if let Some(d) = other.dest() {
                    constants.remove(&d.0);
                }
                None
            }
        };

        if let Some(new_inst) = replacement {
            func.body[i] = new_inst;
        }
    }
}

/// Fold a binary operation on constants
fn fold_binop(op: IrBinOp, left: &IrConst, right: &IrConst) -> Option<IrConst> {
    match (left, right) {
        (IrConst::I32(l), IrConst::I32(r)) => {
            Some(match op {
                IrBinOp::Add => IrConst::I32(l.wrapping_add(*r)),
                IrBinOp::Sub => IrConst::I32(l.wrapping_sub(*r)),
                IrBinOp::Mul => IrConst::I32(l.wrapping_mul(*r)),
                IrBinOp::Div if *r != 0 => IrConst::I32(l / r),
                IrBinOp::Mod if *r != 0 => IrConst::I32(l % r),
                IrBinOp::Eq => IrConst::Bool(l == r),
                IrBinOp::Ne => IrConst::Bool(l != r),
                IrBinOp::Lt => IrConst::Bool(l < r),
                IrBinOp::Le => IrConst::Bool(l <= r),
                IrBinOp::Gt => IrConst::Bool(l > r),
                IrBinOp::Ge => IrConst::Bool(l >= r),
                _ => return None,
            })
        }
        (IrConst::I64(l), IrConst::I64(r)) => {
            Some(match op {
                IrBinOp::Add => IrConst::I64(l.wrapping_add(*r)),
                IrBinOp::Sub => IrConst::I64(l.wrapping_sub(*r)),
                IrBinOp::Mul => IrConst::I64(l.wrapping_mul(*r)),
                IrBinOp::Div if *r != 0 => IrConst::I64(l / r),
                IrBinOp::Mod if *r != 0 => IrConst::I64(l % r),
                IrBinOp::Eq => IrConst::Bool(l == r),
                IrBinOp::Ne => IrConst::Bool(l != r),
                IrBinOp::Lt => IrConst::Bool(l < r),
                IrBinOp::Le => IrConst::Bool(l <= r),
                IrBinOp::Gt => IrConst::Bool(l > r),
                IrBinOp::Ge => IrConst::Bool(l >= r),
                _ => return None,
            })
        }
        (IrConst::Bool(l), IrConst::Bool(r)) => {
            Some(match op {
                IrBinOp::And => IrConst::Bool(*l && *r),
                IrBinOp::Or => IrConst::Bool(*l || *r),
                IrBinOp::Eq => IrConst::Bool(l == r),
                IrBinOp::Ne => IrConst::Bool(l != r),
                _ => return None,
            })
        }
        _ => None,
    }
}

/// Propagate copies to eliminate redundant moves
fn propagate_copies(func: &mut IrFunction) {
    // Track which registers are copies of other registers
    let mut copies: HashMap<String, Reg> = HashMap::new();

    for inst in &mut func.body {
        // Substitute known copies in uses
        let substitute_uses = |r: &Reg, copies: &HashMap<String, Reg>| -> Reg {
            let mut current = r.clone();
            // Follow copy chain (max 10 to prevent infinite loops)
            for _ in 0..10 {
                if let Some(src) = copies.get(&current.0) {
                    current = src.clone();
                } else {
                    break;
                }
            }
            current
        };

        match inst {
            IrInst::MovReg { dest, src } => {
                let actual_src = substitute_uses(src, &copies);
                if actual_src != *src {
                    *src = actual_src.clone();
                }
                copies.insert(dest.0.clone(), actual_src);
            }
            IrInst::BinOp { dest, left, right, .. } => {
                *left = substitute_uses(left, &copies);
                *right = substitute_uses(right, &copies);
                copies.remove(&dest.0);
            }
            IrInst::UnaryOp { dest, operand, .. } => {
                *operand = substitute_uses(operand, &copies);
                copies.remove(&dest.0);
            }
            IrInst::Call { dest, args, .. } | IrInst::ExternCall { dest, args, .. } => {
                for arg in args {
                    *arg = substitute_uses(arg, &copies);
                }
                if let Some(d) = dest {
                    copies.remove(&d.0);
                }
            }
            IrInst::Ret { value } => {
                if let Some(v) = value {
                    *v = substitute_uses(v, &copies);
                }
            }
            IrInst::BranchIf { cond, .. } => {
                *cond = substitute_uses(cond, &copies);
            }
            IrInst::Label { .. } => {
                // Labels are merge points - invalidate all copies
                copies.clear();
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_simple_func(name: &str, body: Vec<IrInst>) -> IrFunction {
        let mut func = IrFunction::new(name);
        func.body = body;
        func.instruction_count = func.count_instructions();
        func
    }

    #[test]
    fn test_inline_simple_function() {
        // Callee: fn const42() -> i32 { return 42 }
        let callee = make_simple_func(
            "const42",
            vec![
                IrInst::MovConst {
                    dest: Reg::result(),
                    value: IrConst::I32(42),
                },
                IrInst::Ret {
                    value: Some(Reg::result()),
                },
            ],
        );

        // Caller: fn main() { call const42() }
        let mut caller = make_simple_func(
            "main",
            vec![
                IrInst::Call {
                    dest: Some(Reg::result()),
                    func: "const42".to_string(),
                    args: vec![],
                },
                IrInst::Ret {
                    value: Some(Reg::result()),
                },
            ],
        );

        let mut program = IrProgram {
            imports: vec![],
            functions: vec![callee, caller.clone()],
        };

        inline_functions(&mut program, 10);

        let main = program.find_function("main").unwrap();

        // Call should be replaced with inlined code
        assert!(!main.body.iter().any(|i| matches!(i, IrInst::Call { .. })));
        // Should have a MovConst with 42
        assert!(main.body.iter().any(|i| matches!(
            i,
            IrInst::MovConst {
                value: IrConst::I32(42),
                ..
            }
        )));
    }

    #[test]
    fn test_inline_with_args() {
        // Callee: fn add(x, y) -> i32 { return x + y }
        let mut callee = IrFunction::new("add");
        callee.params = vec![
            IrParam {
                name: "x".to_string(),
                ty: IrType::I32,
            },
            IrParam {
                name: "y".to_string(),
                ty: IrType::I32,
            },
        ];
        callee.return_type = IrType::I32;
        callee.body = vec![
            IrInst::BinOp {
                dest: Reg::result(),
                op: IrBinOp::Add,
                left: Reg::new("x"),
                right: Reg::new("y"),
            },
            IrInst::Ret {
                value: Some(Reg::result()),
            },
        ];
        callee.instruction_count = 2;

        // Caller: fn main() { call add(a, b) }
        let caller = make_simple_func(
            "main",
            vec![
                IrInst::MovConst {
                    dest: Reg::new("a"),
                    value: IrConst::I32(10),
                },
                IrInst::MovConst {
                    dest: Reg::new("b"),
                    value: IrConst::I32(20),
                },
                IrInst::Call {
                    dest: Some(Reg::result()),
                    func: "add".to_string(),
                    args: vec![Reg::new("a"), Reg::new("b")],
                },
                IrInst::Ret {
                    value: Some(Reg::result()),
                },
            ],
        );

        let mut program = IrProgram {
            imports: vec![],
            functions: vec![callee, caller],
        };

        inline_functions(&mut program, 10);

        let main = program.find_function("main").unwrap();

        // Call should be inlined
        assert!(!main.body.iter().any(|i| matches!(i, IrInst::Call { .. })));
        // Should have a BinOp::Add
        assert!(main.body.iter().any(|i| matches!(
            i,
            IrInst::BinOp {
                op: IrBinOp::Add,
                ..
            }
        )));
    }

    #[test]
    fn test_no_inline_large_function() {
        // Large function (>threshold instructions)
        let mut large_body = Vec::new();
        for i in 0..20 {
            large_body.push(IrInst::MovConst {
                dest: Reg::temp(i),
                value: IrConst::I32(i as i32),
            });
        }
        large_body.push(IrInst::Ret {
            value: Some(Reg::temp(0)),
        });

        let large_func = make_simple_func("large", large_body);

        let caller = make_simple_func(
            "main",
            vec![
                IrInst::Call {
                    dest: Some(Reg::result()),
                    func: "large".to_string(),
                    args: vec![],
                },
                IrInst::Ret {
                    value: Some(Reg::result()),
                },
            ],
        );

        let mut program = IrProgram {
            imports: vec![],
            functions: vec![large_func, caller],
        };

        inline_functions(&mut program, 10);

        let main = program.find_function("main").unwrap();

        // Call should NOT be inlined (function too large)
        assert!(main.body.iter().any(|i| matches!(i, IrInst::Call { .. })));
    }

    #[test]
    fn test_constant_propagation() {
        let mut func = make_simple_func(
            "test",
            vec![
                IrInst::MovConst {
                    dest: Reg::new("a"),
                    value: IrConst::I32(10),
                },
                IrInst::MovConst {
                    dest: Reg::new("b"),
                    value: IrConst::I32(20),
                },
                IrInst::BinOp {
                    dest: Reg::result(),
                    op: IrBinOp::Add,
                    left: Reg::new("a"),
                    right: Reg::new("b"),
                },
                IrInst::Ret {
                    value: Some(Reg::result()),
                },
            ],
        );

        propagate_constants(&mut func);

        // The BinOp should be folded to MovConst 30
        assert!(func.body.iter().any(|i| matches!(
            i,
            IrInst::MovConst {
                dest,
                value: IrConst::I32(30)
            } if dest.0 == "result"
        )));
    }

    #[test]
    fn test_dead_code_elimination() {
        let mut func = make_simple_func(
            "test",
            vec![
                IrInst::Ret {
                    value: Some(Reg::new("x")),
                },
                // Dead code after return
                IrInst::MovConst {
                    dest: Reg::new("y"),
                    value: IrConst::I32(42),
                },
            ],
        );

        eliminate_dead_code(&mut func);

        // Dead code should be removed
        assert_eq!(func.body.len(), 1);
        assert!(matches!(&func.body[0], IrInst::Ret { .. }));
    }

    #[test]
    fn test_copy_propagation() {
        let mut func = make_simple_func(
            "test",
            vec![
                IrInst::MovConst {
                    dest: Reg::new("a"),
                    value: IrConst::I32(42),
                },
                IrInst::MovReg {
                    dest: Reg::new("b"),
                    src: Reg::new("a"),
                },
                IrInst::MovReg {
                    dest: Reg::new("c"),
                    src: Reg::new("b"),
                },
                IrInst::Ret {
                    value: Some(Reg::new("c")),
                },
            ],
        );

        propagate_copies(&mut func);

        // The return should use 'a' directly (through copy chain)
        if let IrInst::Ret { value: Some(reg) } = &func.body[3] {
            assert_eq!(reg.0, "a");
        } else {
            panic!("Expected Ret instruction");
        }
    }
}
