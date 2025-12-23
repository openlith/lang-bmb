//! IR Lowering
//!
//! Converts TypedProgram (AST) to IrProgram (IR).

use std::collections::HashMap;

use crate::ast::{Instruction, Opcode, Operand, Statement};
use crate::types::TypedProgram;

use super::types::*;

/// Lower a TypedProgram to IrProgram
pub fn lower_program(program: &TypedProgram) -> IrProgram {
    let mut lowerer = IrLowerer::new();
    lowerer.lower(program)
}

/// IR lowering state
struct IrLowerer {
    /// Temporary register counter
    temp_counter: usize,
    /// Current function's register types
    reg_types: HashMap<String, IrType>,
}

impl IrLowerer {
    fn new() -> Self {
        IrLowerer {
            temp_counter: 0,
            reg_types: HashMap::new(),
        }
    }

    /// Get next temporary register
    fn next_temp(&mut self) -> Reg {
        let reg = Reg::temp(self.temp_counter);
        self.temp_counter += 1;
        reg
    }

    /// Lower entire program
    fn lower(&mut self, program: &TypedProgram) -> IrProgram {
        let mut ir = IrProgram::new();

        // Lower imports (simple imports have name and param_types)
        for import in &program.imports {
            // Parse import name for module.function format if present
            let (module, func) = if import.name.name.contains('.') {
                let parts: Vec<&str> = import.name.name.splitn(2, '.').collect();
                (parts[0].to_string(), parts[1].to_string())
            } else {
                ("env".to_string(), import.name.name.clone())
            };

            ir.imports.push(IrImport {
                module,
                func,
                params: import.param_types.iter().map(IrType::from).collect(),
                return_type: IrType::Void, // Imports don't specify return type in simple form
            });
        }

        // Lower functions
        for typed_node in &program.nodes {
            let func = self.lower_function(typed_node);
            ir.functions.push(func);
        }

        ir
    }

    /// Lower a function
    fn lower_function(&mut self, typed_node: &crate::types::TypedNode) -> IrFunction {
        let node = &typed_node.node;

        // Reset state for new function
        self.temp_counter = 0;
        self.reg_types.clear();

        let mut func = IrFunction::new(&node.name.name);

        // Lower parameters
        for param in &node.params {
            let ir_type = IrType::from(&param.ty);
            func.params.push(IrParam {
                name: param.name.name.clone(),
                ty: ir_type.clone(),
            });
            self.reg_types.insert(param.name.name.clone(), ir_type);
        }

        // Lower return type
        func.return_type = IrType::from(&node.returns);

        // Copy register types from type checker
        for (name, ty) in &typed_node.register_types {
            let ir_type = IrType::from(ty);
            self.reg_types.insert(name.clone(), ir_type);
        }

        // Lower body
        for instr in &node.body {
            match instr {
                Instruction::Label(ident) => {
                    let label_name = ident.name.trim_start_matches('_').to_string();
                    func.body.push(IrInst::Label {
                        name: Label::new(label_name),
                    });
                }
                Instruction::Statement(stmt) => {
                    self.lower_statement(stmt, &mut func.body);
                }
            }
        }

        // Update instruction count
        func.instruction_count = func.count_instructions();

        // Determine inline hint based on size
        func.inline_hint = if func.instruction_count <= 3 {
            InlineHint::Always
        } else if func.instruction_count > 20 {
            InlineHint::Never
        } else {
            InlineHint::Auto
        };

        func.reg_types = self.reg_types.clone();
        func
    }

    /// Extract destination register from statement operands
    /// In BMB, the first operand is typically the destination for most instructions
    fn extract_dest(&self, stmt: &Statement) -> Reg {
        if let Some(Operand::Register(ident)) = stmt.operands.first() {
            Reg::new(ident.name.trim_start_matches('%'))
        } else {
            Reg::result()
        }
    }

    /// Lower a statement to IR instructions
    fn lower_statement(&mut self, stmt: &Statement, body: &mut Vec<IrInst>) {
        match &stmt.opcode {
            Opcode::Mov => {
                // mov %dest value
                let dest = self.extract_dest(stmt);
                if stmt.operands.len() >= 2 {
                    self.lower_operand_to_reg(&stmt.operands[1], &dest, body);
                }
            }

            Opcode::Add | Opcode::Sub | Opcode::Mul | Opcode::Div | Opcode::Mod => {
                // add %dest %left %right
                let ir_op = match &stmt.opcode {
                    Opcode::Add => IrBinOp::Add,
                    Opcode::Sub => IrBinOp::Sub,
                    Opcode::Mul => IrBinOp::Mul,
                    Opcode::Div => IrBinOp::Div,
                    Opcode::Mod => IrBinOp::Mod,
                    _ => unreachable!(),
                };

                let dest = self.extract_dest(stmt);
                if stmt.operands.len() >= 3 {
                    let left = self.lower_operand(&stmt.operands[1], body);
                    let right = self.lower_operand(&stmt.operands[2], body);
                    body.push(IrInst::BinOp {
                        dest,
                        op: ir_op,
                        left,
                        right,
                    });
                }
            }

            // Bitwise operations
            Opcode::And | Opcode::Or | Opcode::Xor | Opcode::Shl | Opcode::Shr => {
                // and %dest %left %right
                let ir_op = match &stmt.opcode {
                    Opcode::And => IrBinOp::And,
                    Opcode::Or => IrBinOp::Or,
                    Opcode::Xor => IrBinOp::Xor,
                    Opcode::Shl => IrBinOp::Shl,
                    Opcode::Shr => IrBinOp::Shr,
                    _ => unreachable!(),
                };

                let dest = self.extract_dest(stmt);
                if stmt.operands.len() >= 3 {
                    let left = self.lower_operand(&stmt.operands[1], body);
                    let right = self.lower_operand(&stmt.operands[2], body);
                    body.push(IrInst::BinOp {
                        dest,
                        op: ir_op,
                        left,
                        right,
                    });
                }
            }

            Opcode::Not => {
                // not %dest %value - unary bitwise NOT
                let dest = self.extract_dest(stmt);
                if stmt.operands.len() >= 2 {
                    let operand = self.lower_operand(&stmt.operands[1], body);
                    body.push(IrInst::UnaryOp {
                        dest,
                        op: IrUnaryOp::Not,
                        operand,
                    });
                }
            }

            Opcode::Eq | Opcode::Ne | Opcode::Lt | Opcode::Le | Opcode::Gt | Opcode::Ge => {
                // eq %dest %left %right
                let ir_op = match &stmt.opcode {
                    Opcode::Eq => IrBinOp::Eq,
                    Opcode::Ne => IrBinOp::Ne,
                    Opcode::Lt => IrBinOp::Lt,
                    Opcode::Le => IrBinOp::Le,
                    Opcode::Gt => IrBinOp::Gt,
                    Opcode::Ge => IrBinOp::Ge,
                    _ => unreachable!(),
                };

                let dest = self.extract_dest(stmt);
                if stmt.operands.len() >= 3 {
                    let left = self.lower_operand(&stmt.operands[1], body);
                    let right = self.lower_operand(&stmt.operands[2], body);
                    body.push(IrInst::BinOp {
                        dest,
                        op: ir_op,
                        left,
                        right,
                    });
                }
            }

            Opcode::Ret => {
                // ret %value or ret literal
                let value = stmt.operands.first().map(|op| self.lower_operand(op, body));
                body.push(IrInst::Ret { value });
            }

            Opcode::Jmp => {
                // jmp _label
                if let Some(Operand::Label(ident)) = stmt.operands.first() {
                    let label_name = ident.name.trim_start_matches('_').to_string();
                    body.push(IrInst::Jump {
                        target: Label::new(label_name),
                    });
                }
            }

            Opcode::Jif => {
                // jif %cond _label
                if stmt.operands.len() >= 2 {
                    let cond = self.lower_operand(&stmt.operands[0], body);
                    if let Operand::Label(ident) = &stmt.operands[1] {
                        let label_name = ident.name.trim_start_matches('_').to_string();
                        body.push(IrInst::BranchIf {
                            cond,
                            target: Label::new(label_name),
                        });
                    }
                }
            }

            Opcode::Call => {
                // call %dest func_name args...
                // or call func_name args... (result in %result)
                if !stmt.operands.is_empty() {
                    // First operand could be dest register or function name
                    let (dest, func_name, args_start) =
                        if let Operand::Register(ident) = &stmt.operands[0] {
                            if stmt.operands.len() >= 2 {
                                if let Operand::Register(func_ident) = &stmt.operands[1] {
                                    (Some(Reg::new(&ident.name)), func_ident.name.clone(), 2)
                                } else {
                                    // First operand is the function name
                                    (Some(Reg::result()), ident.name.clone(), 1)
                                }
                            } else {
                                (Some(Reg::result()), ident.name.clone(), 1)
                            }
                        } else {
                            return; // Invalid call format
                        };

                    let args: Vec<Reg> = stmt.operands[args_start..]
                        .iter()
                        .map(|op| self.lower_operand(op, body))
                        .collect();

                    body.push(IrInst::Call {
                        dest,
                        func: func_name,
                        args,
                    });
                }
            }

            Opcode::Xcall => {
                // External call: xcall %dest module.func args...
                let dest = self.extract_dest(stmt);
                if stmt.operands.len() >= 2 {
                    if let Operand::Register(mod_func) = &stmt.operands[1] {
                        let (module, func) = if mod_func.name.contains('.') {
                            let parts: Vec<&str> = mod_func.name.splitn(2, '.').collect();
                            (parts[0].to_string(), parts[1].to_string())
                        } else {
                            ("env".to_string(), mod_func.name.clone())
                        };

                        let args: Vec<Reg> = stmt.operands[2..]
                            .iter()
                            .map(|op| self.lower_operand(op, body))
                            .collect();

                        body.push(IrInst::ExternCall {
                            dest: Some(dest),
                            module,
                            func,
                            args,
                        });
                    }
                }
            }

            // Handle other opcodes as no-ops for now
            Opcode::Load | Opcode::Store | Opcode::Print => {}
        }
    }

    /// Lower an operand, potentially emitting instructions
    fn lower_operand(&mut self, op: &Operand, body: &mut Vec<IrInst>) -> Reg {
        match op {
            Operand::Register(ident) => Reg::new(ident.name.trim_start_matches('%')),
            Operand::IntLiteral(v) => {
                let temp = self.next_temp();
                let value = if *v >= i32::MIN as i64 && *v <= i32::MAX as i64 {
                    IrConst::I32(*v as i32)
                } else {
                    IrConst::I64(*v)
                };
                body.push(IrInst::MovConst {
                    dest: temp.clone(),
                    value,
                });
                temp
            }
            Operand::FloatLiteral(v) => {
                let temp = self.next_temp();
                body.push(IrInst::MovConst {
                    dest: temp.clone(),
                    value: IrConst::F64(*v),
                });
                temp
            }
            Operand::Label(ident) => {
                // Labels are handled specially in control flow
                Reg::new(ident.name.trim_start_matches('_'))
            }
            Operand::StringLiteral(_) => {
                // Strings are lowered as pointers (not fully supported yet)
                let temp = self.next_temp();
                body.push(IrInst::MovConst {
                    dest: temp.clone(),
                    value: IrConst::I64(0),
                });
                temp
            }
            Operand::Identifier(ident) => {
                // Treat identifiers like registers
                Reg::new(ident.name.trim_start_matches('%'))
            }
            Operand::QualifiedIdent { module, name, .. } => {
                // Qualified identifiers become register references
                Reg::new(format!("{}_{}", module.name, name.name))
            }
            Operand::FieldAccess { base, field } => {
                // Field access: base is Identifier, create field reference
                let base_name = base.name.trim_start_matches('%');
                Reg::new(format!("{}.{}", base_name, field.name))
            }
            Operand::ArrayAccess { base, index } => {
                // Array access: base is Identifier, index is Box<Operand>
                let _base_name = base.name.trim_start_matches('%');
                let _index_reg = self.lower_operand(index, body);
                // Return a temp for the result
                self.next_temp()
            }
        }
    }

    /// Lower an operand directly to a destination register
    fn lower_operand_to_reg(&mut self, op: &Operand, dest: &Reg, body: &mut Vec<IrInst>) {
        match op {
            Operand::Register(ident) | Operand::Identifier(ident) => {
                let src_name = ident.name.trim_start_matches('%');
                if src_name != dest.0 {
                    body.push(IrInst::MovReg {
                        dest: dest.clone(),
                        src: Reg::new(src_name),
                    });
                }
            }
            Operand::IntLiteral(v) => {
                let value = if *v >= i32::MIN as i64 && *v <= i32::MAX as i64 {
                    IrConst::I32(*v as i32)
                } else {
                    IrConst::I64(*v)
                };
                body.push(IrInst::MovConst {
                    dest: dest.clone(),
                    value,
                });
            }
            Operand::FloatLiteral(v) => {
                body.push(IrInst::MovConst {
                    dest: dest.clone(),
                    value: IrConst::F64(*v),
                });
            }
            Operand::Label(_) => {
                // Labels shouldn't be moved to registers
            }
            Operand::StringLiteral(_) => {
                // Strings lowered as null pointers for now
                body.push(IrInst::MovConst {
                    dest: dest.clone(),
                    value: IrConst::I64(0),
                });
            }
            Operand::QualifiedIdent { module, name, .. } => {
                let src = Reg::new(format!("{}_{}", module.name, name.name));
                body.push(IrInst::MovReg {
                    dest: dest.clone(),
                    src,
                });
            }
            Operand::FieldAccess { base, field } => {
                let base_name = base.name.trim_start_matches('%');
                let src = Reg::new(format!("{}.{}", base_name, field.name));
                body.push(IrInst::MovReg {
                    dest: dest.clone(),
                    src,
                });
            }
            Operand::ArrayAccess { base, index } => {
                // Lower index, base is Identifier
                let _base_name = base.name.trim_start_matches('%');
                let _index_reg = self.lower_operand(index, body);
                // Placeholder: actual array access would generate load instruction
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Identifier, Node, Parameter, Span, Type};
    use crate::types::{TypeRegistry, TypedNode};

    fn make_typed_node(node: Node) -> TypedNode {
        TypedNode {
            node,
            register_types: HashMap::new(),
        }
    }

    fn make_param(name: &str, ty: Type) -> Parameter {
        Parameter {
            name: Identifier::new(name, Span::default()),
            ty,
            span: Span::default(),
        }
    }

    #[test]
    fn test_lower_simple_function() {
        // @node main
        // @returns i32
        //   mov %result 42
        //   ret %result
        let node = Node {
            name: Identifier::new("main", Span::default()),
            tags: vec![],
            params: vec![],
            returns: Type::I32,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body: vec![
                Instruction::Statement(Statement {
                    opcode: Opcode::Mov,
                    operands: vec![
                        Operand::Register(Identifier::new("result", Span::default())),
                        Operand::IntLiteral(42),
                    ],
                    span: Span::default(),
                }),
                Instruction::Statement(Statement {
                    opcode: Opcode::Ret,
                    operands: vec![Operand::Register(Identifier::new("result", Span::default()))],
                    span: Span::default(),
                }),
            ],
            span: Span::default(),
        };

        let program = TypedProgram {
            imports: vec![],
            structs: vec![],
            enums: vec![],
            contracts: vec![],
            nodes: vec![make_typed_node(node)],
            registry: TypeRegistry::new(),
        };

        let ir = lower_program(&program);

        assert_eq!(ir.functions.len(), 1);
        let func = &ir.functions[0];
        assert_eq!(func.name, "main");
        assert_eq!(func.return_type, IrType::I32);

        // Should have: mov %result 42, ret %result
        assert_eq!(func.body.len(), 2);
        assert!(matches!(&func.body[0], IrInst::MovConst { .. }));
        assert!(matches!(&func.body[1], IrInst::Ret { .. }));
    }

    #[test]
    fn test_lower_arithmetic() {
        // add %result %x %y
        let stmt = Statement {
            opcode: Opcode::Add,
            operands: vec![
                Operand::Register(Identifier::new("result", Span::default())),
                Operand::Register(Identifier::new("x", Span::default())),
                Operand::Register(Identifier::new("y", Span::default())),
            ],
            span: Span::default(),
        };

        let node = Node {
            name: Identifier::new("add_fn", Span::default()),
            tags: vec![],
            params: vec![make_param("x", Type::I32), make_param("y", Type::I32)],
            returns: Type::I32,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body: vec![Instruction::Statement(stmt)],
            span: Span::default(),
        };

        let program = TypedProgram {
            imports: vec![],
            structs: vec![],
            enums: vec![],
            contracts: vec![],
            nodes: vec![make_typed_node(node)],
            registry: TypeRegistry::new(),
        };

        let ir = lower_program(&program);
        let func = &ir.functions[0];

        assert_eq!(func.params.len(), 2);
        assert!(matches!(
            &func.body[0],
            IrInst::BinOp {
                op: IrBinOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn test_lower_control_flow() {
        // jif %cond _label
        // ret 0
        // _label:
        // ret 1
        let body = vec![
            Instruction::Statement(Statement {
                opcode: Opcode::Jif,
                operands: vec![
                    Operand::Register(Identifier::new("cond", Span::default())),
                    Operand::Label(Identifier::new("_done", Span::default())),
                ],
                span: Span::default(),
            }),
            Instruction::Statement(Statement {
                opcode: Opcode::Ret,
                operands: vec![Operand::IntLiteral(0)],
                span: Span::default(),
            }),
            Instruction::Label(Identifier::new("_done", Span::default())),
            Instruction::Statement(Statement {
                opcode: Opcode::Ret,
                operands: vec![Operand::IntLiteral(1)],
                span: Span::default(),
            }),
        ];

        let node = Node {
            name: Identifier::new("branch_fn", Span::default()),
            tags: vec![],
            params: vec![make_param("cond", Type::Bool)],
            returns: Type::I32,
            preconditions: vec![],
            postconditions: vec![],
            invariants: vec![],
            variants: vec![],
            pure: false,
            requires: vec![],
            assertions: vec![],
            tests: vec![],
            body,
            span: Span::default(),
        };

        let mut reg_types = HashMap::new();
        reg_types.insert("cond".to_string(), Type::Bool);

        let program = TypedProgram {
            imports: vec![],
            structs: vec![],
            enums: vec![],
            contracts: vec![],
            nodes: vec![TypedNode {
                node,
                register_types: reg_types,
            }],
            registry: TypeRegistry::new(),
        };

        let ir = lower_program(&program);
        let func = &ir.functions[0];

        // Should have: BranchIf, MovConst+Ret, Label, MovConst+Ret
        assert!(func
            .body
            .iter()
            .any(|inst| matches!(inst, IrInst::BranchIf { .. })));
        assert!(func
            .body
            .iter()
            .any(|inst| matches!(inst, IrInst::Label { .. })));
    }
}
