use crate::parser;
use crate::vm;

fn generate(ast: &parser::AST, vm: &mut vm::VirtualMachine, instr: &mut Vec<vm::Opcode>) {
    match ast {
        parser::AST::BinaryOp(op, lhs, rhs) => {
            generate(rhs, vm, instr);
            generate(lhs, vm, instr);
            match op {
                parser::Operator::And => {
                    instr.push(vm::Opcode::And);
                }
                parser::Operator::Divide => {
                    instr.push(vm::Opcode::Div);
                }
                parser::Operator::Equal => {
                    instr.push(vm::Opcode::Equal);
                }
                parser::Operator::Greater => {
                    instr.push(vm::Opcode::Greater);
                }
                parser::Operator::GreaterEqual => {
                    instr.push(vm::Opcode::GreaterEqual);
                }
                parser::Operator::Less => {
                    instr.push(vm::Opcode::Less);
                }
                parser::Operator::LessEqual => {
                    instr.push(vm::Opcode::LessEqual);
                }
                parser::Operator::Minus => {
                    instr.push(vm::Opcode::Sub);
                }
                parser::Operator::Mod => {
                    instr.push(vm::Opcode::Mod);
                }
                parser::Operator::Multiply => {
                    instr.push(vm::Opcode::Mul);
                }
                parser::Operator::Not => {
                    instr.push(vm::Opcode::Not);
                }
                parser::Operator::NotEqual => {
                    instr.push(vm::Opcode::NotEqual);
                }
                parser::Operator::Or => {
                    instr.push(vm::Opcode::Or);
                }
                parser::Operator::Plus => {
                    instr.push(vm::Opcode::Add);
                }
            }
        }
        parser::AST::Boolean(b) => {
            instr.push(vm::Opcode::Bconst(*b));
        }
        parser::AST::Integer(i) => {
            instr.push(vm::Opcode::Iconst(*i));
        }
        parser::AST::UnaryOp(op, ast) => {
            generate(ast, vm, instr);
            match op {
                parser::Operator::Minus => {
                    instr.push(vm::Opcode::Iconst(0));
                    instr.push(vm::Opcode::Sub);
                }
                parser::Operator::Not => {
                    instr.push(vm::Opcode::Not);
                }
                _ => unreachable!(),
            }
        }
        parser::AST::None => {}
    }
}

pub fn eval(vm: &mut vm::VirtualMachine, ast: &parser::AST) -> Result<i64, vm::RuntimeError> {
    let mut instr = Vec::new();
    generate(ast, vm, &mut instr);
    vm.ip = vm.instructions.len();
    vm.instructions.extend(instr);

    match vm.run() {
        Ok(()) => match vm.stack.pop() {
            Some(v) => Ok(v),
            None => {
                return Err(vm::RuntimeError {
                    err: "Stack underflow.".to_string(),
                    line: usize::max_value(),
                    col: usize::max_value(),
                });
            }
        },
        Err(e) => Err(e),
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter;
    use crate::parser;
    use crate::vm;

    macro_rules! eval {
        ($input:expr, $value:expr) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match interpreter::eval(&mut vm, &ast) {
                    Ok(v) => {
                        assert_eq!(v, $value);
                    }
                    Err(_) => {
                        assert!(false);
                    }
                },
                parser::ParseResult::NotMatched(_) => {
                    assert!(false);
                }
                parser::ParseResult::Error(_, _, _) => {
                    assert!(false);
                }
            }
        }};
    }

    #[test]
    fn evals() {
        eval!("1 + 2", 3);
        eval!("1 - 2", -1);
        eval!("1 * 2", 2);
        eval!("4 / 2", 2);
        eval!("true && false", 0);
        eval!("true || false", 1);
        eval!("21 % 6", 3);
        eval!("!true", 0);
        eval!("-42", -42);
        eval!("1 < 2", 1);
        eval!("2 <= 2", 1);
        eval!("2 == 2", 1);
        eval!("2 != 2", 0);
        eval!("1 > 2", 0);
        eval!("2 >= 2", 1);
        eval!("5 * 4 * 3 * 2 * 1", 120);
    }
}
