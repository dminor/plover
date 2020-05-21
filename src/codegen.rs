use crate::parser;
use crate::typeinfer::{infer, type_of, Type, TypedAST};
use crate::vm;
use std::collections::HashMap;
use std::collections::HashSet;
use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub struct InterpreterError {
    pub err: String,
    pub line: usize,
    pub col: usize,
}

impl fmt::Display for InterpreterError {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "InterpreterError: {}", self.err)
    }
}

impl Error for InterpreterError {}

fn find_upvalues(
    ast: &TypedAST,
    ids: &mut HashMap<String, usize>,
    upvalues: &mut HashMap<String, (usize, Type)>,
) {
    match ast {
        TypedAST::BinaryOp(_, _, lhs, rhs, _, _) => {
            find_upvalues(lhs, ids, upvalues);
            find_upvalues(rhs, ids, upvalues);
        }
        TypedAST::Call(fun, args) => {
            find_upvalues(fun, ids, upvalues);
            find_upvalues(args, ids, upvalues);
        }
        TypedAST::Define(_, id, value) => {
            // Shadow id while it is in scope
            if let Some(_) = ids.get(id) {
                ids.remove(id);
            }
            find_upvalues(value, ids, upvalues);
        }
        TypedAST::Function(_, param, body) => {
            let mut local_ids = ids.clone();
            find_upvalues(param, &mut local_ids, upvalues);
            find_upvalues(body, &mut local_ids, upvalues);
        }
        TypedAST::If(conds, els) => {
            for cond in conds {
                find_upvalues(&cond.0, ids, upvalues);
                find_upvalues(&cond.1, ids, upvalues);
            }
            find_upvalues(&els, ids, upvalues);
        }
        TypedAST::Identifier(typ, id) => match ids.get(id) {
            Some(offset) => {
                upvalues.insert(id.to_string(), (*offset, typ.clone()));
            }
            None => {}
        },
        TypedAST::Program(_, expressions) => {
            for expression in expressions {
                find_upvalues(expression, ids, upvalues);
            }
        }
        TypedAST::Tuple(_, elements) => {
            for element in elements {
                find_upvalues(element, ids, upvalues);
            }
        }
        TypedAST::UnaryOp(_, _, ast) => {
            find_upvalues(ast, ids, upvalues);
        }
        _ => {}
    }
}

fn generate(
    ast: &TypedAST,
    vm: &mut vm::VirtualMachine,
    instr: &mut Vec<vm::Opcode>,
    ids: &HashMap<String, usize>,
) {
    match ast {
        TypedAST::BinaryOp(_, op, lhs, rhs, line, col) => {
            instr.push(vm::Opcode::Srcpos(*line, *col));
            generate(rhs, vm, instr, ids);
            generate(lhs, vm, instr, ids);
            match op {
                parser::Operator::And => {
                    instr.push(vm::Opcode::And);
                }
                parser::Operator::Divide => {
                    instr.push(vm::Opcode::Div);
                }
                parser::Operator::Equal => {
                    if let Type::Tuple(types) = type_of(rhs) {
                        instr.push(vm::Opcode::Equal);
                        for _ in 1..types.len() {
                            instr.push(vm::Opcode::Rot);
                            instr.push(vm::Opcode::Equal);
                            instr.push(vm::Opcode::And);
                        }
                    } else {
                        instr.push(vm::Opcode::Equal);
                    }
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
                    if let Type::Tuple(types) = type_of(rhs) {
                        instr.push(vm::Opcode::NotEqual);
                        for _ in 1..types.len() {
                            instr.push(vm::Opcode::Rot);
                            instr.push(vm::Opcode::NotEqual);
                            instr.push(vm::Opcode::Or);
                        }
                    } else {
                        instr.push(vm::Opcode::NotEqual);
                    }
                }
                parser::Operator::Or => {
                    instr.push(vm::Opcode::Or);
                }
                parser::Operator::Plus => {
                    instr.push(vm::Opcode::Add);
                }
            }
        }
        TypedAST::Boolean(b) => {
            instr.push(vm::Opcode::Bconst(*b));
        }
        TypedAST::Call(fun, arg) => {
            generate(arg, vm, instr, ids);
            generate(fun, vm, instr, ids);
            instr.push(vm::Opcode::Call);
        }
        TypedAST::Datatype(typ, variants) => {
            for variant in variants {
                if let Type::Datatype(_) = &variant.1 {
                    instr.push(vm::Opcode::Uconst);
                    instr.push(vm::Opcode::Dconst(typ.to_string(), variant.0.to_string()));
                    instr.push(vm::Opcode::SetEnv(variant.0.to_string()));
                } else {
                    let mut fn_instr = Vec::new();
                    fn_instr.push(vm::Opcode::Dup);
                    fn_instr.push(vm::Opcode::Dconst(typ.to_string(), variant.0.to_string()));

                    fn_instr.push(vm::Opcode::Ret(1));
                    let ip = vm.instructions.len();
                    vm.instructions.extend(fn_instr);
                    instr.push(vm::Opcode::Fconst(None, ip, HashMap::new()));
                    instr.push(vm::Opcode::SetEnv(variant.0.to_string()));
                }
            }
            instr.push(vm::Opcode::Uconst);
        }
        TypedAST::Define(_, id, value) => {
            generate(&value, vm, instr, ids);
            instr.push(vm::Opcode::Dup);
            instr.push(vm::Opcode::SetEnv(id.to_string()));
        }
        TypedAST::Function(id, param, body) => {
            let mut fn_instr = Vec::new();
            let mut local_ids = ids.clone();
            let mut param_ids = HashSet::new();
            let mut count = 0;
            match &**param {
                TypedAST::Identifier(_, id) => {
                    count = 2;
                    local_ids.insert(id.to_string(), 0);
                    param_ids.insert(id.to_string());
                }
                TypedAST::Tuple(_, elements) => {
                    for element in elements {
                        if let TypedAST::Identifier(_, id) = element {
                            local_ids.insert(id.to_string(), count);
                            param_ids.insert(id.to_string());
                        }
                        count += 1;
                    }
                }
                TypedAST::Unit => {
                    count = 1;
                }
                _ => unreachable!(),
            }

            // We find the "upvalues", function arguments from enclosing
            // functions that are used in this function and place them in the
            // environment instead of retrieving them from the stack.
            let mut upvalues = HashMap::new();
            let mut upvalue_ids = ids.clone();
            find_upvalues(body, &mut upvalue_ids, &mut upvalues);
            for upvalue in &upvalues {
                let id = upvalue.0;
                if param_ids.contains(id) {
                    continue;
                }
                if let Some(_) = ids.get(id) {
                    local_ids.remove(id);
                }
            }

            generate(&body, vm, &mut fn_instr, &local_ids);
            fn_instr.push(vm::Opcode::Ret(count - 1));
            let ip = vm.instructions.len();
            vm.instructions.extend(fn_instr);
            instr.push(vm::Opcode::Fconst(id.clone(), ip, upvalues));

            if let Some(id) = id {
                instr.push(vm::Opcode::Dup);
                instr.push(vm::Opcode::SetEnv(id.to_string()));
            }
        }
        TypedAST::If(conds, els) => {
            let start_ip = instr.len();
            for cond in conds {
                let mut then = Vec::new();
                generate(&cond.0, vm, instr, ids);
                generate(&cond.1, vm, &mut then, ids);
                let offset = 2 + then.len() as i64;
                instr.push(vm::Opcode::Jz(offset));
                instr.extend(then);
                instr.push(vm::Opcode::Jmp(i64::max_value()));
            }
            generate(&els, vm, instr, ids);

            // TODO: this rewrites all jmp instructions to be past the end of
            // the if expression. This is safe as long as if is the only
            // expression for which we use jmp.
            for i in start_ip..instr.len() {
                if let vm::Opcode::Jmp(_) = instr[i] {
                    let offset = (instr.len() - i) as i64;
                    instr[i] = vm::Opcode::Jmp(offset);
                }
            }
        }
        TypedAST::Identifier(_, id) => match ids.get(id) {
            Some(offset) => instr.push(vm::Opcode::Arg(*offset)),
            None => {
                // type checking ensures this is a valid identifier
                instr.push(vm::Opcode::GetEnv(id.to_string()))
            }
        },
        TypedAST::Integer(i) => {
            instr.push(vm::Opcode::Iconst(*i));
        }
        TypedAST::Match(_, _, _) => {}
        TypedAST::Program(_, expressions) => {
            for i in 0..expressions.len() {
                generate(&expressions[i], vm, instr, ids);
                if i + 1 != expressions.len() {
                    instr.push(vm::Opcode::Pop);
                }
            }
        }
        TypedAST::Tuple(_, elements) => {
            for element in elements.iter().rev() {
                generate(&element, vm, instr, ids);
            }
        }
        TypedAST::UnaryOp(_, op, ast) => {
            generate(ast, vm, instr, ids);
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
        TypedAST::Unit => {
            instr.push(vm::Opcode::Uconst);
        }
    }
}

fn to_typed_value(vm: &mut vm::VirtualMachine, typ: &Type) -> Option<vm::Value> {
    match typ {
        Type::Tuple(types) => {
            let mut values = Vec::new();
            for i in 0..types.len() {
                match to_typed_value(vm, &types[types.len() - i - 1]) {
                    Some(value) => {
                        values.push(value);
                    }
                    None => {
                        return None;
                    }
                }
            }
            Some(vm::Value::Tuple(values))
        }
        _ => match vm.stack.pop() {
            Some(value) => Some(value),
            None => None,
        },
    }
}

pub fn eval(vm: &mut vm::VirtualMachine, ast: &parser::AST) -> Result<vm::Value, InterpreterError> {
    match infer(ast, &mut vm.env.types) {
        Ok(typed_ast) => {
            let mut instr = Vec::new();
            let ids = HashMap::new();
            generate(&typed_ast, vm, &mut instr, &ids);
            vm.ip = vm.instructions.len();
            vm.instructions.extend(instr);
            // TODO: This is useful for debugging. Add an argument to enable it.
            //println!("disassembly:");
            //for i in 0..vm.instructions.len() {
            //    println!("  {} {}", i, vm.instructions[i]);
            //}
            match vm.run() {
                Ok(()) => match to_typed_value(vm, &type_of(&typed_ast)) {
                    Some(value) => Ok(value),
                    None => Err(InterpreterError {
                        err: "Stack underflow.".to_string(),
                        line: usize::max_value(),
                        col: usize::max_value(),
                    }),
                },
                Err(err) => Err(err),
            }
        }
        Err(err) => {
            return Err(err);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::codegen;
    use crate::parser;
    use crate::vm;
    use crate::vm::Value;

    macro_rules! eval {
        ($input:expr, Datatype, $value:expr) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match codegen::eval(&mut vm, &ast) {
                    Ok(v) => match v {
                        Value::Datatype(_, _, v) => {
                            assert_eq!(v, $value);
                        }
                        _ => {
                            assert!(false);
                        }
                    },
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
        ($input:expr, Tuple, $($value:expr),*) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match codegen::eval(&mut vm, &ast) {
                    Ok(v) => match v {
                        Value::Tuple(elements) => {
                            let mut i = 0;
                            $(
                                assert!(i < elements.len());
                                assert_eq!(elements[i], $value);
                                i += 1;
                                assert!(i != 0);  // Silence warning
                            )*
                        }
                        _ => {
                            assert!(false);
                        }
                    },
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
        ($input:expr, Unit) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match codegen::eval(&mut vm, &ast) {
                    Ok(v) => {
                        assert_eq!(v, Value::Unit);
                    },
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
        ($input:expr, $type:tt, $value:expr) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match codegen::eval(&mut vm, &ast) {
                    Ok(v) => match v {
                        Value::$type(t) => {
                            assert_eq!(t, $value);
                        }
                        _ => {
                            assert!(false);
                        }
                    },
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

    macro_rules! evalfails {
        ($input:expr, $err:expr) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match codegen::eval(&mut vm, &ast) {
                    Ok(_) => {
                        assert!(false);
                    }
                    Err(err) => {
                        assert_eq!(err.err, $err);
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
        eval!("1 + 2", Integer, 3);
        eval!("1 - 2", Integer, -1);
        eval!("1 * 2", Integer, 2);
        eval!("4 / 2", Integer, 2);
        eval!("true && false", Boolean, false);
        eval!("true || false", Boolean, true);
        eval!("21 % 6", Integer, 3);
        eval!("~true", Boolean, false);
        eval!("-42", Integer, -42);
        eval!("1 < 2", Boolean, true);
        eval!("2 <= 2", Boolean, true);
        eval!("2 == 2", Boolean, true);
        eval!("2 ~= 2", Boolean, false);
        eval!("1 > 2", Boolean, false);
        eval!("2 >= 2", Boolean, true);
        eval!("5 * 4 * 3 * 2 * 1", Integer, 120);
        evalfails!(
            "1 + true",
            "Type error: expected integer but found boolean."
        );
        evalfails!(
            "1 && true",
            "Type error: expected boolean but found integer."
        );
        evalfails!("~1", "Type error: expected boolean but found integer.");
        evalfails!("-false", "Type error: expected integer but found boolean.");
        evalfails!(
            "1 == true",
            "Type error: expected integer but found boolean."
        );
        evalfails!(
            "1 ~= false",
            "Type error: expected integer but found boolean."
        );
        evalfails!(
            "0 <= false",
            "Type error: expected integer but found boolean."
        );
        eval!("(1 + 2) * 5", Integer, 15);
        eval!("1 + 2 * 5", Integer, 11);
        evalfails!("1 / 0", "Division by zero.");
        evalfails!("1 % 0", "Division by zero.");
        evalfails!(
            "if true then 1 else false end",
            "Type error: expected integer but found boolean."
        );
        evalfails!(
            "if true then 1 elsif true then false else 2 end",
            "Type error: expected integer but found boolean."
        );
        evalfails!(
            "if true then false else 1 end",
            "Type error: expected boolean but found integer."
        );
        evalfails!(
            "if 1 then false else true end",
            "Type error: expected boolean but found integer."
        );
        eval!("if true then 1 else 2 end", Integer, 1);
        eval!("if false then 1 else 2 end", Integer, 2);
        eval!("if false then 1 elsif true then 2 else 3 end", Integer, 2);
        eval!(
            "if true then if false then 1 else 2 end else 3 end",
            Integer,
            2
        );
        eval!("(1,)", Tuple, Value::Integer(1));
        eval!(
            "(1, false)",
            Tuple,
            Value::Integer(1),
            Value::Boolean(false)
        );
        eval!("(1, 1 + 2)", Tuple, Value::Integer(1), Value::Integer(3));
        eval!(
            "(1, 1, 2)",
            Tuple,
            Value::Integer(1),
            Value::Integer(1),
            Value::Integer(2)
        );
        evalfails!(
            "fn 1 -> 5 end",
            "Type error: lambda parameter must be identifier or tuple of identifiers."
        );
        evalfails!(
            "fn (a, 1) -> 5 end",
            "Type error: lambda parameter must be identifier or tuple of identifiers."
        );
        eval!("(fn x -> x + 1 end) 1", Integer, 2);
        eval!("(fn x -> ~x end) false", Boolean, true);
        evalfails!(
            "(fn x -> x + 1 end) true",
            "Type error: expected integer but found boolean."
        );
        evalfails!(
            "(fn (x, y) -> x + y + 1 end) true",
            "Type error: expected (integer, integer) but found boolean."
        );
        eval!(
            "(fn x -> (x + 1, 1, 2) end) 1",
            Tuple,
            Value::Integer(2),
            Value::Integer(1),
            Value::Integer(2)
        );
        eval!("(fn (x, y) -> x + y end) (1, 2)", Integer, 3);
        eval!("(1, 1) == (1, 0)", Boolean, false);
        eval!("(1, 1, 1) == (1, 1, 0)", Boolean, false);
        eval!("(1, 1, 1, 1) == (1, 1, 1, 0)", Boolean, false);
        eval!("(1, 1, 1, 1) == (1, 1, 1, 1)", Boolean, true);
        eval!("(1, 1) ~= (1, 0)", Boolean, true);
        eval!("def x := 42", Integer, 42);
        eval!("def f := fn x -> x + 1 end 1", Integer, 2);
        eval!(
            "def t := 1
             def f := fn x -> x + t end
             def t := 2
             f 1",
            Integer,
            2
        );
        eval!(
            "def t := 1
             (def f := fn x ->
                 def t := 2
                 x + t
             end)
             f 1",
            Integer,
            3
        );
        eval!(
            "(def f := fn t -> fn x -> x + t end end)
             (f 2) 1",
            Integer,
            3
        );
        eval!(
            "(def f := fn (x, y) -> x == y end)
             f (1, 2)",
            Boolean,
            false
        );
        eval!(
            "(def f := fn (x, y) -> x == y end)
             f (1, false)",
            Boolean,
            false
        );
        eval!(
            "(def f := fn (x, y) -> x == y end)
             f (1, 1)",
            Boolean,
            true
        );
        eval!(
            "(def f := fn (x, y) -> x == y end)
             (def g := fn (x, y) -> x == y end)
             f (f, g)",
            Boolean,
            false
        );
        eval!(
            "type Maybe := Some x | None end
             None",
            Datatype,
            Box::new(vm::Value::Unit)
        );
        eval!(
            "type Maybe := Some x | None end
             Some 42",
            Datatype,
            Box::new(vm::Value::Integer(42))
        );
        eval!(
            "type Maybe := Some x | None end
             fn f x -> Some x end
             f 42",
            Datatype,
            Box::new(vm::Value::Integer(42))
        );
        eval!("()", Unit);
        eval!("fn () -> 42 end ()", Integer, 42);
        eval!("fn () -> () end ()", Unit);
        eval!(
            "def f := fn (x, y) ->
                 if x == 1 then
                     true
                 else
                     false
                 end
             end (1, 0)
        ",
            Boolean,
            true
        );
        eval!(
            "fn fact (n, acc) ->
                 if n == 0 then
                    acc
                 else
                    fact(n - 1, n*acc)
                 end
             end
             fact (5, 1)
        ",
            Integer,
            120
        );
        eval!(
            "fn fact n ->
                fn iter (n, acc) ->
                     if n == 0 then
                        acc
                     else
                        iter(n - 1, n*acc)
                     end
                end
                iter (n, 1)
             end
             fact 5
        ",
            Integer,
            120
        );
    }
}
