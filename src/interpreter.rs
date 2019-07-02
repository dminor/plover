use crate::parser;
use crate::vm;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
enum Type {
    Boolean,
    Function(Box<Type>, Box<Type>),
    Integer,
    Tuple(Vec<Type>),
}

impl fmt::Display for Type {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Function(param, body) => write!(f, "{} -> {}", param, body),
            Type::Integer => write!(f, "integer"),
            Type::Tuple(elements) => {
                write!(f, "(")?;
                for i in 0..elements.len() {
                    write!(f, "{}", elements[i])?;
                    if i + 1 != elements.len() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Boolean(bool),
    Function,
    Integer(i64),
    Tuple(Vec<Value>),
}

impl fmt::Display for Value {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Function => write!(f, "(lambda)"),
            Value::Integer(v) => write!(f, "{}", v),
            Value::Tuple(elements) => {
                write!(f, "(")?;
                for i in 0..elements.len() {
                    write!(f, "{}", elements[i])?;
                    if i + 1 != elements.len() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

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
        parser::AST::Function(_, _) => {
            // TODO
        }
        parser::AST::If(conds, els) => {
            let start_ip = instr.len();
            for cond in conds {
                let mut then = Vec::new();
                generate(&cond.0, vm, instr);
                generate(&cond.1, vm, &mut then);
                let offset = 2 + then.len() as i64;
                instr.push(vm::Opcode::Jz(offset));
                instr.extend(then);
                instr.push(vm::Opcode::Jmp(i64::max_value()));
            }
            generate(&els, vm, instr);

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
        parser::AST::Identifier(_) => {
            // TODO
        }
        parser::AST::Integer(i) => {
            instr.push(vm::Opcode::Iconst(*i));
        }
        parser::AST::Tuple(elements) => {
            for element in elements {
                generate(&element, vm, instr);
            }
            instr.push(vm::Opcode::Tconst(elements.len()));
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

fn typecheck(ast: &parser::AST, ids: &HashMap<String, Type>) -> Result<Type, InterpreterError> {
    match ast {
        parser::AST::BinaryOp(op, lhs, rhs) => match typecheck(rhs, ids) {
            Ok(rhs_type) => match typecheck(lhs, ids) {
                Ok(lhs_type) => match op {
                    parser::Operator::Divide
                    | parser::Operator::Minus
                    | parser::Operator::Mod
                    | parser::Operator::Multiply
                    | parser::Operator::Plus => {
                        if rhs_type != Type::Integer || lhs_type != Type::Integer {
                            Err(InterpreterError {
                                err: "Type error: expected integer.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(Type::Integer)
                        }
                    }
                    parser::Operator::Greater
                    | parser::Operator::GreaterEqual
                    | parser::Operator::Less
                    | parser::Operator::LessEqual => {
                        if rhs_type != Type::Integer || lhs_type != Type::Integer {
                            Err(InterpreterError {
                                err: "Type error: expected integer.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(Type::Boolean)
                        }
                    }
                    parser::Operator::And | parser::Operator::Or => {
                        if rhs_type != Type::Boolean || lhs_type != Type::Boolean {
                            Err(InterpreterError {
                                err: "Type error: expected boolean.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(Type::Boolean)
                        }
                    }
                    parser::Operator::Not => unreachable!(),
                    parser::Operator::Equal | parser::Operator::NotEqual => {
                        if rhs_type != lhs_type {
                            Err(InterpreterError {
                                err: "Type error: type mismatch.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(Type::Boolean)
                        }
                    }
                },
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
        parser::AST::Boolean(_) => Ok(Type::Boolean),
        parser::AST::Function(param, body) => {
            let err =
                "Type error: function parameters should be identifier or tuple of identifiers."
                    .to_string();
            let mut params = Vec::new();
            match &**param {
                parser::AST::Identifier(p) => {
                    params.push(p);
                }
                parser::AST::Tuple(elements) => {
                    for element in elements {
                        match element {
                            parser::AST::Identifier(p) => {
                                params.push(p);
                            }
                            _ => {
                                return Err(InterpreterError {
                                    err: err,
                                    line: usize::max_value(),
                                    col: usize::max_value(),
                                });
                            }
                        }
                    }
                }
                _ => {
                    return Err(InterpreterError {
                        err: err,
                        line: usize::max_value(),
                        col: usize::max_value(),
                    });
                }
            }
            let mut ids = ids.clone();
            let mut types = Vec::new();
            for param in params {
                match typeinfer(param, body) {
                    Some(typ) => {
                        types.push(typ.clone());
                        ids.insert(param.to_string(), typ);
                    }
                    None => {
                        let mut err = "Type error: could not infer type for: ".to_string();
                        err.push_str(param);
                        err.push('.');
                        return Err(InterpreterError {
                            err: err,
                            line: usize::max_value(),
                            col: usize::max_value(),
                        });
                    }
                }
            }
            match typecheck(&body, &ids) {
                Ok(typ) => {
                    if types.len() > 1 {
                        Ok(Type::Function(Box::new(Type::Tuple(types)), Box::new(typ)))
                    } else {
                        Ok(Type::Function(Box::new(types[0].clone()), Box::new(typ)))
                    }
                }
                Err(err) => Err(err),
            }
        }
        parser::AST::Identifier(s) => match ids.get(s) {
            Some(typ) => Ok(typ.clone()),
            None => Err(InterpreterError {
                err: "Type error: could not infer type for identifier.".to_string(),
                line: usize::max_value(),
                col: usize::max_value(),
            }),
        },
        parser::AST::If(conds, els) => {
            let mut first = true;
            let mut inferred_type = Type::Boolean;
            for cond in conds {
                match typecheck(&cond.0, ids) {
                    Ok(Type::Boolean) => {}
                    Err(err) => {
                        return Err(err);
                    }
                    _ => {
                        return Err(InterpreterError {
                            err: "Type error: expected boolean.".to_string(),
                            line: usize::max_value(),
                            col: usize::max_value(),
                        });
                    }
                }
                match typecheck(&cond.1, ids) {
                    Ok(t) => {
                        if first {
                            first = false;
                            inferred_type = t;
                        } else if inferred_type != t {
                            let mut err = "Type mismatch: expected ".to_string();
                            err.push_str(&inferred_type.to_string());
                            err.push_str(" found ");
                            err.push_str(&t.to_string());
                            err.push('.');
                            return Err(InterpreterError {
                                err: err,
                                line: usize::max_value(),
                                col: usize::max_value(),
                            });
                        }
                    }
                    Err(err) => {
                        return Err(err);
                    }
                }
            }
            match typecheck(&els, ids) {
                Ok(t) => {
                    if inferred_type != t {
                        let mut err = "Type mismatch: expected ".to_string();
                        err.push_str(&inferred_type.to_string());
                        err.push_str(" found ");
                        err.push_str(&t.to_string());
                        err.push('.');
                        return Err(InterpreterError {
                            err: err,
                            line: usize::max_value(),
                            col: usize::max_value(),
                        });
                    }
                }
                Err(err) => {
                    return Err(err);
                }
            }
            Ok(inferred_type)
        }
        parser::AST::Integer(_) => Ok(Type::Integer),
        parser::AST::Tuple(elements) => {
            let mut types = Vec::new();
            for element in elements {
                match typecheck(&element, ids) {
                    Ok(typ) => {
                        types.push(typ);
                    }
                    Err(err) => {
                        return Err(err);
                    }
                }
            }
            Ok(Type::Tuple(types))
        }
        parser::AST::UnaryOp(op, ast) => match typecheck(ast, ids) {
            Ok(ast_type) => match op {
                parser::Operator::Minus => {
                    if ast_type == Type::Integer {
                        Ok(Type::Integer)
                    } else {
                        Err(InterpreterError {
                            err: "Type error: expected integer.".to_string(),
                            line: usize::max_value(),
                            col: usize::max_value(),
                        })
                    }
                }
                parser::Operator::Not => {
                    if ast_type == Type::Boolean {
                        Ok(Type::Boolean)
                    } else {
                        Err(InterpreterError {
                            err: "Type error: expected boolean.".to_string(),
                            line: usize::max_value(),
                            col: usize::max_value(),
                        })
                    }
                }
                _ => Err(InterpreterError {
                    err: "Invalid unary operator.".to_string(),
                    line: usize::max_value(),
                    col: usize::max_value(),
                }),
            },
            Err(err) => Err(err),
        },
        parser::AST::None => Err(InterpreterError {
            err: "None has no type.".to_string(),
            line: usize::max_value(),
            col: usize::max_value(),
        }),
    }
}

fn type_from_operator(op: &parser::Operator) -> Option<Type> {
    match op {
        parser::Operator::And => Some(Type::Boolean),
        parser::Operator::Divide => Some(Type::Integer),
        parser::Operator::Equal => None,
        parser::Operator::Greater => Some(Type::Integer),
        parser::Operator::GreaterEqual => Some(Type::Integer),
        parser::Operator::Less => Some(Type::Integer),
        parser::Operator::LessEqual => Some(Type::Integer),
        parser::Operator::Minus => Some(Type::Integer),
        parser::Operator::Mod => Some(Type::Integer),
        parser::Operator::Multiply => Some(Type::Integer),
        parser::Operator::Not => Some(Type::Boolean),
        parser::Operator::NotEqual => None,
        parser::Operator::Or => Some(Type::Boolean),
        parser::Operator::Plus => Some(Type::Integer),
    }
}

fn typeinfer(id: &str, ast: &parser::AST) -> Option<Type> {
    match ast {
        parser::AST::BinaryOp(op, lhs, rhs) => {
            if let parser::AST::Identifier(s) = &**lhs {
                if s == id {
                    match type_from_operator(op) {
                        Some(typ) => return Some(typ),
                        None => match &**rhs {
                            parser::AST::BinaryOp(op, _, _) => {
                                return type_from_operator(op);
                            }
                            parser::AST::UnaryOp(op, _) => {
                                return type_from_operator(op);
                            }
                            _ => {
                                return None;
                            }
                        },
                    }
                }
            }
            if let parser::AST::Identifier(s) = &**rhs {
                if s == id {
                    match type_from_operator(op) {
                        Some(typ) => return Some(typ),
                        None => match &**lhs {
                            parser::AST::BinaryOp(op, _, _) => {
                                return type_from_operator(op);
                            }
                            parser::AST::UnaryOp(op, _) => {
                                return type_from_operator(op);
                            }
                            _ => {
                                return None;
                            }
                        },
                    }
                }
            }
            match typeinfer(id, lhs) {
                Some(typ) => Some(typ),
                None => typeinfer(id, rhs),
            }
        }
        parser::AST::Function(_, body) => typeinfer(id, body),
        parser::AST::Tuple(elements) => {
            for element in elements {
                match typeinfer(id, element) {
                    Some(typ) => return Some(typ),
                    None => {}
                }
            }
            None
        }
        parser::AST::UnaryOp(op, ast) => {
            if let parser::AST::Identifier(s) = &**ast {
                if s == id {
                    type_from_operator(op)
                } else {
                    typeinfer(id, ast)
                }
            } else {
                typeinfer(id, ast)
            }
        }
        _ => None,
    }
}

fn to_typed_value(typ: &Type, value: i64) -> Value {
    match typ {
        Type::Boolean => Value::Boolean(value != 0),
        Type::Function(_, _) => Value::Function,
        Type::Integer => Value::Integer(value),
        Type::Tuple(types) => {
            let mut values = Vec::new();
            unsafe {
                let boxed = Box::from_raw(value as *mut Vec<i64>);
                for i in 0..types.len() {
                    let v = to_typed_value(&types[i], boxed[i]);
                    values.push(v);
                }
            }
            Value::Tuple(values)
        }
    }
}

pub fn eval(vm: &mut vm::VirtualMachine, ast: &parser::AST) -> Result<Value, InterpreterError> {
    match typecheck(ast, &HashMap::new()) {
        Ok(typ) => {
            let mut instr = Vec::new();
            generate(ast, vm, &mut instr);
            vm.ip = vm.instructions.len();
            vm.instructions.extend(instr);
            // TODO: This is useful for debugging. Add an argument to enable it.
            //println!("disassembly:");
            //for i in 0..vm.instructions.len() {
            //    println!("  {} {}", i, vm.instructions[i]);
            //}
            match vm.run() {
                Ok(()) => match vm.stack.pop() {
                    Some(value) => Ok(to_typed_value(&typ, value)),
                    None => Err(InterpreterError {
                        err: "Stack underflow.".to_string(),
                        line: usize::max_value(),
                        col: usize::max_value(),
                    }),
                },
                Err(e) => Err(e),
            }
        }
        Err(err) => {
            return Err(err);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter;
    use crate::interpreter::Type;
    use crate::interpreter::Value;
    use crate::parser;
    use crate::vm;
    use std::collections::HashMap;

    macro_rules! eval {
        ($input:expr, Tuple, $($value:expr),*) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match interpreter::eval(&mut vm, &ast) {
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
        ($input:expr, $type:tt, $value:expr) => {{
            let mut vm = vm::VirtualMachine::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match interpreter::eval(&mut vm, &ast) {
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
                parser::ParseResult::Matched(ast, _) => match interpreter::eval(&mut vm, &ast) {
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

    macro_rules! typecheck {
        ($input:expr, $value:expr) => {{
            let ids = HashMap::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match interpreter::typecheck(&ast, &ids) {
                    Ok(typ) => {
                        assert_eq!(typ.to_string(), $value);
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

    macro_rules! typeinfer {
        ($input:expr, $id:expr, $value:expr) => {{
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match interpreter::typeinfer($id, &ast) {
                    Some(typ) => {
                        assert_eq!(typ, $value);
                    }
                    None => {
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
        typecheck!("5", "integer");
        typecheck!("true", "boolean");
        typecheck!("2 + 5 + 3", "integer");
        typecheck!("true && false", "boolean");
        typecheck!("~false", "boolean");
        typecheck!("-1", "integer");
        evalfails!("1 + true", "Type error: expected integer.");
        evalfails!("1 && true", "Type error: expected boolean.");
        evalfails!("~1", "Type error: expected boolean.");
        evalfails!("-false", "Type error: expected integer.");
        evalfails!("1 == true", "Type error: type mismatch.");
        evalfails!("1 ~= false", "Type error: type mismatch.");
        evalfails!("0 <= false", "Type error: expected integer.");
        eval!("(1 + 2) * 5", Integer, 15);
        eval!("1 + 2 * 5", Integer, 11);
        evalfails!("1 / 0", "Division by zero.");
        evalfails!("1 % 0", "Division by zero.");
        typecheck!("if true then 1 else 2 end", "integer");
        evalfails!(
            "if true then 1 else false end",
            "Type mismatch: expected integer found boolean."
        );
        evalfails!(
            "if true then 1 elsif true then false else 2 end",
            "Type mismatch: expected integer found boolean."
        );
        evalfails!(
            "if true then false else 1 end",
            "Type mismatch: expected boolean found integer."
        );
        evalfails!(
            "if 1 then false else true end",
            "Type error: expected boolean."
        );
        eval!("if true then 1 else 2 end", Integer, 1);
        eval!("if false then 1 else 2 end", Integer, 2);
        eval!("if false then 1 elsif true then 2 else 3 end", Integer, 2);
        eval!(
            "if true then if false then 1 else 2 end else 3 end",
            Integer,
            2
        );
        typecheck!("(1, false)", "(integer, boolean)");
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
            "Type error: function parameters should be identifier or tuple of identifiers."
        );
        evalfails!(
            "fn (a, 1) -> 5 end",
            "Type error: function parameters should be identifier or tuple of identifiers."
        );
        typeinfer!("-a", "a", Type::Integer);
        typeinfer!("~a", "a", Type::Boolean);
        typeinfer!("a + 1", "a", Type::Integer);
        typeinfer!("a - 1", "a", Type::Integer);
        typeinfer!("a * 1", "a", Type::Integer);
        typeinfer!("a / 1", "a", Type::Integer);
        typeinfer!("2 % a", "a", Type::Integer);
        typeinfer!("1 < a", "a", Type::Integer);
        typeinfer!("1 <= a", "a", Type::Integer);
        typeinfer!("1 + 2 <= a", "a", Type::Integer);
        typeinfer!("a + 1 <= b", "a", Type::Integer);
        typeinfer!("a + b", "a", Type::Integer);
        typeinfer!("a + b", "b", Type::Integer);
        typeinfer!("a + b < c", "a", Type::Integer);
        typeinfer!("a + b < c", "b", Type::Integer);
        typeinfer!("a + b < c", "c", Type::Integer);
        typeinfer!("a + b == c", "a", Type::Integer);
        typeinfer!("a + b == c", "b", Type::Integer);
        typeinfer!("a + b == c", "c", Type::Integer);
        typeinfer!("a == -b", "a", Type::Integer);
        typecheck!("fn x -> x + 1 end", "integer -> integer");
        typecheck!("fn (x, y) -> x + y end", "(integer, integer) -> integer");
        typecheck!("fn x -> (x, x + 1) end", "integer -> (integer, integer)");
        typecheck!("fn x -> ~x end", "boolean -> boolean");
        typecheck!("fn (x, y) -> x < y end", "(integer, integer) -> boolean");
        typecheck!(
            "fn x -> fn y -> x + y end end",
            "integer -> integer -> integer"
        );
    }
}
