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

pub enum TypedAST {
    BinaryOp(Type, parser::Operator, Box<TypedAST>, Box<TypedAST>),
    Boolean(bool),
    Call(Box<TypedAST>, Box<TypedAST>),
    Function(Box<TypedAST>, Box<TypedAST>),
    Identifier(Type, String),
    If(Vec<(TypedAST, TypedAST)>, Box<TypedAST>),
    Integer(i64),
    Let(Type, String, Box<TypedAST>),
    Tuple(Type, Vec<TypedAST>),
    UnaryOp(Type, parser::Operator, Box<TypedAST>),
}

fn type_of(ast: &TypedAST) -> Type {
    match ast {
        TypedAST::BinaryOp(typ, _, _, _)
        | TypedAST::Identifier(typ, _)
        | TypedAST::Let(typ, _, _)
        | TypedAST::Tuple(typ, _)
        | TypedAST::UnaryOp(typ, _, _) => typ.clone(),
        TypedAST::Boolean(_) => Type::Boolean,
        TypedAST::Call(fun, _) => match &**fun {
            TypedAST::Function(_, body) => type_of(body),
            _ => unreachable!(),
        },
        TypedAST::Function(param, body) => {
            Type::Function(Box::new(type_of(param)), Box::new(type_of(body)))
        }
        TypedAST::If(_, els) => type_of(els),
        TypedAST::Integer(_) => Type::Integer,
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

fn generate(
    ast: &TypedAST,
    vm: &mut vm::VirtualMachine,
    instr: &mut Vec<vm::Opcode>,
    ids: &HashMap<String, usize>,
) {
    match ast {
        TypedAST::BinaryOp(_, op, lhs, rhs) => {
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
        TypedAST::Call(fun, args) => {
            generate(args, vm, instr, ids);
            generate(fun, vm, instr, ids);
            instr.push(vm::Opcode::Call);
        }
        TypedAST::Function(param, body) => {
            let mut fn_instr = Vec::new();
            let mut local_ids = ids.clone();
            let mut count = 0;
            match &**param {
                TypedAST::Identifier(_, id) => {
                    count = 2;
                    local_ids.insert(id.to_string(), 0);
                }
                TypedAST::Tuple(_, elements) => {
                    for element in elements {
                        if let TypedAST::Identifier(_, id) = element {
                            local_ids.insert(id.to_string(), count);
                        }
                        count += 1;
                    }
                }
                _ => unreachable!(),
            }
            generate(body, vm, &mut fn_instr, &local_ids);
            fn_instr.push(vm::Opcode::Ret(count - 1));
            let ip = vm.instructions.len();
            vm.instructions.extend(fn_instr);
            instr.push(vm::Opcode::Fconst(ip));
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
            None => unreachable!(),
        },
        TypedAST::Integer(i) => {
            instr.push(vm::Opcode::Iconst(*i));
        }
        TypedAST::Let(_, _, _) => {
            // TODO
        }
        TypedAST::Tuple(_, elements) => {
            for element in elements {
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
    }
}

fn typecheck(ast: &parser::AST, ids: &HashMap<String, Type>) -> Result<TypedAST, InterpreterError> {
    match ast {
        parser::AST::BinaryOp(op, lhs, rhs) => match typecheck(rhs, ids) {
            Ok(typed_rhs) => match typecheck(lhs, ids) {
                Ok(typed_lhs) => match op {
                    parser::Operator::Divide
                    | parser::Operator::Minus
                    | parser::Operator::Mod
                    | parser::Operator::Multiply
                    | parser::Operator::Plus => {
                        if type_of(&typed_rhs) != Type::Integer
                            || type_of(&typed_lhs) != Type::Integer
                        {
                            Err(InterpreterError {
                                err: "Type error: expected integer.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(TypedAST::BinaryOp(
                                Type::Integer,
                                op.clone(),
                                Box::new(typed_lhs),
                                Box::new(typed_rhs),
                            ))
                        }
                    }
                    parser::Operator::Greater
                    | parser::Operator::GreaterEqual
                    | parser::Operator::Less
                    | parser::Operator::LessEqual => {
                        if type_of(&typed_rhs) != Type::Integer
                            || type_of(&typed_lhs) != Type::Integer
                        {
                            Err(InterpreterError {
                                err: "Type error: expected integer.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(TypedAST::BinaryOp(
                                Type::Boolean,
                                op.clone(),
                                Box::new(typed_lhs),
                                Box::new(typed_rhs),
                            ))
                        }
                    }
                    parser::Operator::And | parser::Operator::Or => {
                        if type_of(&typed_rhs) != Type::Boolean
                            || type_of(&typed_lhs) != Type::Boolean
                        {
                            Err(InterpreterError {
                                err: "Type error: expected boolean.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(TypedAST::BinaryOp(
                                Type::Boolean,
                                op.clone(),
                                Box::new(typed_lhs),
                                Box::new(typed_rhs),
                            ))
                        }
                    }
                    parser::Operator::Not => unreachable!(),
                    parser::Operator::Equal | parser::Operator::NotEqual => {
                        if type_of(&typed_rhs) != type_of(&typed_lhs) {
                            Err(InterpreterError {
                                err: "Type error: type mismatch.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            })
                        } else {
                            Ok(TypedAST::BinaryOp(
                                Type::Boolean,
                                op.clone(),
                                Box::new(typed_lhs),
                                Box::new(typed_rhs),
                            ))
                        }
                    }
                },
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
        parser::AST::Boolean(b) => Ok(TypedAST::Boolean(*b)),
        parser::AST::Call(fun, arg) => match typecheck(&fun, &ids) {
            Ok(TypedAST::Function(param, body)) => match typecheck(arg, &ids) {
                Ok(typed_arg) => {
                    if type_of(&param) == type_of(&typed_arg) {
                        Ok(TypedAST::Call(
                            Box::new(TypedAST::Function(param, body)),
                            Box::new(typed_arg),
                        ))
                    } else {
                        let mut err = "Type error: expected ".to_string();
                        err.push_str(&type_of(&param).to_string());
                        err.push_str(" found ");
                        err.push_str(&type_of(&typed_arg).to_string());
                        err.push('.');
                        Err(InterpreterError {
                            err: err,
                            line: usize::max_value(),
                            col: usize::max_value(),
                        })
                    }
                }
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
            _ => Err(InterpreterError {
                err: "Type error: attempt to call non-lambda.".to_string(),
                line: usize::max_value(),
                col: usize::max_value(),
            }),
        },
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
            let mut typed_params = Vec::new();
            for param in params {
                match typeinfer(param, body) {
                    Some(typ) => {
                        typed_params.push(TypedAST::Identifier(typ.clone(), param.to_string()));
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
                Ok(typed_body) => {
                    if types.len() > 1 {
                        Ok(TypedAST::Function(
                            Box::new(TypedAST::Tuple(Type::Tuple(types), typed_params)),
                            Box::new(typed_body),
                        ))
                    } else {
                        match typed_params.pop() {
                            Some(typ) => {
                                Ok(TypedAST::Function(Box::new(typ), Box::new(typed_body)))
                            }
                            None => unreachable!(),
                        }
                    }
                }
                Err(err) => Err(err),
            }
        }
        parser::AST::Identifier(s) => match ids.get(s) {
            Some(typ) => Ok(TypedAST::Identifier(typ.clone(), s.clone())),
            None => Err(InterpreterError {
                err: "Type error: could not infer type for identifier.".to_string(),
                line: usize::max_value(),
                col: usize::max_value(),
            }),
        },
        parser::AST::If(conds, els) => {
            let mut first = true;
            let mut inferred_type = Type::Boolean;
            let mut typed_conds = Vec::new();
            for cond in conds {
                let typed_cond0;
                let typed_cond1;
                match typecheck(&cond.0, ids) {
                    Ok(t) => match type_of(&t) {
                        Type::Boolean => {
                            typed_cond0 = t;
                        }
                        _ => {
                            return Err(InterpreterError {
                                err: "Type error: expected boolean.".to_string(),
                                line: usize::max_value(),
                                col: usize::max_value(),
                            });
                        }
                    },
                    Err(err) => {
                        return Err(err);
                    }
                }
                match typecheck(&cond.1, ids) {
                    Ok(t) => {
                        if first {
                            first = false;
                            inferred_type = type_of(&t);
                        } else if inferred_type != type_of(&t) {
                            let mut err = "Type mismatch: expected ".to_string();
                            err.push_str(&inferred_type.to_string());
                            err.push_str(" found ");
                            err.push_str(&type_of(&t).to_string());
                            err.push('.');
                            return Err(InterpreterError {
                                err: err,
                                line: usize::max_value(),
                                col: usize::max_value(),
                            });
                        }
                        typed_cond1 = t;
                    }
                    Err(err) => {
                        return Err(err);
                    }
                }
                typed_conds.push((typed_cond0, typed_cond1));
            }
            match typecheck(&els, ids) {
                Ok(t) => {
                    if inferred_type != type_of(&t) {
                        let mut err = "Type mismatch: expected ".to_string();
                        err.push_str(&inferred_type.to_string());
                        err.push_str(" found ");
                        err.push_str(&type_of(&t).to_string());
                        err.push('.');
                        return Err(InterpreterError {
                            err: err,
                            line: usize::max_value(),
                            col: usize::max_value(),
                        });
                    } else {
                        Ok(TypedAST::If(typed_conds, Box::new(t)))
                    }
                }
                Err(err) => {
                    return Err(err);
                }
            }
        }
        parser::AST::Integer(i) => Ok(TypedAST::Integer(*i)),
        parser::AST::Let(id, value) => match &**id {
            parser::AST::Identifier(id) => {
                let mut ids = ids.clone();
                match typeinfer(id, value) {
                    Some(typ) => {
                        ids.insert(id.to_string(), typ);
                        match typecheck(value, &ids) {
                            Ok(typed_body) => Ok(TypedAST::Let(
                                type_of(&typed_body),
                                id.clone(),
                                Box::new(typed_body),
                            )),
                            Err(err) => Err(err),
                        }
                    }
                    None => {
                        let mut err = "Type error: could not infer type for: ".to_string();
                        err.push_str(id);
                        err.push('.');
                        return Err(InterpreterError {
                            err: err,
                            line: usize::max_value(),
                            col: usize::max_value(),
                        });
                    }
                }
            }
            _ => Err(InterpreterError {
                err: "Type error: expected identifier.".to_string(),
                line: usize::max_value(),
                col: usize::max_value(),
            }),
        },
        parser::AST::Tuple(elements) => {
            let mut types = Vec::new();
            let mut typed_elements = Vec::new();
            for element in elements {
                match typecheck(&element, ids) {
                    Ok(typed_element) => {
                        types.push(type_of(&typed_element));
                        typed_elements.push(typed_element);
                    }
                    Err(err) => {
                        return Err(err);
                    }
                }
            }
            Ok(TypedAST::Tuple(Type::Tuple(types), typed_elements))
        }
        parser::AST::UnaryOp(op, ast) => match typecheck(ast, ids) {
            Ok(typed_ast) => match op {
                parser::Operator::Minus => {
                    if type_of(&typed_ast) == Type::Integer {
                        Ok(TypedAST::UnaryOp(
                            Type::Integer,
                            op.clone(),
                            Box::new(typed_ast),
                        ))
                    } else {
                        Err(InterpreterError {
                            err: "Type error: expected integer.".to_string(),
                            line: usize::max_value(),
                            col: usize::max_value(),
                        })
                    }
                }
                parser::Operator::Not => {
                    if type_of(&typed_ast) == Type::Boolean {
                        Ok(TypedAST::UnaryOp(
                            Type::Boolean,
                            op.clone(),
                            Box::new(typed_ast),
                        ))
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
        parser::AST::Boolean(_) => Some(Type::Boolean),
        parser::AST::Function(_, body) => typeinfer(id, body),
        parser::AST::Integer(_) => Some(Type::Integer),
        parser::AST::Let(_, value) => typeinfer(id, value),
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

fn to_typed_value(vm: &mut vm::VirtualMachine, typ: &Type) -> Option<Value> {
    match typ {
        Type::Boolean => match vm.stack.pop() {
            Some(value) => Some(Value::Boolean(value != 0)),
            None => None,
        },
        Type::Function(_, _) => match vm.stack.pop() {
            Some(_) => Some(Value::Function),
            None => None,
        },
        Type::Integer => match vm.stack.pop() {
            Some(value) => Some(Value::Integer(value)),
            None => None,
        },
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
            values.reverse();
            Some(Value::Tuple(values))
        }
    }
}

pub fn eval(vm: &mut vm::VirtualMachine, ast: &parser::AST) -> Result<Value, InterpreterError> {
    match typecheck(ast, &HashMap::new()) {
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
    use crate::interpreter::type_of;
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
                    Ok(typed_ast) => {
                        assert_eq!(type_of(&typed_ast).to_string(), $value);
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
        eval!("(fn x -> x + 1 end) 1", Integer, 2);
        eval!("(fn x -> ~x end) false", Boolean, true);
        typecheck!("(fn x -> ~x end) true", "boolean");
        typecheck!("(fn x -> x + 1 end) 1", "integer");
        evalfails!(
            "(fn x -> x + 1 end) true",
            "Type error: expected integer found boolean."
        );
        evalfails!(
            "(fn (x, y) -> x + y + 1 end) true",
            "Type error: expected (integer, integer) found boolean."
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
        typeinfer!("let x := 1", "x", Type::Integer);
        typeinfer!("let x := let y := 1", "x", Type::Integer);
        typeinfer!("let x := let y := 1", "y", Type::Integer);
        typecheck!("let x := 1", "integer");
        typecheck!("let x := false", "boolean");
        typecheck!("let x := (1, false)", "(integer, boolean)");
    }
}
