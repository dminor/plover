use crate::codegen::InterpreterError;
use crate::parser;
use crate::typeinfer::typeinfer;

use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Type {
    Boolean,
    Function(Box<Type>, Box<Type>),
    Integer,
    Polymorphic(String),
    Tuple(Vec<Type>),
    Unit,
    Datatype(String),
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        if let Type::Polymorphic(s) = other {
            if let Type::Polymorphic(t) = self {
                return s == t;
            } else {
                return true;
            }
        }
        match self {
            Type::Boolean => {
                if let Type::Boolean = other {
                    true
                } else {
                    false
                }
            }
            Type::Function(param, body) => {
                if let Type::Function(other_param, other_body) = other {
                    param == other_param && body == other_body
                } else {
                    false
                }
            }
            Type::Integer => {
                if let Type::Integer = other {
                    true
                } else {
                    false
                }
            }
            Type::Polymorphic(s) => {
                if let Type::Polymorphic(t) = other {
                    s == t
                } else {
                    true
                }
            }
            Type::Tuple(elements) => {
                if let Type::Tuple(other_elements) = other {
                    for i in 0..elements.len() {
                        if elements[i] != other_elements[i] {
                            return false;
                        }
                    }
                    true
                } else {
                    false
                }
            }
            Type::Unit => {
                if let Type::Unit = other {
                    true
                } else {
                    false
                }
            }
            Type::Datatype(s) => {
                if let Type::Datatype(t) = other {
                    s == t
                } else {
                    false
                }
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Function(param, body) => write!(f, "{} -> {}", param, body),
            Type::Integer => write!(f, "integer"),
            Type::Polymorphic(s) => write!(f, "{}", s),
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
            Type::Datatype(s) => write!(f, "{}", s),
            Type::Unit => write!(f, "unit"),
        }
    }
}

pub enum TypedAST {
    BinaryOp(
        Type,
        parser::Operator,
        Box<TypedAST>,
        Box<TypedAST>,
        usize,
        usize,
    ),
    Boolean(bool),
    Call(Box<TypedAST>, Box<TypedAST>),
    Function(Box<TypedAST>, Box<TypedAST>),
    Identifier(Type, String),
    If(Vec<(TypedAST, TypedAST)>, Box<TypedAST>),
    Integer(i64),
    Let(Type, String, Box<TypedAST>),
    Program(Type, Vec<TypedAST>),
    Recur(Type, Box<TypedAST>),
    Tuple(Type, Vec<TypedAST>),
    UnaryOp(Type, parser::Operator, Box<TypedAST>),
    Unit,
}

pub fn type_of(ast: &TypedAST) -> Type {
    match ast {
        TypedAST::BinaryOp(typ, _, _, _, _, _)
        | TypedAST::Identifier(typ, _)
        | TypedAST::Let(typ, _, _)
        | TypedAST::Program(typ, _)
        | TypedAST::Recur(typ, _)
        | TypedAST::Tuple(typ, _)
        | TypedAST::UnaryOp(typ, _, _) => typ.clone(),
        TypedAST::Boolean(_) => Type::Boolean,
        TypedAST::Call(fun, _) => match type_of(fun) {
            Type::Function(_, body) => *body.clone(),
            _ => unreachable!(),
        },
        TypedAST::Function(param, body) => {
            Type::Function(Box::new(type_of(param)), Box::new(type_of(body)))
        }
        TypedAST::If(_, els) => type_of(els),
        TypedAST::Integer(_) => Type::Integer,
        TypedAST::Unit => Type::Unit,
    }
}

fn set_recur_type(ast: &mut TypedAST, typ: &Type) {
    match ast {
        TypedAST::BinaryOp(_, _, lhs, rhs, _, _) => {
            set_recur_type(lhs, typ);
            set_recur_type(rhs, typ);
        }
        TypedAST::Call(fun, args) => {
            set_recur_type(fun, typ);
            set_recur_type(args, typ);
        }
        TypedAST::Function(param, body) => {
            set_recur_type(param, typ);
            set_recur_type(body, typ);
        }
        TypedAST::If(conds, els) => {
            for cond in conds {
                set_recur_type(&mut cond.0, typ);
                set_recur_type(&mut cond.1, typ);
            }
            set_recur_type(els, typ);
        }
        TypedAST::Identifier(_, _) => {}
        TypedAST::Let(_, _, value) => {
            set_recur_type(value, typ);
        }
        TypedAST::Program(_, expressions) => {
            for expression in expressions {
                set_recur_type(expression, typ);
            }
        }
        TypedAST::Recur(ref mut recur_typ, _) => {
            *recur_typ = typ.clone();
        }
        TypedAST::Tuple(_, elements) => {
            for element in elements {
                set_recur_type(element, typ);
            }
        }
        TypedAST::UnaryOp(_, _, ast) => {
            set_recur_type(ast, typ);
        }
        _ => {}
    }
}

pub fn typecheck(
    ast: &parser::AST,
    ids: &mut HashMap<String, Type>,
    current_param: &Option<Type>,
) -> Result<TypedAST, InterpreterError> {
    match ast {
        parser::AST::BinaryOp(op, lhs, rhs, line, col) => {
            match typecheck(rhs, ids, current_param) {
                Ok(typed_rhs) => match typecheck(lhs, ids, current_param) {
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
                                    line: *line,
                                    col: *col,
                                })
                            } else {
                                Ok(TypedAST::BinaryOp(
                                    Type::Integer,
                                    op.clone(),
                                    Box::new(typed_lhs),
                                    Box::new(typed_rhs),
                                    *line,
                                    *col,
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
                                    line: *line,
                                    col: *col,
                                })
                            } else {
                                Ok(TypedAST::BinaryOp(
                                    Type::Boolean,
                                    op.clone(),
                                    Box::new(typed_lhs),
                                    Box::new(typed_rhs),
                                    *line,
                                    *col,
                                ))
                            }
                        }
                        parser::Operator::And | parser::Operator::Or => {
                            if type_of(&typed_rhs) != Type::Boolean
                                || type_of(&typed_lhs) != Type::Boolean
                            {
                                Err(InterpreterError {
                                    err: "Type error: expected boolean.".to_string(),
                                    line: *line,
                                    col: *col,
                                })
                            } else {
                                Ok(TypedAST::BinaryOp(
                                    Type::Boolean,
                                    op.clone(),
                                    Box::new(typed_lhs),
                                    Box::new(typed_rhs),
                                    *line,
                                    *col,
                                ))
                            }
                        }
                        parser::Operator::Not => unreachable!(),
                        parser::Operator::Equal | parser::Operator::NotEqual => {
                            if type_of(&typed_rhs) != type_of(&typed_lhs) {
                                let mut err = "Type error: type mismatch between ".to_string();
                                err.push_str(&type_of(&typed_lhs).to_string());
                                err.push_str(" and ");
                                err.push_str(&type_of(&typed_rhs).to_string());
                                err.push('.');
                                Err(InterpreterError {
                                    err: err,
                                    line: *line,
                                    col: *col,
                                })
                            } else {
                                Ok(TypedAST::BinaryOp(
                                    Type::Boolean,
                                    op.clone(),
                                    Box::new(typed_lhs),
                                    Box::new(typed_rhs),
                                    *line,
                                    *col,
                                ))
                            }
                        }
                    },
                    Err(err) => Err(err),
                },
                Err(err) => Err(err),
            }
        }
        parser::AST::Boolean(b, _, _) => Ok(TypedAST::Boolean(*b)),
        parser::AST::Call(fun, arg, line, col) => match typecheck(&fun, ids, current_param) {
            Ok(typed_fun) => match typecheck(arg, ids, current_param) {
                Ok(typed_arg) => {
                    if let Type::Function(param, _) = type_of(&typed_fun) {
                        if *param == type_of(&typed_arg) {
                            Ok(TypedAST::Call(Box::new(typed_fun), Box::new(typed_arg)))
                        } else {
                            let mut err = "Type error: expected ".to_string();
                            err.push_str(&param.to_string());
                            err.push_str(" found ");
                            err.push_str(&type_of(&typed_arg).to_string());
                            err.push('.');
                            Err(InterpreterError {
                                err: err,
                                line: *line,
                                col: *col,
                            })
                        }
                    } else {
                        Err(InterpreterError {
                            err: "Type error: attempt to call non-lambda.".to_string(),
                            line: *line,
                            col: *col,
                        })
                    }
                }
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
        parser::AST::Datatype(_, _, _, _) => Ok(TypedAST::Unit),
        parser::AST::Function(param, body, line, col) => {
            let err =
                "Type error: function parameters should be identifier or tuple of identifiers."
                    .to_string();
            let mut params = Vec::new();
            match &**param {
                parser::AST::Identifier(p, _, _) => {
                    params.push(p);
                }
                parser::AST::Tuple(elements, _, _) => {
                    for element in elements {
                        match element {
                            parser::AST::Identifier(p, _, _) => {
                                params.push(p);
                            }
                            _ => {
                                return Err(InterpreterError {
                                    err: err,
                                    line: *line,
                                    col: *col,
                                });
                            }
                        }
                    }
                }
                _ => {
                    return Err(InterpreterError {
                        err: err,
                        line: *line,
                        col: *col,
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
                            line: *line,
                            col: *col,
                        });
                    }
                }
            }

            let typed_param;
            if types.len() > 1 {
                typed_param = TypedAST::Tuple(Type::Tuple(types), typed_params);
            } else {
                match typed_params.pop() {
                    Some(typ) => {
                        typed_param = typ;
                    }
                    None => unreachable!(),
                }
            }

            match typecheck(&body, &mut ids, &Some(type_of(&typed_param))) {
                Ok(mut typed_body) => {
                    let return_type = type_of(&typed_body);
                    set_recur_type(&mut typed_body, &return_type);
                    Ok(TypedAST::Function(
                        Box::new(typed_param),
                        Box::new(typed_body),
                    ))
                }
                Err(err) => Err(err),
            }
        }
        parser::AST::Identifier(s, line, col) => match ids.get(s) {
            Some(typ) => Ok(TypedAST::Identifier(typ.clone(), s.clone())),
            None => {
                let mut err = "Type error: could not infer type for identifier: ".to_string();
                err.push_str(s);
                err.push('.');
                return Err(InterpreterError {
                    err: err,
                    line: *line,
                    col: *col,
                });
            }
        },
        parser::AST::If(conds, els, line, col) => {
            let mut first = true;
            let mut inferred_type = Type::Boolean;
            let mut typed_conds = Vec::new();
            for cond in conds {
                let typed_cond0;
                let typed_cond1;
                match typecheck(&cond.0, ids, current_param) {
                    Ok(t) => match type_of(&t) {
                        Type::Boolean => {
                            typed_cond0 = t;
                        }
                        _ => {
                            return Err(InterpreterError {
                                err: "Type error: expected boolean.".to_string(),
                                line: *line,
                                col: *col,
                            });
                        }
                    },
                    Err(err) => {
                        return Err(err);
                    }
                }
                match typecheck(&cond.1, ids, current_param) {
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
                                line: *line,
                                col: *col,
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
            match typecheck(&els, ids, current_param) {
                Ok(t) => {
                    if inferred_type != type_of(&t) {
                        let mut err = "Type mismatch: expected ".to_string();
                        err.push_str(&inferred_type.to_string());
                        err.push_str(" found ");
                        err.push_str(&type_of(&t).to_string());
                        err.push('.');
                        return Err(InterpreterError {
                            err: err,
                            line: *line,
                            col: *col,
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
        parser::AST::Integer(i, _, _) => Ok(TypedAST::Integer(*i)),
        parser::AST::Let(id, value, line, col) => match &**id {
            parser::AST::Identifier(id, _, _) => match typecheck(value, ids, current_param) {
                Ok(typed_value) => {
                    ids.insert(id.to_string(), type_of(&typed_value));
                    Ok(TypedAST::Let(
                        type_of(&typed_value),
                        id.clone(),
                        Box::new(typed_value),
                    ))
                }
                Err(err) => Err(err),
            },
            _ => Err(InterpreterError {
                err: "Type error: expected identifier.".to_string(),
                line: *line,
                col: *col,
            }),
        },
        parser::AST::Program(expressions, _, _) => {
            let mut typed_expressions = Vec::new();
            for expression in expressions {
                match typecheck(&expression, ids, current_param) {
                    Ok(typed_expression) => {
                        typed_expressions.push(typed_expression);
                    }
                    Err(err) => {
                        return Err(err);
                    }
                }
            }
            match typed_expressions.last() {
                Some(expr) => Ok(TypedAST::Program(type_of(expr), typed_expressions)),
                None => unreachable!(),
            }
        }
        parser::AST::Recur(arg, line, col) => match typecheck(arg, ids, current_param) {
            Ok(typed_arg) => match current_param {
                Some(current_param) => {
                    if *current_param == type_of(&typed_arg) {
                        Ok(TypedAST::Recur(
                            Type::Polymorphic("'a".to_string()),
                            Box::new(typed_arg),
                        ))
                    } else {
                        let mut err = "Type error: expected ".to_string();
                        err.push_str(&current_param.to_string());
                        err.push_str(" found ");
                        err.push_str(&type_of(&typed_arg).to_string());
                        err.push('.');
                        Err(InterpreterError {
                            err: err,
                            line: *line,
                            col: *col,
                        })
                    }
                }
                None => unreachable!(),
            },
            Err(err) => Err(err),
        },
        parser::AST::Tuple(elements, _, _) => {
            let mut types = Vec::new();
            let mut typed_elements = Vec::new();
            for element in elements {
                match typecheck(&element, ids, current_param) {
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
        parser::AST::UnaryOp(op, ast, line, col) => match typecheck(ast, ids, current_param) {
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
                            line: *line,
                            col: *col,
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
                            line: *line,
                            col: *col,
                        })
                    }
                }
                _ => Err(InterpreterError {
                    err: "Invalid unary operator.".to_string(),
                    line: *line,
                    col: *col,
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

#[cfg(test)]
mod tests {
    use crate::parser;
    use crate::typechecker;
    use crate::typechecker::type_of;
    use std::collections::HashMap;

    macro_rules! typecheck {
        ($input:expr, $value:expr) => {{
            let mut ids = HashMap::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => {
                    match typechecker::typecheck(&ast, &mut ids, &None) {
                        Ok(typed_ast) => {
                            assert_eq!(type_of(&typed_ast).to_string(), $value);
                        }
                        Err(_) => {
                            assert!(false);
                        }
                    }
                }
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
    fn checks() {
        typecheck!("5", "integer");
        typecheck!("true", "boolean");
        typecheck!("2 + 5 + 3", "integer");
        typecheck!("true && false", "boolean");
        typecheck!("~false", "boolean");
        typecheck!("-1", "integer");
        typecheck!("if true then 1 else 2 end", "integer");
        typecheck!("(1, false)", "(integer, boolean)");
        typecheck!("fn x -> x + 1 end", "integer -> integer");
        typecheck!("fn (x, y) -> x + y end", "(integer, integer) -> integer");
        typecheck!("fn x -> (x, x + 1) end", "integer -> (integer, integer)");
        typecheck!("fn x -> ~x end", "boolean -> boolean");
        typecheck!("fn (x, y) -> x < y end", "(integer, integer) -> boolean");
        typecheck!(
            "fn x -> fn y -> x + y end end",
            "integer -> integer -> integer"
        );
        typecheck!("(fn x -> ~x end) true", "boolean");
        typecheck!("(fn x -> x + 1 end) 1", "integer");
        typecheck!("let x := 1", "integer");
        typecheck!("let x := false", "boolean");
        typecheck!("let x := (1, false)", "(integer, boolean)");
        typecheck!("fn(x, y) -> x == y end", "('a, 'a) -> boolean");
    }
}
