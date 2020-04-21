use std::collections::HashMap;

use crate::parser;
use crate::typechecker::Type;

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

pub fn typeinfer(id: &str, ids: &HashMap<String, Type>, ast: &parser::AST) -> Option<Type> {
    match ast {
        parser::AST::BinaryOp(op, lhs, rhs, _, _) => {
            if let parser::AST::Identifier(s, _, _) = &**lhs {
                if s == id {
                    match type_from_operator(op) {
                        Some(typ) => return Some(typ),
                        None => match &**rhs {
                            parser::AST::Boolean(_, _, _) => {
                                return Some(Type::Boolean);
                            }
                            parser::AST::BinaryOp(op, _, _, _, _) => match type_from_operator(op) {
                                Some(typ) => return Some(typ),
                                None => match op {
                                    parser::Operator::Equal | parser::Operator::NotEqual => {
                                        return Some(Type::Polymorphic("'a".to_string()));
                                    }
                                    _ => return None,
                                },
                            },
                            parser::AST::Integer(_, _, _) => {
                                return Some(Type::Integer);
                            }
                            parser::AST::UnaryOp(op, _, _, _) => {
                                return type_from_operator(op);
                            }
                            _ => match op {
                                parser::Operator::Equal | parser::Operator::NotEqual => {
                                    return Some(Type::Polymorphic("'a".to_string()))
                                }
                                _ => return None,
                            },
                        },
                    }
                }
            }
            if let parser::AST::Identifier(s, _, _) = &**rhs {
                if s == id {
                    match type_from_operator(op) {
                        Some(typ) => return Some(typ),
                        None => match &**lhs {
                            parser::AST::BinaryOp(op, _, _, _, _) => match type_from_operator(op) {
                                Some(typ) => return Some(typ),
                                None => match op {
                                    parser::Operator::Equal | parser::Operator::NotEqual => {
                                        return Some(Type::Polymorphic("'a".to_string()))
                                    }
                                    _ => return None,
                                },
                            },
                            parser::AST::Boolean(_, _, _) => {
                                return Some(Type::Boolean);
                            }
                            parser::AST::Integer(_, _, _) => {
                                return Some(Type::Integer);
                            }
                            parser::AST::UnaryOp(op, _, _, _) => {
                                return type_from_operator(op);
                            }
                            _ => match op {
                                parser::Operator::Equal | parser::Operator::NotEqual => {
                                    return Some(Type::Polymorphic("'a".to_string()))
                                }
                                _ => return None,
                            },
                        },
                    }
                }
            }
            match typeinfer(id, ids, lhs) {
                Some(typ) => Some(typ),
                None => typeinfer(id, ids, rhs),
            }
        }
        parser::AST::Boolean(_, _, _) => Some(Type::Boolean),
        parser::AST::Call(fun, _, _, _) => typeinfer(id, ids, fun),
        parser::AST::Function(_, body, _, _) => typeinfer(id, ids, body),
        parser::AST::Identifier(id, _, _) => match ids.get(id) {
            Some(Type::Function(from, to)) => Some(*to.clone()),
            Some(typ) => Some(typ.clone()),
            None => None,
        },
        parser::AST::If(conds, els, _, _) => {
            for cond in conds {
                match typeinfer(id, ids, &cond.0) {
                    Some(typ) => return Some(typ),
                    None => {}
                }
                match typeinfer(id, ids, &cond.1) {
                    Some(typ) => return Some(typ),
                    None => {}
                }
            }
            match typeinfer(id, ids, els) {
                Some(typ) => return Some(typ),
                None => return None,
            }
        }
        parser::AST::Integer(_, _, _) => Some(Type::Integer),
        parser::AST::Let(_, value, _, _) => typeinfer(id, ids, value),
        parser::AST::Program(expressions, _, _) => {
            for expression in expressions {
                match typeinfer(id, ids, expression) {
                    Some(typ) => return Some(typ),
                    None => {}
                }
            }
            None
        }
        parser::AST::Tuple(elements, _, _) => {
            for element in elements {
                match typeinfer(id, ids, element) {
                    Some(typ) => return Some(typ),
                    None => {}
                }
            }
            None
        }
        parser::AST::UnaryOp(op, ast, _, _) => {
            if let parser::AST::Identifier(s, _, _) = &**ast {
                if s == id {
                    type_from_operator(op)
                } else {
                    typeinfer(id, ids, ast)
                }
            } else {
                typeinfer(id, ids, ast)
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::parser;
    use crate::typechecker::Type;
    use crate::typeinfer;

    macro_rules! typeinfer {
        ($input:expr, $id:expr, $value:expr) => {{
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => {
                    match typeinfer::typeinfer($id, &HashMap::new(), &ast) {
                        Some(typ) => {
                            assert_eq!(typ, $value);
                        }
                        None => {
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
        ($input:expr, $id:expr, $ids:expr, $value:expr) => {{
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match typeinfer::typeinfer($id, $ids, &ast)
                {
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
    fn inferences() {
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
        typeinfer!("let x := 1", "x", Type::Integer);
        typeinfer!("let x := let y := 1", "x", Type::Integer);
        typeinfer!("let x := let y := 1", "y", Type::Integer);
        typeinfer!(
            "fn(x, y) -> x == y end",
            "x",
            Type::Polymorphic("'a".to_string())
        );
        typeinfer!(
            "let main := fn (n, sum) ->
                 if n == 1000 then
                     sum
                 else
                     if (n % 3 == 0) || (n % 5 == 0) then
                         main(n + 1, sum + n)
                     else
                         main(n + 1, sum)
                     end
                 end
             end",
            "n",
            Type::Integer
        );
        let mut ids = HashMap::new();
        ids.insert(
            "Some".to_string(),
            Type::Function(
                Box::new(Type::Polymorphic("'a".to_string())),
                Box::new(Type::Datatype("Maybe".to_string())),
            ),
        );
        ids.insert("None".to_string(), Type::Datatype("Maybe".to_string()));
        typeinfer!(
            "type Maybe := Some : 'a | None;
             let x := Some 42",
            "x",
            &ids,
            Type::Datatype("Maybe".to_string())
        );
        typeinfer!(
            "type Maybe := Some : 'a | None;
             let f := fn x -> Some x end;
             let x := f 42",
            "x",
            &ids,
            Type::Datatype("Maybe".to_string())
        );
    }
}
