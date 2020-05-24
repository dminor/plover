use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;

use crate::codegen::InterpreterError;
use crate::parser;
use crate::unification::unify;

#[derive(Clone, Debug)]
pub enum Type {
    Boolean,
    Datatype(String),
    Function(Box<Type>, Box<Type>),
    Integer,
    Polymorphic(String),
    Tuple(Vec<Type>),
    Unit,
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

#[derive(Clone, Debug)]
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
    Datatype(Type, Vec<(String, Type)>),
    Define(Type, String, Box<TypedAST>),
    Function(Option<String>, Box<TypedAST>, Box<TypedAST>),
    Identifier(Type, String),
    If(Vec<(TypedAST, TypedAST)>, Box<TypedAST>),
    Integer(i64),
    Match(
        Box<TypedAST>,
        Type,
        Vec<(String, Option<TypedAST>, TypedAST)>,
    ),
    Program(Type, Vec<TypedAST>),
    Tuple(Type, Vec<TypedAST>),
    UnaryOp(Type, parser::Operator, Box<TypedAST>),
    Unit,
}

pub fn type_of(ast: &TypedAST) -> Type {
    match ast {
        TypedAST::BinaryOp(typ, _, _, _, _, _)
        | TypedAST::Datatype(typ, _)
        | TypedAST::Define(typ, _, _)
        | TypedAST::Identifier(typ, _)
        | TypedAST::Program(typ, _)
        | TypedAST::Tuple(typ, _)
        | TypedAST::UnaryOp(typ, _, _) => typ.clone(),
        TypedAST::Boolean(_) => Type::Boolean,
        TypedAST::Call(fun, _) => match type_of(fun) {
            Type::Function(_, body) => *body.clone(),
            _ => unreachable!(),
        },
        TypedAST::Function(_, param, body) => {
            Type::Function(Box::new(type_of(param)), Box::new(type_of(body)))
        }
        TypedAST::If(_, els) => type_of(&els),
        TypedAST::Integer(_) => Type::Integer,
        TypedAST::Match(_, _, cases) => {
            if !cases.is_empty() {
                type_of(&cases[0].2)
            } else {
                unreachable!()
            }
        }
        TypedAST::Unit => Type::Unit,
    }
}

fn fresh_type(id: &mut u64) -> Type {
    let typ = Type::Polymorphic("t".to_owned() + &id.to_string());
    *id += 1;
    typ
}

fn build_param_constraints(
    id: &mut u64,
    constraints: &mut Vec<(Type, Type, usize, usize)>,
    ids: &mut HashMap<String, Type>,
    ast: &parser::AST,
    insert_into_ids: bool,
) -> Result<TypedAST, InterpreterError> {
    match ast {
        parser::AST::Identifier(s, _, _) => match ids.get(s) {
            Some(typ) => {
                let typ = typ.clone();
                if insert_into_ids {
                    ids.insert(s.clone(), typ.clone());
                }
                Ok(TypedAST::Identifier(typ, s.clone()))
            }
            None => {
                let typ = fresh_type(id);
                if insert_into_ids {
                    ids.insert(s.clone(), typ.clone());
                }
                Ok(TypedAST::Identifier(typ, s.clone()))
            }
        },
        parser::AST::Tuple(elements, _, _) => {
            let mut types = Vec::new();
            let mut typed_elements = Vec::new();
            for element in elements {
                let typed_element =
                    build_param_constraints(id, constraints, ids, &element, insert_into_ids)?;
                types.push(type_of(&typed_element));
                typed_elements.push(typed_element);
            }
            Ok(TypedAST::Tuple(Type::Tuple(types), typed_elements))
        }
        parser::AST::Unit(_, _) => Ok(TypedAST::Unit),
        parser::AST::BinaryOp(_, _, _, line, col)
        | parser::AST::Boolean(_, line, col)
        | parser::AST::Call(_, _, line, col)
        | parser::AST::Datatype(_, _, line, col)
        | parser::AST::Define(_, _, line, col)
        | parser::AST::Function(_, _, _, line, col)
        | parser::AST::If(_, _, line, col)
        | parser::AST::Integer(_, line, col)
        | parser::AST::Match(_, _, line, col)
        | parser::AST::Program(_, line, col)
        | parser::AST::UnaryOp(_, _, line, col) => Err(InterpreterError {
            err: "Type error: lambda parameter must be identifier or tuple of identifiers."
                .to_string(),
            line: *line,
            col: *col,
        }),
        parser::AST::None => unreachable!(),
    }
}

fn build_constraints(
    id: &mut u64,
    constraints: &mut Vec<(Type, Type, usize, usize)>,
    mut ids: &mut HashMap<String, Type>,
    datatypes: &mut HashMap<String, HashSet<String>>,
    ast: &parser::AST,
) -> Result<TypedAST, InterpreterError> {
    match ast {
        parser::AST::BinaryOp(op, lhs, rhs, line, col) => {
            let typed_lhs = build_constraints(id, constraints, ids, datatypes, &lhs)?;
            let typed_rhs = build_constraints(id, constraints, ids, datatypes, &rhs)?;

            let typ = fresh_type(id);
            match op {
                parser::Operator::And | parser::Operator::Or => {
                    constraints.push((Type::Boolean, type_of(&typed_lhs), *line, *col));
                    constraints.push((Type::Boolean, type_of(&typed_rhs), *line, *col));
                    constraints.push((typ.clone(), Type::Boolean, *line, *col));
                }
                parser::Operator::Divide
                | parser::Operator::Mod
                | parser::Operator::Multiply
                | parser::Operator::Minus
                | parser::Operator::Plus => {
                    constraints.push((Type::Integer, type_of(&typed_lhs), *line, *col));
                    constraints.push((Type::Integer, type_of(&typed_rhs), *line, *col));
                    constraints.push((typ.clone(), Type::Integer, *line, *col));
                }
                parser::Operator::Greater
                | parser::Operator::GreaterEqual
                | parser::Operator::Less
                | parser::Operator::LessEqual => {
                    constraints.push((Type::Integer, type_of(&typed_lhs), *line, *col));
                    constraints.push((Type::Integer, type_of(&typed_rhs), *line, *col));
                    constraints.push((typ.clone(), Type::Boolean, *line, *col));
                }
                parser::Operator::Equal | parser::Operator::NotEqual => {
                    constraints.push((type_of(&typed_lhs), type_of(&typed_rhs), *line, *col));
                    constraints.push((typ.clone(), Type::Boolean, *line, *col));
                }
                _ => unreachable!(),
            }

            Ok(TypedAST::BinaryOp(
                typ,
                op.clone(),
                Box::new(typed_lhs),
                Box::new(typed_rhs),
                *line,
                *col,
            ))
        }
        parser::AST::Boolean(b, _, _) => Ok(TypedAST::Boolean(*b)),
        parser::AST::Call(fun, arg, line, col) => {
            let typed_fun = build_constraints(id, constraints, &mut ids, datatypes, &fun)?;
            let typed_arg = build_constraints(id, constraints, &mut ids, datatypes, &arg)?;

            match &typed_fun {
                TypedAST::Call(fun, _) => {
                    if let TypedAST::Function(_, _, body) = &**fun {
                        constraints.push((type_of(&body), type_of(&typed_arg), *line, *col));
                    }
                }
                TypedAST::Function(_, params, _) => {
                    constraints.push((type_of(&params), type_of(&typed_arg), *line, *col));
                }
                TypedAST::Identifier(Type::Function(_, _), _) => {}
                _ => {
                    return Err(InterpreterError {
                        err: "Type error: attempt to call non-lambda value.".to_string(),
                        line: *line,
                        col: *col,
                    });
                }
            }

            Ok(TypedAST::Call(Box::new(typed_fun), Box::new(typed_arg)))
        }
        parser::AST::Datatype(typ, variants, _, _) => {
            let mut all_variants = HashSet::new();
            let mut typed_variants = Vec::new();
            for variant in variants {
                all_variants.insert(variant.0.to_string());
                match &variant.1 {
                    Some(param) => {
                        // Type for constructor function
                        let typed_param =
                            build_param_constraints(id, constraints, &mut ids, &param, false)?;
                        let typ = Type::Function(
                            Box::new(type_of(&typed_param)),
                            Box::new(Type::Datatype(typ.to_string())),
                        );
                        ids.insert(variant.0.to_string(), typ.clone());
                        typed_variants.push((variant.0.to_string(), typ));
                    }
                    None => {
                        ids.insert(variant.0.to_string(), Type::Datatype(typ.to_string()));
                        typed_variants
                            .push((variant.0.to_string(), Type::Datatype(typ.to_string())));
                    }
                }
            }
            datatypes.insert(typ.to_string(), all_variants);
            Ok(TypedAST::Datatype(
                Type::Datatype(typ.to_string()),
                typed_variants,
            ))
        }
        parser::AST::Define(ident, value, line, col) => {
            if let parser::AST::Identifier(ident, _, _) = &**ident {
                let typed_value = build_constraints(id, constraints, ids, datatypes, &value)?;
                ids.insert(ident.to_string(), type_of(&typed_value));
                Ok(TypedAST::Define(
                    type_of(&typed_value),
                    ident.clone(),
                    Box::new(typed_value),
                ))
            } else {
                Err(InterpreterError {
                    err: "Type error: expected identifier.".to_string(),
                    line: *line,
                    col: *col,
                })
            }
        }
        parser::AST::Function(ident, param, body, line, col) => {
            let mut local_ids = ids.clone();
            let typed_param =
                build_param_constraints(id, constraints, &mut local_ids, &param, true)?;
            let typed_body;
            if let Some(ident) = ident {
                let typ = fresh_type(id);
                ids.insert(
                    ident.to_string(),
                    Type::Function(Box::new(type_of(&typed_param)), Box::new(typ.clone())),
                );
                local_ids.insert(
                    ident.to_string(),
                    Type::Function(Box::new(type_of(&typed_param)), Box::new(typ.clone())),
                );
                typed_body = build_constraints(id, constraints, &mut local_ids, datatypes, &body)?;
                constraints.push((typ, type_of(&typed_body), *line, *col));
            } else {
                typed_body = build_constraints(id, constraints, &mut local_ids, datatypes, &body)?;
            }

            Ok(TypedAST::Function(
                ident.clone(),
                Box::new(typed_param),
                Box::new(typed_body),
            ))
        }
        parser::AST::Identifier(s, line, col) => match ids.get(s) {
            Some(typ) => Ok(TypedAST::Identifier(typ.clone(), s.clone())),
            None => {
                let mut err = "Unknown identifier: ".to_string();
                err.push_str(s);
                err.push('.');
                Err(InterpreterError {
                    err: err.to_string(),
                    line: *line,
                    col: *col,
                })
            }
        },
        parser::AST::If(conds, els, line, col) => {
            let mut first = true;
            let mut inferred_type = Type::Boolean;
            let mut typed_conds = Vec::new();
            for cond in conds {
                let ifpart = build_constraints(id, constraints, ids, datatypes, &cond.0)?;
                let thenpart = build_constraints(id, constraints, ids, datatypes, &cond.1)?;
                constraints.push((Type::Boolean, type_of(&ifpart), *line, *col));
                if first {
                    first = false;
                    inferred_type = type_of(&thenpart);
                } else {
                    constraints.push((inferred_type.clone(), type_of(&thenpart), *line, *col));
                }

                typed_conds.push((ifpart, thenpart));
            }
            let elsepart = build_constraints(id, constraints, ids, datatypes, &els)?;
            constraints.push((inferred_type, type_of(&elsepart), *line, *col));
            Ok(TypedAST::If(typed_conds, Box::new(elsepart)))
        }
        parser::AST::Integer(i, _, _) => Ok(TypedAST::Integer(*i)),
        parser::AST::Match(cond, cases, line, col) => {
            let typed_cond = build_constraints(id, constraints, ids, datatypes, &cond)?;
            match type_of(&typed_cond) {
                Type::Datatype(_) | Type::Polymorphic(_) => {}
                _ => {
                    return Err(InterpreterError {
                        err: "Match statement: expected datatype.".to_string(),
                        line: *line,
                        col: *col,
                    });
                }
            }

            let mut first = true;
            let mut inferred_type = Type::Unit;
            let mut typed_cases = Vec::new();
            let mut present_variants = HashSet::new();
            let mut datatype = Type::Unit;
            for case in cases {
                let mut local_ids = ids.clone();
                let typed_param = match &case.1 {
                    Some(param) => Some(build_param_constraints(
                        id,
                        constraints,
                        &mut local_ids,
                        &param,
                        true,
                    )?),
                    None => None,
                };

                let typed_case =
                    build_constraints(id, constraints, &mut local_ids, datatypes, &case.2)?;
                if first {
                    inferred_type = type_of(&typed_case);
                } else {
                    constraints.push((inferred_type.clone(), type_of(&typed_case), *line, *col));
                }

                let variant_type;
                match ids.get(&case.0) {
                    Some(typ) => {
                        present_variants.insert(case.0.to_string());
                        let typ = match typ {
                            Type::Function(_, body) => body,
                            _ => typ,
                        };
                        variant_type = typ.clone();
                        if first {
                            datatype = variant_type;
                            if let Type::Polymorphic(_) = type_of(&typed_cond) {
                                constraints.push((
                                    type_of(&typed_cond),
                                    datatype.clone(),
                                    *line,
                                    *col,
                                ));
                            }
                        } else if variant_type != datatype {
                            let mut err = "Type error: expected ".to_string();
                            err.push_str(&datatype.to_string());
                            err.push_str(" but found ");
                            err.push_str(&variant_type.to_string());
                            err.push('.');
                            return Err(InterpreterError {
                                err: err.to_string(),
                                line: *line,
                                col: *col,
                            });
                        }
                    }
                    None => {
                        let mut err = "Unknown variant in match: ".to_string();
                        err.push_str(&case.0);
                        err.push('.');

                        return Err(InterpreterError {
                            err: err.to_string(),
                            line: *line,
                            col: *col,
                        });
                    }
                }

                typed_cases.push((case.0.to_string(), typed_param, typed_case));
                first = false;
            }

            if let Some(all_variants) = datatypes.get(&datatype.to_string()) {
                let mut missing: Vec<&String> =
                    all_variants.difference(&present_variants).collect();
                if !missing.is_empty() {
                    missing.sort();
                    let mut err = "Missing variants in match of ".to_string();
                    err.push_str(&datatype.to_string());
                    err.push(':');
                    for variant in missing {
                        err.push(' ');
                        err.push_str(variant);
                    }
                    err.push('.');
                    return Err(InterpreterError {
                        err,
                        line: *line,
                        col: *col,
                    });
                }
            }

            Ok(TypedAST::Match(Box::new(typed_cond), datatype, typed_cases))
        }
        parser::AST::Program(expressions, line, col) => {
            let mut typed_expressions = Vec::new();
            for expr in expressions {
                let typed_expr = build_constraints(id, constraints, ids, datatypes, &expr)?;
                typed_expressions.push(typed_expr);
            }
            match typed_expressions.last() {
                Some(expr) => {
                    let typ = fresh_type(id);
                    constraints.push((typ, type_of(expr), *line, *col));
                    Ok(TypedAST::Program(type_of(expr), typed_expressions))
                }
                None => unreachable!(),
            }
        }
        parser::AST::UnaryOp(op, ast, line, col) => {
            let typed = build_constraints(id, constraints, ids, datatypes, ast)?;
            let typ = fresh_type(id);
            let op_typ = match op {
                parser::Operator::Minus => Type::Integer,
                parser::Operator::Not => Type::Boolean,
                _ => unreachable!(),
            };

            constraints.push((op_typ.clone(), type_of(&typed), *line, *col));

            constraints.push((typ.clone(), op_typ, *line, *col));

            Ok(TypedAST::UnaryOp(typ, op.clone(), Box::new(typed)))
        }
        parser::AST::Tuple(elements, _, _) => {
            let mut types = Vec::new();
            let mut typed_elements = Vec::new();
            for element in elements {
                let typed_element = build_constraints(id, constraints, ids, datatypes, &element)?;
                types.push(type_of(&typed_element));
                typed_elements.push(typed_element);
            }
            Ok(TypedAST::Tuple(Type::Tuple(types), typed_elements))
        }
        parser::AST::Unit(_, _) => Ok(TypedAST::Unit),
        _ => unreachable!(),
    }
}

fn substitute_in_type<S: ::std::hash::BuildHasher>(
    bindings: &HashMap<String, Type, S>,
    typ: &mut Type,
) {
    match typ {
        Type::Polymorphic(s) => {
            if let Some(subst) = bindings.get(s) {
                *typ = subst.clone();
            }
        }
        Type::Function(param, body) => {
            substitute_in_type(bindings, param);
            substitute_in_type(bindings, body);
        }
        Type::Tuple(elements) => {
            elements
                .iter_mut()
                .for_each(|element| substitute_in_type(bindings, element));
        }
        _ => {}
    }
}

fn substitute<S: ::std::hash::BuildHasher>(
    bindings: &HashMap<String, Type, S>,
    ast: &mut TypedAST,
) {
    match ast {
        TypedAST::BinaryOp(typ, _, lhs, rhs, _, _) => {
            if let Type::Polymorphic(s) = typ {
                if let Some(subst) = bindings.get(s) {
                    *typ = subst.clone();
                }
            }
            substitute(bindings, lhs);
            substitute(bindings, rhs);
        }
        TypedAST::Call(fun, args) => {
            substitute(bindings, fun);
            substitute(bindings, args);
        }
        TypedAST::Define(_, _, value) => {
            substitute(bindings, value);
        }
        TypedAST::Function(_, param, body) => {
            substitute(bindings, param);
            substitute(bindings, body);
        }
        TypedAST::Identifier(typ, _) => {
            substitute_in_type(bindings, typ);
        }
        TypedAST::If(conds, els) => {
            for cond in conds {
                substitute(bindings, &mut cond.0);
                substitute(bindings, &mut cond.1);
            }
            substitute(bindings, els);
        }
        TypedAST::Match(cond, datatype, cases) => {
            substitute(bindings, cond);
            substitute_in_type(bindings, datatype);
            for case in cases {
                substitute(bindings, &mut case.2);
            }
        }
        TypedAST::Program(typ, expressions) => {
            substitute_in_type(bindings, typ);
            for expr in expressions {
                substitute(bindings, expr);
            }
        }
        TypedAST::Tuple(typ, elements) => {
            substitute_in_type(bindings, typ);
            for element in elements {
                substitute(bindings, element);
            }
        }
        TypedAST::UnaryOp(typ, _, ast) => {
            if let Type::Polymorphic(s) = typ {
                if let Some(subst) = bindings.get(s) {
                    *typ = subst.clone();
                }
            }
            substitute(bindings, ast);
        }
        _ => {}
    }
}

pub fn infer(
    ast: &parser::AST,
    mut ids: &mut HashMap<String, Type>,
) -> Result<TypedAST, InterpreterError> {
    let mut id = 1;
    let mut constraints = Vec::new();
    let mut datatypes: HashMap<String, HashSet<String>> = HashMap::new();

    let mut typed_ast =
        build_constraints(&mut id, &mut constraints, &mut ids, &mut datatypes, &ast)?;
    let mut bindings: HashMap<String, Type> = HashMap::new();
    for mut constraint in constraints {
        substitute_in_type(&bindings, &mut constraint.0);
        substitute_in_type(&bindings, &mut constraint.1);
        let typ_first = constraint.0.to_string();
        let typ_second = constraint.1.to_string();
        if !unify(&[constraint.0], &[constraint.1], &mut bindings) {
            let mut err = "Type error: expected ".to_string();
            err.push_str(&typ_first);
            err.push_str(" but found ");
            err.push_str(&typ_second);
            err.push('.');

            return Err(InterpreterError {
                err: err.to_string(),
                line: constraint.2,
                col: constraint.3,
            });
        }
    }
    substitute(&bindings, &mut typed_ast);
    Ok(typed_ast)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::parser;
    use crate::typeinfer;
    use crate::typeinfer::type_of;

    macro_rules! infer {
        ($input:expr, $value:expr) => {{
            let mut ids = HashMap::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match typeinfer::infer(&ast, &mut ids) {
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

    macro_rules! inferfails {
        ($input:expr, $err:expr, $line:expr, $col:expr) => {{
            let mut ids = HashMap::new();
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, _) => match typeinfer::infer(&ast, &mut ids) {
                    Ok(_) => {
                        assert!(false);
                    }
                    Err(err) => {
                        assert_eq!(err.err, $err);
                        assert_eq!(err.line, $line);
                        assert_eq!(err.col, $col);
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
        infer!("5", "integer");
        infer!("true", "boolean");
        infer!("2 + 5 + 3", "integer");
        infer!("true && false", "boolean");
        infer!("~false", "boolean");
        infer!("-1", "integer");
        inferfails!(
            "~1",
            "Type error: expected boolean but found integer.",
            1,
            3
        );
        inferfails!(
            "2 + 5 + false",
            "Type error: expected integer but found boolean.",
            1,
            14
        );
        infer!("1 + 1", "integer");
        infer!("1 - 1", "integer");
        infer!("1 * 1", "integer");
        infer!("1 / 1", "integer");
        infer!("2 % 1", "integer");
        infer!("1 < 1", "boolean");
        infer!("1 <= 1", "boolean");
        infer!("1 + 2 <= 1", "boolean");
        infer!("1 + 2 >= 1", "boolean");
        infer!("1 + 2 == 3", "boolean");
        infer!("1 == -1", "boolean");
        infer!("if true then 1 else 2 end", "integer");
        inferfails!(
            "if 1 then 1 else 2 end",
            "Type error: expected boolean but found integer.",
            1,
            23
        );
        infer!("(1, false)", "(integer, boolean)");
        inferfails!("a + 1", "Unknown identifier: a.", 1, 1);
        inferfails!("(1, a, false)", "Unknown identifier: a.", 1, 5);
        infer!("fn x -> x + 1 end", "integer -> integer");
        infer!("fn (x, y) -> x + y end", "(integer, integer) -> integer");
        infer!("fn x -> (x, x + 1) end", "integer -> (integer, integer)");
        infer!("fn x -> ~x end", "boolean -> boolean");
        infer!("fn (x, y) -> x < y end", "(integer, integer) -> boolean");
        infer!(
            "fn x -> fn y -> x + y end end",
            "integer -> integer -> integer"
        );
        infer!("fn(x, y) -> x == y end", "(t2, t2) -> boolean");
        infer!("(fn x -> ~x end) true", "boolean");
        infer!("(fn x -> x + 1 end) 1", "integer");
        inferfails!(
            "def x := (1,1)
             x 1",
            "Type error: attempt to call non-lambda value.",
            2,
            17
        );
        infer!("def x := 1", "integer");
        infer!("def x := false", "boolean");
        infer!("def x := (1, false)", "(integer, boolean)");
        infer!(
            "fn fact (n, acc) ->
                 if n == 0 then
                    acc
                 else
                    fact(n - 1, n*acc)
                 end
             end",
            "(integer, integer) -> integer"
        );
        infer!("type Maybe := Some x | None end", "Maybe");
        infer!(
            "type E := A | B end
             fn x -> A end",
            "t1 -> E"
        );
        infer!(
            "type E := A | B end
             fn x -> A end 10",
            "E"
        );
        infer!(
            "type E := A | B end
             fn x -> if x then A else B end end true",
            "E"
        );
        infer!(
            "(def f := fn x -> x + 1 end)
             fn x -> f x end 10",
            "integer"
        );
        infer!(
            "type E := A x | B end
             fn x -> A x end 10",
            "E"
        );
        infer!(
            "type E := A(x,y) | B end
             fn x -> A(x,x) end 10",
            "E"
        );
        infer!(
            "fn fact n ->
                 fn iter(n, acc) ->
                    if n == 0 then
                       acc
                    else
                       iter(n - 1, n*acc)
                    end
                 end
                 iter (n, 1)
             end",
            "integer -> integer"
        );
        infer!(
            "type E := A | B end
             match A with
                A -> 0
                | B -> 1
             end
            ",
            "integer"
        );
        infer!(
            "type E := A | B end
             def p := A
             match p with
                A -> 0
                | B -> 1
             end
            ",
            "integer"
        );
        infer!(
            "type E := A | B end
             fn f () -> A end
            ",
            "unit -> E"
        );
        infer!(
            "type E := A | B end
             fn f () -> A end
             f
            ",
            "unit -> E"
        );
        infer!(
            "type E := A | B end
             fn f () -> A end
             match f () with
                A -> 0
                | B -> 1
             end
            ",
            "integer"
        );
        inferfails!(
            "type E := A | B end
             match A with
                A -> true
                | B -> 1
             end
            ",
            "Type error: expected boolean but found integer.",
            5,
            17
        );
        inferfails!(
            "type E := A | B end
             type F := C | D end
             match A with
                 A -> 0
                | D -> 1
             end
            ",
            "Type error: expected E but found F.",
            6,
            17
        );
        inferfails!(
            "type E := A | B end
             fn f () -> A end
             match false with
                A -> 0
                | B -> 1
             end
            ",
            "Match statement: expected datatype.",
            6,
            17
        );
        inferfails!(
            "type E := A | B end
             type F := C | D end
             fn f () -> A end
             match f () with
                 C -> 0
                | D -> 1
             end
            ",
            "Type error: expected E but found F.",
            7,
            17
        );
        infer!(
            "type Maybe := Some x | None end
             match Some 1 with
                Some x -> x
                | None -> 0
             end
            ",
            "integer"
        );
        inferfails!(
            "type E := A | B end
             match A with
                 A -> 0
                | false -> 1
             end
            ",
            "Unknown variant in match: false.",
            5,
            17
        );
        inferfails!(
            "type E := A | B | C | D end
             match A with
                 A -> 0
             end
            ",
            "Missing variants in match of E: B C D.",
            4,
            17
        );
    }
}
