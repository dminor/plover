use std::fmt;

use crate::pest::Parser;
use pest::iterators::Pair;

#[derive(Parser)]
#[grammar = "plover.pest"]
pub struct PloverParser;

#[derive(Clone, Debug)]
pub enum Operator {
    And,
    Divide,
    Equal,
    GreaterEqual,
    Greater,
    Less,
    LessEqual,
    Minus,
    Mod,
    Multiply,
    Not,
    NotEqual,
    Or,
    Plus,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operator::And => write!(f, "&&"),
            Operator::Divide => write!(f, "/"),
            Operator::Equal => write!(f, "=="),
            Operator::Greater => write!(f, ">"),
            Operator::GreaterEqual => write!(f, ">="),
            Operator::Less => write!(f, "<"),
            Operator::LessEqual => write!(f, "<="),
            Operator::Minus => write!(f, "-"),
            Operator::Multiply => write!(f, "*"),
            Operator::Mod => write!(f, "%"),
            Operator::Not => write!(f, "~"),
            Operator::NotEqual => write!(f, "~="),
            Operator::Or => write!(f, "||"),
            Operator::Plus => write!(f, "+"),
        }
    }
}

pub enum AST {
    BinaryOp(Operator, Box<AST>, Box<AST>, usize, usize),
    Boolean(bool, usize, usize),
    Call(Box<AST>, Box<AST>, usize, usize),
    Datatype(String, Vec<(String, Option<AST>)>, usize, usize),
    Define(Box<AST>, Box<AST>, usize, usize),
    Function(Option<String>, Box<AST>, Box<AST>, usize, usize),
    Identifier(String, usize, usize),
    If(Vec<(AST, AST)>, Box<AST>, usize, usize),
    Integer(i64, usize, usize),
    Match(Box<AST>, Vec<(String, Option<AST>, AST)>, usize, usize),
    Program(Vec<AST>, usize, usize),
    Tuple(Vec<AST>, usize, usize),
    UnaryOp(Operator, Box<AST>, usize, usize),
    Unit(usize, usize),
}

impl fmt::Display for AST {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AST::BinaryOp(op, lhs, rhs, _, _) => write!(f, "({} {} {})", op, lhs, rhs),
            AST::Boolean(b, _, _) => write!(f, "{}:Boolean", b),
            AST::Call(fun, args, _, _) => write!(f, "(apply {} {})", fun, args),
            AST::Datatype(name, variants, _, _) => {
                write!(f, "(")?;
                for i in 0..variants.len() {
                    write!(f, "{}", variants[i].0)?;
                    if let Some(param) = &variants[i].1 {
                        write!(f, ": {}", param)?;
                    }
                    if i + 1 != variants.len() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ") {}:Type", name)
            }
            AST::Define(id, value, _, _) => write!(f, "(define {} {})", id, value),
            AST::Function(id, param, body, _, _) => {
                if let Some(id) = id {
                    write!(f, "({} {} {})", id, param, body)
                } else {
                    write!(f, "(fn {} {})", param, body)
                }
            }
            AST::Identifier(id, _, _) => write!(f, "{}:Identifier", id),
            AST::If(conds, els, _, _) => {
                write!(f, "(if ")?;
                for cond in conds {
                    write!(f, "(cond {} {}) ", cond.0, cond.1)?;
                }
                write!(f, "(else {}))", els)
            }
            AST::Integer(n, _, _) => write!(f, "{}:Integer", n),
            AST::Match(id, cases, _, _) => {
                write!(f, "(match {} ", id)?;
                for i in 0..cases.len() {
                    if let Some(param) = &cases[i].1 {
                        write!(f, "(case {}: {} {})", cases[i].0, param, cases[i].2)?;
                    } else {
                        write!(f, "(case {} {})", cases[i].0, cases[i].2)?;
                    }
                    if i + 1 != cases.len() {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")
            }
            AST::Program(expressions, _, _) => {
                if expressions.len() > 1 {
                    write!(f, "(")?;
                }
                for i in 0..expressions.len() {
                    write!(f, "{}", expressions[i])?;
                    if i + 1 != expressions.len() {
                        write!(f, " ")?;
                    }
                }
                if expressions.len() > 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            AST::Tuple(elements, _, _) => {
                write!(f, "(")?;
                for i in 0..elements.len() {
                    write!(f, "{}", elements[i])?;
                    if i + 1 != elements.len() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "):Tuple")
            }
            AST::UnaryOp(op, ast, _, _) => write!(f, "({} {})", op, ast),
            AST::Unit(_, _) => write!(f, "():Unit"),
        }
    }
}

pub struct ParseError {
    pub msg: String,
    pub line: usize,
    pub col: usize,
}

#[allow(clippy::cognitive_complexity)]
fn astify(pair: Pair<Rule>) -> AST {
    match pair.as_rule() {
        Rule::addition => {
            let mut inner = pair.into_inner();
            let mut lhs = astify(inner.next().unwrap());
            loop {
                if inner.peek().is_none() {
                    break;
                } else {
                    let pair = inner.next().unwrap();
                    if let Rule::addition_op = pair.as_rule() {
                        let (line, col) = pair.as_span().start_pos().line_col();
                        let op = match pair.into_inner().next().unwrap().as_rule() {
                            Rule::minus => Operator::Minus,
                            Rule::or => Operator::Or,
                            Rule::plus => Operator::Plus,
                            _ => unreachable!(),
                        };
                        let rhs = inner.next().unwrap();
                        lhs = AST::BinaryOp(op, Box::new(lhs), Box::new(astify(rhs)), line, col)
                    } else {
                        unreachable!();
                    }
                }
            }
            lhs
        }
        Rule::boolean => {
            let (line, col) = pair.as_span().start_pos().line_col();
            AST::Boolean(pair.as_str().trim().parse().unwrap(), line, col)
        }
        Rule::call => {
            let (line, col) = pair.as_span().start_pos().line_col();
            let mut inner = pair.into_inner();
            let value_or_fn = astify(inner.next().unwrap());
            if inner.peek().is_some() {
                AST::Call(
                    Box::new(value_or_fn),
                    Box::new(astify(inner.next().unwrap())),
                    line,
                    col,
                )
            } else {
                value_or_fn
            }
        }
        Rule::comparison => {
            let mut inner = pair.into_inner();
            let mut lhs = astify(inner.next().unwrap());
            loop {
                if inner.peek().is_none() {
                    break;
                } else {
                    let pair = inner.next().unwrap();
                    if let Rule::comparison_op = pair.as_rule() {
                        let (line, col) = pair.as_span().start_pos().line_col();
                        let op = match pair.into_inner().next().unwrap().as_rule() {
                            Rule::greater => Operator::Greater,
                            Rule::greater_equal => Operator::GreaterEqual,
                            Rule::less => Operator::Less,
                            Rule::less_equal => Operator::LessEqual,
                            _ => unreachable!(),
                        };
                        let rhs = inner.next().unwrap();
                        lhs = AST::BinaryOp(op, Box::new(lhs), Box::new(astify(rhs)), line, col)
                    } else {
                        unreachable!();
                    }
                }
            }
            lhs
        }
        Rule::conditional => {
            if pair.as_str().starts_with("if") {
                let (line, col) = pair.as_span().start_pos().line_col();
                let mut conds = Vec::<(AST, AST)>::new();
                let mut inner = pair.into_inner();
                loop {
                    let cond_or_else = astify(inner.next().unwrap());
                    if inner.peek().is_some() {
                        let then = astify(inner.next().unwrap());
                        conds.push((cond_or_else, then));
                    } else {
                        return AST::If(conds, Box::new(cond_or_else), line, col);
                    }
                }
            } else {
                astify(pair.into_inner().next().unwrap())
            }
        }
        Rule::datatype => {
            let (line, col) = pair.as_span().start_pos().line_col();
            let mut inner = pair.into_inner();
            let name = inner.next().unwrap().as_str().trim();
            let mut variants = Vec::new();
            for variant in inner {
                let mut inner = variant.into_inner();
                let id = inner.next().unwrap().as_str().trim().to_string();
                let mut params = Vec::new();
                for param in inner {
                    params.push(astify(param));
                }
                let param = match params.len() {
                    0 => None,
                    1 => Some(params.pop().unwrap()),
                    _ => Some(AST::Tuple(params, line, col)),
                };
                variants.push((id, param));
            }
            AST::Datatype(name.into(), variants, line, col)
        }
        Rule::def => {
            let (line, col) = pair.as_span().start_pos().line_col();
            let mut inner = pair.into_inner();
            let id = astify(inner.next().unwrap());
            let value = astify(inner.next().unwrap());
            AST::Define(Box::new(id), Box::new(value), line, col)
        }
        Rule::equality => {
            let mut inner = pair.into_inner();
            let mut lhs = astify(inner.next().unwrap());
            loop {
                if inner.peek().is_none() {
                    break;
                } else {
                    let pair = inner.next().unwrap();
                    if let Rule::equality_op = pair.as_rule() {
                        let (line, col) = pair.as_span().start_pos().line_col();
                        let op = match pair.into_inner().next().unwrap().as_rule() {
                            Rule::equal => Operator::Equal,
                            Rule::not_equal => Operator::NotEqual,
                            _ => unreachable!(),
                        };
                        let rhs = inner.next().unwrap();
                        lhs = AST::BinaryOp(op, Box::new(lhs), Box::new(astify(rhs)), line, col)
                    } else {
                        unreachable!();
                    }
                }
            }
            lhs
        }
        Rule::function => {
            let (line, col) = pair.as_span().start_pos().line_col();
            let mut inner = pair.into_inner();
            let id_or_param = inner.next().unwrap();
            let param_or_body = astify(inner.next().unwrap());
            if inner.peek().is_none() {
                AST::Function(
                    None,
                    Box::new(astify(id_or_param)),
                    Box::new(param_or_body),
                    line,
                    col,
                )
            } else {
                let body = astify(inner.next().unwrap());
                AST::Function(
                    Some(id_or_param.as_str().to_string()),
                    Box::new(param_or_body),
                    Box::new(body),
                    line,
                    col,
                )
            }
        }
        Rule::identifier => {
            let (line, col) = pair.as_span().start_pos().line_col();
            AST::Identifier(pair.as_str().trim().parse().unwrap(), line, col)
        }
        Rule::match_expr => {
            let (line, col) = pair.as_span().start_pos().line_col();
            let mut inner = pair.into_inner();
            let cond = astify(inner.next().unwrap());
            let mut cases = Vec::new();
            loop {
                let variant = inner.next().unwrap();
                let mut variant_inner = variant.into_inner();
                let id = variant_inner.next().unwrap().as_str().to_string();
                let mut params = Vec::new();
                for param in variant_inner {
                    params.push(astify(param));
                }
                let param = match params.len() {
                    0 => None,
                    1 => Some(params.pop().unwrap()),
                    _ => Some(AST::Tuple(params, line, col)),
                };
                let expr = astify(inner.next().unwrap());
                cases.push((id, param, expr));
                if inner.peek().is_none() {
                    break;
                }
            }
            AST::Match(Box::new(cond), cases, line, col)
        }
        Rule::multiplication => {
            let mut inner = pair.into_inner();
            let mut lhs = astify(inner.next().unwrap());
            loop {
                if inner.peek().is_none() {
                    break;
                } else {
                    let pair = inner.next().unwrap();
                    if let Rule::multiplication_op = pair.as_rule() {
                        let (line, col) = pair.as_span().start_pos().line_col();
                        let op = match pair.into_inner().next().unwrap().as_rule() {
                            Rule::and => Operator::And,
                            Rule::divide => Operator::Divide,
                            Rule::modulus => Operator::Mod,
                            Rule::multiply => Operator::Multiply,
                            _ => unreachable!(),
                        };
                        let rhs = inner.next().unwrap();
                        lhs = AST::BinaryOp(op, Box::new(lhs), Box::new(astify(rhs)), line, col)
                    } else {
                        unreachable!();
                    }
                }
            }
            lhs
        }
        Rule::number => {
            let (line, col) = pair.as_span().start_pos().line_col();
            AST::Integer(pair.as_str().trim().parse().unwrap(), line, col)
        }
        Rule::body | Rule::program => {
            let (line, col) = pair.as_span().start_pos().line_col();
            let mut exprs = Vec::new();
            for expr in pair.into_inner() {
                if expr.as_rule() != Rule::EOI {
                    exprs.push(astify(expr));
                }
            }
            AST::Program(exprs, line, col)
        }
        Rule::unary => {
            let mut inner = pair.into_inner();
            let pair = inner.next().unwrap();
            if let Rule::unary_op = pair.as_rule() {
                let (line, col) = pair.as_span().start_pos().line_col();
                let op = match pair.into_inner().next().unwrap().as_rule() {
                    Rule::minus => Operator::Minus,
                    Rule::not => Operator::Not,
                    _ => unreachable!(),
                };
                AST::UnaryOp(op, Box::new(astify(inner.next().unwrap())), line, col)
            } else {
                astify(pair)
            }
        }
        Rule::tuple => {
            let (line, col) = pair.as_span().start_pos().line_col();
            let mut elements = Vec::new();
            let mut inner = pair.into_inner();
            while inner.peek().is_some() {
                elements.push(astify(inner.next().unwrap()));
            }
            AST::Tuple(elements, line, col)
        }
        Rule::unit => {
            let (line, col) = pair.as_span().start_pos().line_col();
            AST::Unit(line, col)
        }
        Rule::value => astify(pair.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

pub fn parse(src: &str) -> Result<AST, ParseError> {
    match PloverParser::parse(Rule::program, src) {
        Ok(mut program) => Ok(astify(program.next().unwrap())),
        Err(err) => Err(ParseError {
            msg: err.to_string(),
            line: 0,
            col: 0,
        }),
    }
}

#[cfg(test)]
mod tests {
    use crate::parser;

    macro_rules! parse {
        ($input:expr, $value:expr) => {{
            match parser::parse($input) {
                Ok(ast) => {
                    assert_eq!(ast.to_string(), $value);
                }
                Err(err) => {
                    println!("ParseError: {} {} {}", err.msg, err.line, err.col);
                    assert!(false);
                }
            }
        }};
    }

    #[test]
    fn parse() {
        parse!("42", "42:Integer");
        parse!("  42", "42:Integer");
        parse!("  42 ", "42:Integer");
        parse!("true", "true:Boolean");
        parse!("false", "false:Boolean");
        parse!("-42", "(- 42:Integer)");
        parse!("- 42", "(- 42:Integer)");
        parse!("--42", "(- (- 42:Integer))");
        parse!("~true", "(~ true:Boolean)");
        parse!("1 * 2", "(* 1:Integer 2:Integer)");
        parse!("1*2", "(* 1:Integer 2:Integer)");
        parse!("1 / 2", "(/ 1:Integer 2:Integer)");
        parse!("true && false", "(&& true:Boolean false:Boolean)");
        parse!("true || false", "(|| true:Boolean false:Boolean)");
        parse!("1 / 2 * 3", "(* (/ 1:Integer 2:Integer) 3:Integer)");
        parse!("1 / 2 + 5", "(+ (/ 1:Integer 2:Integer) 5:Integer)");
        parse!("1 + 2", "(+ 1:Integer 2:Integer)");
        parse!("1 - 2", "(- 1:Integer 2:Integer)");
        parse!("1 < 2", "(< 1:Integer 2:Integer)");
        parse!("1 <= 2", "(<= 1:Integer 2:Integer)");
        parse!("1 == 2", "(== 1:Integer 2:Integer)");
        parse!("1 ~= 2", "(~= 1:Integer 2:Integer)");
        parse!("1 >= 2", "(>= 1:Integer 2:Integer)");
        parse!("1 > 2", "(> 1:Integer 2:Integer)");
        parse!("1 > 2 * 4", "(> 1:Integer (* 2:Integer 4:Integer))");
        parse!("~true || false", "(|| (~ true:Boolean) false:Boolean)");
        parse!(
            "2 < 3 == 3 < 4",
            "(== (< 2:Integer 3:Integer) (< 3:Integer 4:Integer))"
        );
        parse!(
            "2 * 3 ~= 1 - 2",
            "(~= (* 2:Integer 3:Integer) (- 1:Integer 2:Integer))"
        );
        parse!("1 / (2 + 5)", "(/ 1:Integer (+ 2:Integer 5:Integer))");
        parse!(
            "(1 < 2) == false",
            "(== (< 1:Integer 2:Integer) false:Boolean)"
        );
        parse!(
            "if true then 1 else 2 end",
            "(if (cond true:Boolean 1:Integer) (else 2:Integer))"
        );
        parse!(
            "if true then
                1
             elsif false then
                2
             else
                3
             end",
            "(if (cond true:Boolean 1:Integer) (cond false:Boolean 2:Integer) (else 3:Integer))"
        );
        parse!(
            "if true then
                if true then
                    1
                else
                    2
                end
             elsif false then
                3
             else
                4
             end",
            "(if (cond true:Boolean (if (cond true:Boolean 1:Integer) (else 2:Integer))) (cond false:Boolean 3:Integer) (else 4:Integer))"
        );
        parse!("x", "x:Identifier");
        parse!("x2", "x2:Identifier");
        parse!(
            "fn x -> x + 1 end",
            "(fn x:Identifier (+ x:Identifier 1:Integer))"
        );
        parse!("fn () -> 2 end", "(fn ():Unit 2:Integer)");
        parse!("fn f () -> 2 end", "(f ():Unit 2:Integer)");
        parse!(
            "fn (x, y) -> x + y end",
            "(fn (x:Identifier, y:Identifier):Tuple (+ x:Identifier y:Identifier))"
        );
        parse!(
            "fn f (x, y) -> x + y end",
            "(f (x:Identifier, y:Identifier):Tuple (+ x:Identifier y:Identifier))"
        );
        parse!("(1)", "1:Integer");
        parse!("(1,)", "(1:Integer):Tuple");
        parse!("(1, 2, 3)", "(1:Integer, 2:Integer, 3:Integer):Tuple");
        parse!(
            "(1, 2, (2 + 3))",
            "(1:Integer, 2:Integer, (+ 2:Integer 3:Integer)):Tuple"
        );
        parse!("f (1)", "(apply f:Identifier 1:Integer)");
        parse!(
            "fn x -> x + 1 end (1)",
            "(apply (fn x:Identifier (+ x:Identifier 1:Integer)) 1:Integer)"
        );
        parse!(
            "g(f(1))",
            "(apply g:Identifier (apply f:Identifier 1:Integer))"
        );
        parse!(
            "(g ())(1)",
            "(apply (apply g:Identifier ():Unit) 1:Integer)"
        );
        parse!("def x := 1", "(define x:Identifier 1:Integer)");
        parse!(
            "def f := fn x -> x + 1 end",
            "(define f:Identifier (fn x:Identifier (+ x:Identifier 1:Integer)))"
        );
        parse!(
            "def t := (1, 2, 3)",
            "(define t:Identifier (1:Integer, 2:Integer, 3:Integer):Tuple)"
        );
        parse!(
            "def x := 1
             def y := 2",
            "((define x:Identifier 1:Integer) (define y:Identifier 2:Integer))"
        );
        parse!(
            "def f := fn x -> def t := 2 x + t end",
            "(define f:Identifier (fn x:Identifier ((define t:Identifier 2:Integer) (+ x:Identifier t:Identifier))))"
        );
        parse!("type Option := Some | None end", "(Some, None) Option:Type");
        parse!(
            "type Option := Some (x) | None end",
            "(Some: x:Identifier, None) Option:Type"
        );
        parse!(
            "type Pair := Cons (a, b) | Null end",
            "(Cons: (a:Identifier, b:Identifier):Tuple, Null) Pair:Type"
        );
        parse!(
            "type Option := Some (x) | None end def a := Some (42)",
            "((Some: x:Identifier, None) Option:Type (define a:Identifier (apply Some:Identifier 42:Integer)))"
        );
        parse!("()", "():Unit");
        parse!("(   )", "():Unit");
        parse!("fn f () -> () end", "(f ():Unit ():Unit)");
        parse!(
            "fn f (x) -> x + 1 end",
            "(f x:Identifier (+ x:Identifier 1:Integer))"
        );
        parse!(
            "match p with A -> 0 end",
            "(match p:Identifier (case A 0:Integer))"
        );
        parse!(
            "match p with A -> 0 | B -> 1 end",
            "(match p:Identifier (case A 0:Integer) (case B 1:Integer))"
        );
        parse!(
            "match p with Cons (a, b) -> (1 + len(b)) | Null -> 0 end",
            "(match p:Identifier (case Cons: (a:Identifier, b:Identifier):Tuple (+ 1:Integer (apply len:Identifier b:Identifier))) (case Null 0:Integer))"
        );
        parse!(
            "match f () with
                A -> 0
                | B -> 1
             end
            ",
            "(match (apply f:Identifier ():Unit) (case A 0:Integer) (case B 1:Integer))"
        );
        parse!(
            "def t := 1
             def f := fn x ->
                 def t := 2
                 x + t
             end
             f(1)",
            "((define t:Identifier 1:Integer) (define f:Identifier (fn x:Identifier ((define t:Identifier 2:Integer) (+ x:Identifier t:Identifier)))) (apply f:Identifier 1:Integer))"
        );
        parse!(
            "fn fact (n) ->
                 fn iter(n, acc) ->
                    if n == 0 then
                       acc
                    else
                       iter(n - 1, n*acc)
                    end
                 end
                 iter(n, 1)
             end",
            "(fact n:Identifier ((iter (n:Identifier, acc:Identifier):Tuple (if (cond (== n:Identifier 0:Integer) acc:Identifier) (else (apply iter:Identifier ((- n:Identifier 1:Integer), (* n:Identifier acc:Identifier)):Tuple)))) (apply iter:Identifier (n:Identifier, 1:Integer):Tuple)))"
        );
    }
}
