use std::fmt;

/*
expression     -> "let" ( IDENTIFIER ":=" expression )* in expression end
                  | conditional
conditional    -> "if" equality "then" expression
                  ("elsif" equality "then" expression)*
                  "else" expression "end"
                  | equality
equality       -> comparison ( ( "!=" | "==" ) comparison )*
comparison     -> addition ( ( ">" | ">=" | "<" | "<=" ) addition )*
addition       -> multiplication ( ( "+" | "-" | "or" ) multiplication )*
multiplication -> unary ( ( "/" | "*" | "|" | "mod" | "and" ) unary )*
unary          -> ( "!" | "-" ) unary | call
call           -> value ( "(" ( value ,? )* ")" )?
value          -> IDENTIFIER | INTEGER | STRING | "false" | "true"
                  | "(" expression ")" | "[" ( expression )* "]"
                  | "fn" "(" ( IDENTIFIER ,? ) * ")" expression end
*/

macro_rules! binary_op {
    ($value:expr, $operator:tt, $ps:expr) => {{
        match $value($ps.clone()) {
            ParseResult::Matched(mut lhs, ps) => {
                let mut lps = ps.clone();
                loop {
                    lps = skip!(lps, whitespace);
                    let op = $operator!(lps);
                    lps = skip!(lps, whitespace);
                    match $value(lps) {
                        ParseResult::Matched(rhs, ps) => {
                            lhs = AST::BinaryOp(op, Box::new(lhs), Box::new(rhs));
                            lps = ps;
                        }
                        ParseResult::NotMatched(ps) => {
                            return ParseResult::Error(
                                "Expected value.".to_string(),
                                ps.line,
                                ps.col,
                            );
                        }
                        ParseResult::Error(err, line, col) => {
                            return ParseResult::Error(err, line, col);
                        }
                    }
                }
                ParseResult::Matched(lhs, lps)
            }
            ParseResult::NotMatched(ps) => ParseResult::NotMatched(ps),
            ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
        }
    }};
}

macro_rules! addition_operator {
    ($ps:expr) => {{
        match $ps.chars.peek() {
            Some(c) => match c {
                '+' => {
                    $ps.chars.next();
                    Operator::Plus
                }
                '-' => {
                    $ps.chars.next();
                    Operator::Minus
                }
                '|' => {
                    $ps.chars.next();
                    match $ps.chars.next() {
                        Some('|') => Operator::Or,
                        _ => {
                            return ParseResult::Error(
                                "Expected |.".to_string(),
                                $ps.line,
                                $ps.col,
                            );
                        }
                    }
                }
                _ => {
                    break;
                }
            },
            None => {
                break;
            }
        }
    }};
}

macro_rules! comparison_operator {
    ($ps:expr) => {{
        match $ps.chars.peek() {
            Some(c) => match c {
                '<' => {
                    $ps.chars.next();
                    match $ps.chars.peek() {
                        Some('=') => {
                            $ps.chars.next();
                            Operator::LessEqual
                        }
                        _ => Operator::Less,
                    }
                }
                '>' => {
                    $ps.chars.next();
                    match $ps.chars.peek() {
                        Some('=') => {
                            $ps.chars.next();
                            Operator::GreaterEqual
                        }
                        _ => Operator::Greater,
                    }
                }
                _ => {
                    break;
                }
            },
            None => {
                break;
            }
        }
    }};
}

macro_rules! equality_operator {
    ($ps:expr) => {{
        match $ps.chars.peek() {
            Some(c) => match c {
                '!' => {
                    $ps.chars.next();
                    match $ps.chars.next() {
                        Some('=') => Operator::NotEqual,
                        _ => {
                            return ParseResult::Error(
                                "Expected =.".to_string(),
                                $ps.line,
                                $ps.col,
                            );
                        }
                    }
                }
                '=' => {
                    $ps.chars.next();
                    match $ps.chars.next() {
                        Some('=') => Operator::Equal,
                        _ => {
                            return ParseResult::Error(
                                "Expected =.".to_string(),
                                $ps.line,
                                $ps.col,
                            );
                        }
                    }
                }
                _ => {
                    break;
                }
            },
            None => {
                break;
            }
        }
    }};
}

macro_rules! multiplication_operator {
    ($ps:expr) => {{
        match $ps.chars.peek() {
            Some(c) => match c {
                '*' => {
                    $ps.chars.next();
                    Operator::Multiply
                }
                '/' => {
                    $ps.chars.next();
                    Operator::Divide
                }
                '%' => {
                    $ps.chars.next();
                    Operator::Mod
                }
                '&' => {
                    $ps.chars.next();
                    match $ps.chars.next() {
                        Some('&') => Operator::And,
                        _ => {
                            return ParseResult::Error(
                                "Expected &.".to_string(),
                                $ps.line,
                                $ps.col,
                            );
                        }
                    }
                }
                _ => {
                    break;
                }
            },
            None => {
                break;
            }
        }
    }};
}

macro_rules! or {
    ($ps:expr, $( $fn:expr),* ) => {{
        $(
            match $fn($ps.clone()) {
                ParseResult::Matched(ast, ps) => {
                    return ParseResult::Matched(ast, ps);
                }
                ParseResult::NotMatched(_) => {}
                ParseResult::Error(err, line, col) => {
                    return ParseResult::Error(err, line, col);
                }
            }
        )*
        ParseResult::NotMatched($ps)
    }};
}

macro_rules! skip {
    ($chars:expr, $fn:expr) => {{
        match $fn($chars) {
            ParseResult::Matched(_, ps) | ParseResult::NotMatched(ps) => ps,
            ParseResult::Error(err, line, col) => {
                return ParseResult::Error(err, line, col);
            }
        }
    }};
}

pub enum Operator {
    Plus,
    Minus,
    Multiply,
    Divide,
    Mod,
    And,
    Not,
    Or,
    Less,
    LessEqual,
    Equal,
    NotEqual,
    GreaterEqual,
    Greater,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operator::Plus => write!(f, "+"),
            Operator::Minus => write!(f, "-"),
            Operator::Multiply => write!(f, "*"),
            Operator::Divide => write!(f, "/"),
            Operator::Mod => write!(f, "%"),
            Operator::And => write!(f, "&&"),
            Operator::Not => write!(f, "!"),
            Operator::Or => write!(f, "||"),
            Operator::Less => write!(f, "<"),
            Operator::LessEqual => write!(f, "<="),
            Operator::Equal => write!(f, "=="),
            Operator::NotEqual => write!(f, "!="),
            Operator::GreaterEqual => write!(f, ">="),
            Operator::Greater => write!(f, ">"),
        }
    }
}

pub enum AST {
    BinaryOp(Operator, Box<AST>, Box<AST>),
    Boolean(bool),
    Integer(i64),
    UnaryOp(Operator, Box<AST>),
    None,
}

impl fmt::Display for AST {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AST::BinaryOp(op, lhs, rhs) => write!(f, "({} {} {})", op, lhs, rhs),
            AST::Boolean(b) => write!(f, "{}:Boolean", b),
            AST::Integer(n) => write!(f, "{}:Integer", n),
            AST::UnaryOp(op, ast) => write!(f, "({} {})", op, ast),
            AST::None => write!(f, "None"),
        }
    }
}

pub enum ParseResult<'a> {
    Error(String, usize, usize),
    Matched(AST, ParseState<'a>),
    NotMatched(ParseState<'a>),
}

#[derive(Clone)]
pub struct ParseState<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    line: usize,
    col: usize,
}

fn expression(ps: ParseState) -> ParseResult {
    equality(ps)
}

fn equality(ps: ParseState) -> ParseResult {
    binary_op!(comparison, equality_operator, ps)
}

fn comparison(ps: ParseState) -> ParseResult {
    binary_op!(addition, comparison_operator, ps)
}

fn addition(ps: ParseState) -> ParseResult {
    binary_op!(multiplication, addition_operator, ps)
}

fn multiplication(ps: ParseState) -> ParseResult {
    binary_op!(unary, multiplication_operator, ps)
}

fn unary(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    lps = skip!(lps, whitespace);
    match lps.chars.peek() {
        Some(c) => match c {
            '!' => {
                lps.chars.next();
                match value(lps) {
                    ParseResult::Matched(ast, ps) => {
                        ParseResult::Matched(AST::UnaryOp(Operator::Not, Box::new(ast)), ps)
                    }
                    ParseResult::NotMatched(ps) => {
                        ParseResult::Error("Expected value.".to_string(), ps.line, ps.col)
                    }
                    ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
                }
            }
            '-' => {
                lps.chars.next();
                match value(lps) {
                    ParseResult::Matched(ast, ps) => {
                        ParseResult::Matched(AST::UnaryOp(Operator::Minus, Box::new(ast)), ps)
                    }
                    ParseResult::NotMatched(ps) => {
                        ParseResult::Error("Expected value.".to_string(), ps.line, ps.col)
                    }
                    ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
                }
            }
            _ => value(lps),
        },
        None => ParseResult::Error("Unexpected end of input.".to_string(), ps.line, ps.col),
    }
}

fn value(ps: ParseState) -> ParseResult {
    or!(ps, boolean, number)
}

fn whitespace(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    let mut succeeded = false;
    loop {
        match lps.chars.peek() {
            Some(c) => match c {
                ' ' | '\n' => {
                    succeeded = true;
                    lps.chars.next();
                }
                _ => {
                    break;
                }
            },
            _ => {
                break;
            }
        }
    }
    if succeeded {
        ParseResult::Matched(AST::None, lps)
    } else {
        ParseResult::NotMatched(ps)
    }
}

fn boolean(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    let mut s = String::new();
    loop {
        match lps.chars.peek() {
            Some(c) => {
                if c.is_alphabetic() {
                    s.push(*c);
                    lps.chars.next();
                } else {
                    break;
                }
            }
            _ => {
                break;
            }
        }
    }
    match &s[..] {
        "true" => ParseResult::Matched(AST::Boolean(true), lps),
        "false" => ParseResult::Matched(AST::Boolean(false), lps),
        _ => ParseResult::NotMatched(ps),
    }
}

fn number(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    let mut s = String::new();
    loop {
        match lps.chars.peek() {
            Some(c) => {
                if c.is_numeric() {
                    s.push(*c);
                    lps.chars.next();
                } else {
                    break;
                }
            }
            None => {
                break;
            }
        }
    }
    match s.parse::<i64>() {
        Ok(n) => ParseResult::Matched(AST::Integer(n), lps),
        _ => ParseResult::NotMatched(ps),
    }
}

pub fn parse(src: &str) -> ParseResult {
    let mut ps = ParseState {
        chars: src.chars().peekable(),
        line: usize::max_value(),
        col: usize::max_value(),
    };
    ps = skip!(ps, whitespace);
    expression(ps)
}

#[cfg(test)]
mod tests {
    use crate::parser;

    macro_rules! parse {
        ($input:expr, $value:expr) => {{
            match parser::parse($input) {
                parser::ParseResult::Matched(ast, mut ps) => {
                    assert_eq!(ast.to_string(), $value);
                    assert_eq!(ps.chars.next(), None);
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
    fn parse() {
        parse!("42", "42:Integer");
        parse!("42", "42:Integer");
        parse!("  42", "42:Integer");
        parse!("true", "true:Boolean");
        parse!("false", "false:Boolean");
        parse!("1 + 2", "(+ 1:Integer 2:Integer)");
        parse!("1 - 2", "(- 1:Integer 2:Integer)");
        parse!("1 * 2", "(* 1:Integer 2:Integer)");
        parse!("1 / 2", "(/ 1:Integer 2:Integer)");
        parse!("1 / 2 + 5", "(+ (/ 1:Integer 2:Integer) 5:Integer)");
        parse!("true && false", "(&& true:Boolean false:Boolean)");
        parse!("true || false", "(|| true:Boolean false:Boolean)");
        parse!("1 < 2", "(< 1:Integer 2:Integer)");
        parse!("1 <= 2", "(<= 1:Integer 2:Integer)");
        parse!("1 == 2", "(== 1:Integer 2:Integer)");
        parse!("1 != 2", "(!= 1:Integer 2:Integer)");
        parse!("1 >= 2", "(>= 1:Integer 2:Integer)");
        parse!("1 > 2", "(> 1:Integer 2:Integer)");
        parse!("1 > 2 * 4", "(> 1:Integer (* 2:Integer 4:Integer))");
        parse!("!true || false", "(|| (! true:Boolean) false:Boolean)");
        parse!("-42", "(- 42:Integer)");
    }
}
