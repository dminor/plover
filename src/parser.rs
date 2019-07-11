use std::fmt;

/*
expression     -> "let" ( IDENTIFIER ":=" expression )* in expression end
                  | conditional
conditional    -> "if" equality "then" expression
                  ("elsif" equality "then" expression)*
                  "else" expression "end"
                  | equality
equality       -> comparison ( ( "~=" | "==" ) comparison )*
comparison     -> addition ( ( ">" | ">=" | "<" | "<=" ) addition )*
addition       -> multiplication ( ( "+" | "-" | "or" ) multiplication )*
multiplication -> unary ( ( "/" | "*" | "|" | "mod" | "and" ) unary )*
unary          -> ( "~" | "-" ) unary | call
call           -> value value | value
value          -> IDENTIFIER | INTEGER | STRING | "false" | "true"
                  | "(" expression ")" | "[" ( expression )* "]"
                  | "fn" ( IDENTIFIER ,? )* -> expression end
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

macro_rules! arrow {
    ($ps:expr) => {{
        match $ps.chars.peek() {
            Some(c) => match c {
                '-' => {
                    $ps.chars.next();
                    match $ps.chars.next() {
                        Some('>') => true,
                        _ => {
                            return ParseResult::Error(
                                "Expected >.".to_string(),
                                $ps.line,
                                $ps.col,
                            );
                        }
                    }
                }
                _ => false,
            },
            None => false,
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
                '~' => {
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

macro_rules! expect {
    ($ps:expr, $($keyword:expr),* ) => {{
        let mut s = String::new();
        loop {
            match $ps.chars.peek() {
                Some(c) => {
                    if c.is_alphabetic() {
                        s.push(*c);
                        $ps.chars.next();
                    } else {
                        break;
                    }
                }
                _ => {
                    break;
                }
            }
        }
        let mut result = None;
        $(
            if s == $keyword {
                result = Some(s.to_string());
            }
        )*
        result
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

#[derive(Clone)]
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
    BinaryOp(Operator, Box<AST>, Box<AST>),
    Boolean(bool),
    Call(Box<AST>, Box<AST>),
    Function(Box<AST>, Box<AST>),
    Identifier(String),
    If(Vec<(AST, AST)>, Box<AST>),
    Integer(i64),
    Tuple(Vec<AST>),
    UnaryOp(Operator, Box<AST>),
    None,
}

impl fmt::Display for AST {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AST::BinaryOp(op, lhs, rhs) => write!(f, "({} {} {})", op, lhs, rhs),
            AST::Boolean(b) => write!(f, "{}:Boolean", b),
            AST::Call(fun, args) => write!(f, "(apply {} {})", fun, args),
            AST::Function(param, body) => write!(f, "(fn {} {})", param, body),
            AST::Identifier(id) => write!(f, "{}:Identifier", id),
            AST::If(conds, els) => {
                write!(f, "(if ")?;
                for cond in conds {
                    write!(f, "(cond {} {}) ", cond.0, cond.1)?;
                }
                write!(f, "(else {}))", els)
            }
            AST::Integer(n) => write!(f, "{}:Integer", n),
            AST::Tuple(elements) => {
                write!(f, "(")?;
                for i in 0..elements.len() {
                    write!(f, "{}", elements[i])?;
                    if i + 1 != elements.len() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "):Tuple")
            }
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
    or!(ps, conditional, equality)
}

fn conditional(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    lps = skip!(lps, whitespace);
    let mut conds = Vec::<(AST, AST)>::new();
    match expect!(lps, "if") {
        Some(_) => loop {
            match expression(lps) {
                ParseResult::Matched(cond, ps) => {
                    lps = skip!(ps, whitespace);
                    match expect!(lps, "then") {
                        Some(_) => match expression(lps) {
                            ParseResult::Matched(then, ps) => {
                                lps = skip!(ps, whitespace);
                                conds.push((cond, then));
                                match expect!(lps, "elsif", "else") {
                                    Some(s) => match &s[..] {
                                        "else" => match expression(lps) {
                                            ParseResult::Matched(els, ps) => {
                                                lps = skip!(ps, whitespace);
                                                if let Some(_) = expect!(lps, "end") {
                                                    return ParseResult::Matched(
                                                        AST::If(conds, Box::new(els)),
                                                        lps,
                                                    );
                                                } else {
                                                    return ParseResult::Error(
                                                        "Expected end.".to_string(),
                                                        lps.line,
                                                        lps.col,
                                                    );
                                                }
                                            }
                                            ParseResult::NotMatched(ps) => {
                                                return ParseResult::Error(
                                                    "Expected expression.".to_string(),
                                                    ps.line,
                                                    ps.col,
                                                );
                                            }
                                            ParseResult::Error(err, line, col) => {
                                                return ParseResult::Error(err, line, col);
                                            }
                                        },
                                        "elsif" => {}
                                        _ => unreachable!(),
                                    },
                                    None => {
                                        return ParseResult::Error(
                                            "Expected elsif or else.".to_string(),
                                            lps.line,
                                            lps.col,
                                        );
                                    }
                                }
                            }
                            ParseResult::NotMatched(ps) => {
                                return ParseResult::Error(
                                    "Expected expression.".to_string(),
                                    ps.line,
                                    ps.col,
                                )
                            }
                            ParseResult::Error(err, line, col) => {
                                return ParseResult::Error(err, line, col);
                            }
                        },
                        None => {
                            return ParseResult::Error(
                                "Expected then clause.".to_string(),
                                lps.line,
                                lps.col,
                            );
                        }
                    }
                }
                ParseResult::NotMatched(ps) => {
                    return ParseResult::Error("Expected expression.".to_string(), ps.line, ps.col)
                }
                ParseResult::Error(err, line, col) => {
                    return ParseResult::Error(err, line, col);
                }
            }
        },
        None => ParseResult::NotMatched(ps),
    }
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
            '~' => {
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
            _ => call(lps),
        },
        None => ParseResult::Error("Unexpected end of input.".to_string(), ps.line, ps.col),
    }
}

fn call(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    lps = skip!(lps, whitespace);

    match value(lps) {
        ParseResult::Matched(fun, ps) => {
            lps = skip!(ps, whitespace);
            match value(lps) {
                ParseResult::Matched(args, ps) => {
                    ParseResult::Matched(AST::Call(Box::new(fun), Box::new(args)), ps)
                }
                ParseResult::NotMatched(ps) => ParseResult::Matched(fun, ps),
                ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
            }
        }
        ParseResult::NotMatched(ps) => {
            ParseResult::Error("Expected value.".to_string(), ps.line, ps.col)
        }
        ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
    }
}

fn value(ps: ParseState) -> ParseResult {
    or!(
        ps,
        boolean,
        function,
        tuple,
        identifier,
        integer,
        parenthesized_expression
    )
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
    match expect!(lps, "true", "false") {
        Some(s) => match &s[..] {
            "true" => ParseResult::Matched(AST::Boolean(true), lps),
            "false" => ParseResult::Matched(AST::Boolean(false), lps),
            _ => unreachable!(),
        },
        None => ParseResult::NotMatched(lps),
    }
}

fn function(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    if let Some(_) = expect!(lps, "fn") {
        lps = skip!(lps, whitespace);
        match value(lps) {
            ParseResult::Matched(param, ps) => {
                lps = skip!(ps, whitespace);
                if arrow!(lps) {
                    match expression(lps) {
                        ParseResult::Matched(body, ps) => {
                            lps = ps;
                            if let Some(_) = expect!(lps, "end") {
                                ParseResult::Matched(
                                    AST::Function(Box::new(param), Box::new(body)),
                                    lps,
                                )
                            } else {
                                ParseResult::Error("Expected end.".to_string(), lps.line, lps.col)
                            }
                        }
                        ParseResult::NotMatched(ps) => {
                            ParseResult::Error("Expected expression.".to_string(), ps.line, ps.col)
                        }
                        ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
                    }
                } else {
                    ParseResult::Error("Expected is.".to_string(), lps.line, lps.col)
                }
            }
            ParseResult::NotMatched(ps) => {
                ParseResult::Error("Expected value.".to_string(), ps.line, ps.col)
            }
            ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
        }
    } else {
        ParseResult::NotMatched(lps)
    }
}

fn identifier(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    let mut s = String::new();
    let mut first = true;
    loop {
        match lps.chars.peek() {
            Some(c) => {
                if first && c.is_alphabetic() {
                    first = false;
                    s.push(*c);
                    lps.chars.next();
                } else if !first && c.is_alphanumeric() {
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
    if !s.is_empty() {
        match &s[..] {
            "if" | "else" | "elsif" | "end" | "fn" | "then" => ParseResult::NotMatched(lps),
            _ => ParseResult::Matched(AST::Identifier(s), lps),
        }
    } else {
        ParseResult::NotMatched(lps)
    }
}

fn integer(ps: ParseState) -> ParseResult {
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

fn parenthesized_expression(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    if let Some('(') = lps.chars.next() {
        match expression(lps) {
            ParseResult::Matched(expr, mut ps) => {
                if let Some(')') = ps.chars.next() {
                    ParseResult::Matched(expr, ps)
                } else {
                    ParseResult::Error("Expected ).".to_string(), ps.line, ps.col)
                }
            }
            ParseResult::NotMatched(ps) => {
                ParseResult::Error("Expected expression.".to_string(), ps.line, ps.col)
            }
            ParseResult::Error(err, line, col) => ParseResult::Error(err, line, col),
        }
    } else {
        ParseResult::NotMatched(ps)
    }
}

fn tuple(ps: ParseState) -> ParseResult {
    let mut lps = ps.clone();
    let mut elements = Vec::new();
    lps = skip!(lps, whitespace);
    if let Some('(') = lps.chars.next() {
        let mut has_comma = false;
        loop {
            lps = skip!(lps, whitespace);
            // Allow for tuple with one element
            if let Some(')') = lps.chars.peek() {
                lps.chars.next();
                break;
            }
            match expression(lps) {
                ParseResult::Matched(element, ps) => {
                    lps = skip!(ps, whitespace);
                    elements.push(element);
                }
                ParseResult::NotMatched(ps) => {
                    return ParseResult::Error("Expected expression.".to_string(), ps.line, ps.col);
                }
                ParseResult::Error(err, line, col) => {
                    return ParseResult::Error(err, line, col);
                }
            }
            match lps.chars.next() {
                Some(',') => {
                    has_comma = true;
                }
                Some(')') => {
                    break;
                }
                None => {
                    return ParseResult::Error(
                        "Unexpected end of input.".to_string(),
                        lps.line,
                        lps.col,
                    );
                }
                _ => {
                    return ParseResult::Error("Expected , or ).".to_string(), lps.line, lps.col);
                }
            }
        }
        if has_comma {
            ParseResult::Matched(AST::Tuple(elements), lps)
        } else {
            ParseResult::NotMatched(ps)
        }
    } else {
        ParseResult::NotMatched(lps)
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
        parse!("1 ~= 2", "(~= 1:Integer 2:Integer)");
        parse!("1 >= 2", "(>= 1:Integer 2:Integer)");
        parse!("1 > 2", "(> 1:Integer 2:Integer)");
        parse!("1 > 2 * 4", "(> 1:Integer (* 2:Integer 4:Integer))");
        parse!("~true || false", "(|| (~ true:Boolean) false:Boolean)");
        parse!("-42", "(- 42:Integer)");
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
        parse!(
            "fn (x, y) -> x + y end",
            "(fn (x:Identifier, y:Identifier):Tuple (+ x:Identifier y:Identifier))"
        );
        parse!("(1)", "1:Integer");
        parse!("(1,)", "(1:Integer):Tuple");
        parse!("(1, 2, 3)", "(1:Integer, 2:Integer, 3:Integer):Tuple");
        parse!(
            "(1, 2, (2 + 3))",
            "(1:Integer, 2:Integer, (+ 2:Integer 3:Integer)):Tuple"
        );
        parse!(
            "fn x -> x + 1 end 1",
            "(apply (fn x:Identifier (+ x:Identifier 1:Integer)) 1:Integer)"
        );
    }
}
