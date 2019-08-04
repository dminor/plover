use crate::interpreter;
use std::collections::HashMap;
use std::fmt;

macro_rules! err {
    ($vm:expr, $msg:expr) => {{
        return Err(interpreter::InterpreterError {
            err: $msg.to_string(),
            line: $vm.line,
            col: $vm.col,
        });
    }};
}

pub enum Opcode {
    Add,
    And,
    Arg(usize),
    Bconst(bool),
    Call,
    Div,
    Dup,
    Equal,
    Fconst(usize),
    GetEnv(String),
    Greater,
    GreaterEqual,
    Iconst(i64),
    Jmp(i64),
    Jz(i64),
    Less,
    LessEqual,
    Mod,
    Mul,
    Not,
    NotEqual,
    Or,
    Pop,
    Ret(usize),
    Rot,
    SetEnv(String),
    Srcpos(usize, usize),
    Sub,
    Swap,
}

impl fmt::Display for Opcode {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Opcode::Add => write!(f, "add"),
            Opcode::And => write!(f, "and"),
            Opcode::Arg(n) => write!(f, "arg {}", n),
            Opcode::Bconst(b) => write!(f, "const {}", b),
            Opcode::Call => write!(f, "call"),
            Opcode::Div => write!(f, "div"),
            Opcode::Dup => write!(f, "dup"),
            Opcode::Equal => write!(f, "eq"),
            Opcode::Fconst(ip) => write!(f, "lambda @{}", ip),
            Opcode::GetEnv(id) => write!(f, "getenv {}", id),
            Opcode::Greater => write!(f, "gt"),
            Opcode::GreaterEqual => write!(f, "ge"),
            Opcode::Iconst(i) => write!(f, "const {}", i),
            Opcode::Jmp(ip) => write!(f, "jmp {}", ip),
            Opcode::Jz(ip) => write!(f, "jz {}", ip),
            Opcode::Less => write!(f, "lt"),
            Opcode::LessEqual => write!(f, "le"),
            Opcode::Mod => write!(f, "mod"),
            Opcode::Mul => write!(f, "mul"),
            Opcode::Not => write!(f, "not"),
            Opcode::NotEqual => write!(f, "neq"),
            Opcode::Or => write!(f, "or"),
            Opcode::Pop => write!(f, "pop"),
            Opcode::Ret(n) => write!(f, "ret {}", n),
            Opcode::Rot => write!(f, "rot"),
            Opcode::SetEnv(id) => write!(f, "setenv {}", id),
            Opcode::Srcpos(line, col) => write!(f, "srcpos {} {}", line, col),
            Opcode::Sub => write!(f, "sub"),
            Opcode::Swap => write!(f, "swap"),
        }
    }
}

pub struct Function {
    ip: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Boolean(bool),
    Function(usize),
    Integer(i64),
    Tuple(Vec<Value>),
}

impl fmt::Display for Value {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Function(ip) => write!(f, "(lambda @{})", ip),
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

pub struct VirtualMachine {
    pub instructions: Vec<Opcode>,
    pub ip: usize,
    pub stack: Vec<Value>,
    pub callstack: Vec<(Function, usize, usize)>,
    pub fconsts: Vec<Function>,

    pub env: HashMap<String, Value>,
    pub type_env: HashMap<String, interpreter::Type>,

    pub line: usize,
    pub col: usize,
}

impl VirtualMachine {
    pub fn run(&mut self) -> Result<(), interpreter::InterpreterError> {
        while self.ip < self.instructions.len() {
            match &self.instructions[self.ip] {
                Opcode::Add => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            self.stack.push(Value::Integer(x + y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::And => match self.stack.pop() {
                    Some(Value::Boolean(x)) => match self.stack.pop() {
                        Some(Value::Boolean(y)) => {
                            self.stack.push(Value::Boolean(x && y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Arg(offset) => match self.callstack.last() {
                    Some((_, sp, _)) => {
                        self.stack.push(self.stack[*sp - offset].clone());
                    }
                    None => err!(self, "Call stack underflow."),
                },
                Opcode::Bconst(b) => {
                    self.stack.push(Value::Boolean(*b));
                }
                Opcode::Call => match self.stack.pop() {
                    Some(Value::Function(ip)) => {
                        let return_ip = self.ip;
                        self.ip = ip;
                        self.callstack
                            .push((Function { ip: ip }, self.stack.len() - 1, return_ip));
                        continue;
                    }
                    _ => unreachable!(),
                },
                Opcode::Div => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            if y == 0 {
                                err!(self, "Division by zero.")
                            }
                            self.stack.push(Value::Integer(x / y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Dup => match self.stack.pop() {
                    Some(v) => {
                        self.stack.push(v.clone());
                        self.stack.push(v);
                    }
                    _ => unreachable!(),
                },
                Opcode::Equal => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push(Value::Boolean(x == y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Fconst(ip) => {
                    self.stack.push(Value::Function(*ip));
                }
                Opcode::GetEnv(id) => match self.env.get(id) {
                    Some(x) => {
                        self.stack.push(x.clone());
                    }
                    None => err!(self, "Unknown identifier."),
                },
                Opcode::Greater => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            self.stack.push(Value::Boolean(x > y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::GreaterEqual => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            self.stack.push(Value::Boolean(x >= y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Iconst(i) => {
                    self.stack.push(Value::Integer(*i));
                }
                Opcode::Jmp(offset) => {
                    self.ip = (self.ip as i64 + offset) as usize;
                    continue;
                }
                Opcode::Jz(offset) => match self.stack.pop() {
                    Some(Value::Boolean(v)) => {
                        if !v {
                            self.ip = (self.ip as i64 + offset) as usize;
                            continue;
                        }
                    }
                    _ => unreachable!(),
                },
                Opcode::Less => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            self.stack.push(Value::Boolean(x < y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::LessEqual => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            self.stack.push(Value::Boolean(x <= y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Mod => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            if y == 0 {
                                err!(self, "Division by zero.")
                            }
                            self.stack.push(Value::Integer(x % y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Mul => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            self.stack.push(Value::Integer(x * y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::NotEqual => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push(Value::Boolean(x != y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Not => match self.stack.pop() {
                    Some(Value::Boolean(x)) => {
                        self.stack.push(Value::Boolean(!x));
                    }
                    _ => unreachable!(),
                },
                Opcode::Or => match self.stack.pop() {
                    Some(Value::Boolean(x)) => match self.stack.pop() {
                        Some(Value::Boolean(y)) => {
                            self.stack.push(Value::Boolean(x || y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Pop => match self.stack.pop() {
                    Some(_) => {}
                    _ => unreachable!(),
                },
                Opcode::Ret(n) => match self.callstack.pop() {
                    Some((_, sp, ip)) => {
                        self.stack.drain(sp..sp + n);
                        self.ip = ip;
                    }
                    None => err!(self, "Call stack underflow."),
                },
                Opcode::Rot => {
                    if self.stack.len() < 3 {
                        err!(self, "Stack underflow.")
                    }
                    if let Some(a) = self.stack.pop() {
                        self.stack.insert(self.stack.len() - 2, a);
                    }
                }
                Opcode::SetEnv(id) => match self.stack.pop() {
                    Some(x) => {
                        self.env.insert(id.to_string(), x);
                    }
                    _ => unreachable!(),
                },
                Opcode::Srcpos(line, col) => {
                    self.line = *line;
                    self.col = *col;
                }
                Opcode::Sub => match self.stack.pop() {
                    Some(Value::Integer(x)) => match self.stack.pop() {
                        Some(Value::Integer(y)) => {
                            self.stack.push(Value::Integer(x - y));
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
                Opcode::Swap => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push(x);
                            self.stack.push(y);
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                },
            }
            self.ip += 1;
        }
        Ok(())
    }

    pub fn new() -> VirtualMachine {
        VirtualMachine {
            instructions: Vec::new(),
            ip: 0,
            stack: Vec::new(),
            callstack: Vec::new(),
            fconsts: Vec::new(),
            env: HashMap::new(),
            type_env: HashMap::new(),
            line: usize::max_value(),
            col: usize::max_value(),
        }
    }
}
