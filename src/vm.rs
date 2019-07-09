use crate::interpreter;
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
    Equal,
    Fconst(usize),
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
    Srcpos(usize, usize),
    Sub,
    Swap,
}

pub struct Function {
    ip: usize,
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
            Opcode::Equal => write!(f, "eq"),
            Opcode::Fconst(ip) => write!(f, "lambda @{}", ip),
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
            Opcode::Srcpos(line, col) => write!(f, "srcpos {} {}", line, col),
            Opcode::Sub => write!(f, "sub"),
            Opcode::Swap => write!(f, "swap"),
        }
    }
}

pub struct VirtualMachine {
    pub instructions: Vec<Opcode>,
    pub ip: usize,
    pub stack: Vec<i64>,
    pub callstack: Vec<(Function, usize, usize)>,

    pub line: usize,
    pub col: usize,
}

impl VirtualMachine {
    pub fn run(&mut self) -> Result<(), interpreter::InterpreterError> {
        while self.ip < self.instructions.len() {
            match &self.instructions[self.ip] {
                Opcode::Add => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push(x + y);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::And => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            let b = x != 0 && y != 0;
                            self.stack.push(b as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Arg(offset) => match self.callstack.last() {
                    Some((_, sp, _)) => {
                        self.stack.push(self.stack[*sp - offset]);
                    }
                    None => err!(self, "Call stack underflow."),
                },
                Opcode::Bconst(b) => {
                    self.stack.push(*b as i64);
                }
                Opcode::Call => match self.stack.pop() {
                    Some(fun) => unsafe {
                        let boxed = Box::from_raw(fun as *mut Function);
                        let ip = self.ip;
                        self.ip = boxed.ip;
                        self.callstack.push((*boxed, self.stack.len() - 1, ip));
                        continue;
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Div => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            if y == 0 {
                                err!(self, "Division by zero.")
                            }
                            self.stack.push(x / y);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Equal => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push((x == y) as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Fconst(ip) => {
                    let fun = Function { ip: *ip };
                    let boxed: Box<Function> = Box::new(fun);
                    let ptr = Box::into_raw(boxed);
                    self.stack.push(ptr as i64);
                }
                Opcode::Greater => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push((x > y) as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::GreaterEqual => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push((x >= y) as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Iconst(i) => {
                    self.stack.push(*i);
                }
                Opcode::Jmp(offset) => {
                    self.ip = (self.ip as i64 + offset) as usize;
                    continue;
                }
                Opcode::Jz(offset) => match self.stack.pop() {
                    Some(v) => {
                        if v == 0 {
                            self.ip = (self.ip as i64 + offset) as usize;
                            continue;
                        }
                    }
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Less => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push((x < y) as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::LessEqual => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push((x <= y) as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Mod => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            if y == 0 {
                                err!(self, "Division by zero.")
                            }
                            self.stack.push(x % y);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Mul => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push(x * y);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::NotEqual => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push((x != y) as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Not => match self.stack.pop() {
                    Some(x) => {
                        self.stack.push((x == 0) as i64);
                    }
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Or => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            let b = (x != 0) || (y != 0);
                            self.stack.push(b as i64);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Pop => match self.stack.pop() {
                    Some(_) => {}
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Ret(n) => match self.callstack.pop() {
                    Some((_, sp, ip)) => {
                        self.stack.drain(sp..sp + n);
                        self.ip = ip;
                    }
                    None => err!(self, "Call stack underflow."),
                },
                Opcode::Srcpos(line, col) => {
                    self.line = *line;
                    self.col = *col;
                }
                Opcode::Sub => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push(x - y);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
                },
                Opcode::Swap => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
                            self.stack.push(x);
                            self.stack.push(y);
                        }
                        None => err!(self, "Stack underflow."),
                    },
                    None => err!(self, "Stack underflow."),
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
            line: usize::max_value(),
            col: usize::max_value(),
        }
    }
}
