use crate::interpreter;

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
    Bconst(bool),
    Div,
    Equal,
    Greater,
    GreaterEqual,
    Iconst(i64),
    Less,
    LessEqual,
    Mod,
    Mul,
    Not,
    NotEqual,
    Or,
    Srcpos(usize, usize),
    Sub,
}

pub struct VirtualMachine {
    pub instructions: Vec<Opcode>,
    pub ip: usize,
    pub stack: Vec<i64>,

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
                Opcode::Bconst(b) => {
                    self.stack.push(*b as i64);
                }
                Opcode::Div => match self.stack.pop() {
                    Some(x) => match self.stack.pop() {
                        Some(y) => {
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
            line: 0,
            col: 0,
        }
    }
}
