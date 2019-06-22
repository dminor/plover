use std::cmp::min;
use std::env;
use std::fs::File;
use std::io::prelude::*;

mod parser;

use std::io::{self, BufRead, Write};

fn eval(filename: &str, src: &str) {
    let lines: Vec<&str> = src.split('\n').collect();
    match parser::parse(&src) {
        parser::ParseResult::Matched(ast, _) => {
            println!("{}", ast.to_string());
        }
        parser::ParseResult::NotMatched(_) => {
            println!("parse did not match any productions!?");
        }
        parser::ParseResult::Error(err, line, col) => {
            let line = min(lines.len(), line);
            let col = min(lines[line - 1].len(), col);
            let width = line.to_string().len() + 2;
            println!("{}", err);
            println!("{s:>width$}|", s = " ", width = width);
            println!(" {} | {}", line, lines[line - 1]);
            print!("{s:>width$}|", s = " ", width = width);
            println!("{s:>width$}^", s = " ", width = col);
            println!("--> {}:{}", filename, line);
        }
    }
}

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    for i in 1..args.len() {
        let filename = &args[i];
        let mut file = File::open(&filename)?;
        let mut program = String::new();
        file.read_to_string(&mut program)?;
        eval(&filename, &program);
        return Ok(());
    }

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    println!("Welcome to Hobbes!");
    print!("> ");
    stdout.flush()?;

    for line in stdin.lock().lines() {
        match line {
            Ok(src) => {
                eval("<stdin>", &src);
            }
            _ => break,
        }
        print!("> ");
        stdout.flush()?;
    }

    Ok(())
}
