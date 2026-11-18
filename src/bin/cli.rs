//! A minimal command line interface evaluating expressions over the reals.
//!
//! Expressions given as arguments are evaluated and printed, otherwise expressions are read from stdin line by line.

use std::io::{self, BufRead, IsTerminal, Write};

use formalith::{field::real::R, try_parse};

fn eval(input: &str) {
    match try_parse!(input, R) {
        Ok(term) => println!("{term}"),
        Err(err) => eprintln!("error: {err}"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !args.is_empty() {
        args.iter().for_each(|arg| eval(arg));
        return;
    }

    let interactive = io::stdin().is_terminal();
    let mut lines = io::stdin().lock().lines();
    loop {
        if interactive {
            print!("> ");
            io::stdout().flush().unwrap();
        }
        let Some(Ok(line)) = lines.next() else {
            break;
        };
        match line.trim() {
            "" => {}
            "exit" | "quit" => break,
            input => eval(input),
        }
    }
}
