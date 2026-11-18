//! A minimal command line interface evaluating expressions over the reals.
//!
//! Expressions given as arguments are evaluated and printed, otherwise expressions are read line by line,
//! with line editing and history.

use formalith::{field::real::R, try_parse};
use rustyline::{DefaultEditor, error::ReadlineError};

fn eval(input: &str) {
    match try_parse!(input, R) {
        Ok(term) => println!("{term}"),
        Err(err) => eprintln!("error: {err}"),
    }
}

fn main() -> Result<(), ReadlineError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !args.is_empty() {
        args.iter().for_each(|arg| eval(arg));
        return Ok(());
    }

    let mut editor = DefaultEditor::new()?;
    loop {
        let line = match editor.readline("> ") {
            Ok(line) => line,
            Err(ReadlineError::Eof | ReadlineError::Interrupted) => break,
            Err(err) => return Err(err),
        };
        match line.trim() {
            "" => {}
            "exit" | "quit" => break,
            input => {
                editor.add_history_entry(input)?;
                eval(input);
            }
        }
    }
    Ok(())
}
