//! A minimal command line interface evaluating expressions in a chosen set (the reals by default).
//!
//! Expressions given as arguments are evaluated and printed, otherwise expressions are read line by line,
//! with line editing and history. The set is chosen with `--set <name>` on the command line, or `:set <name>`
//! in the interactive mode. Typst math output is enabled with `--typst`, or toggled with `:typst`.
//!
//! Variables and functions are defined with `a := x^2` or `f(x, y) := x*y`, listed with `:defs` and removed with
//! `:clear <name>`, or `:clear` for all of them. Linear systems are solved with `x + y = 3, x - y = 1`.

use std::{
    panic::{self, AssertUnwindSafe},
    process::ExitCode,
};

use formalith::{
    parser::environment::Environment,
    repl::{SetChoice, sets_help},
};
use rustyline::{DefaultEditor, error::ReadlineError};

/// Evaluate and print an expression. Operations unsupported by the set panic, so panics are caught to keep the
/// interface running.
fn eval(input: &str, set: SetChoice, typst: bool, env: &mut Environment) {
    match panic::catch_unwind(AssertUnwindSafe(|| set.eval(input, typst, env))) {
        Ok(Ok(term)) => println!("{term}"),
        Ok(Err(err)) => eprintln!("error: {err}"),
        Err(_) => eprintln!("error: this operation is not supported in {}", set.name()),
    }
}

fn main() -> Result<ExitCode, ReadlineError> {
    let mut args = std::env::args().skip(1).peekable();
    let mut set = SetChoice::R;
    let mut typst = false;
    while let Some(flag) =
        args.next_if(|arg| ["--set", "-s", "--typst", "-t"].contains(&arg.as_str()))
    {
        if flag == "--typst" || flag == "-t" {
            typst = true;
            continue;
        }
        match args.next().as_deref().map(str::parse) {
            Some(Ok(choice)) => set = choice,
            Some(Err(err)) => {
                eprintln!("error: {err}");
                return Ok(ExitCode::FAILURE);
            }
            None => {
                eprintln!("error: missing set after `{flag}`\n{}", sets_help());
                return Ok(ExitCode::FAILURE);
            }
        }
    }
    let mut env = Environment::new();
    let args: Vec<String> = args.collect();
    if !args.is_empty() {
        args.iter().for_each(|arg| eval(arg, set, typst, &mut env));
        return Ok(ExitCode::SUCCESS);
    }

    let mut editor = DefaultEditor::new()?;
    loop {
        let line = match editor.readline(&format!("{}> ", set.name())) {
            Ok(line) => line,
            Err(ReadlineError::Eof | ReadlineError::Interrupted) => break,
            Err(err) => return Err(err),
        };
        match line.trim() {
            "" => {}
            "exit" | "quit" => break,
            input => {
                editor.add_history_entry(input)?;
                if input == ":typst" {
                    typst = !typst;
                    println!(
                        "typst output {}",
                        if typst { "enabled" } else { "disabled" }
                    );
                } else if let Some(name) = input.strip_prefix(":set") {
                    match name.trim() {
                        "" => println!("current set: {}\n{}", set.name(), sets_help()),
                        name => match name.parse() {
                            Ok(choice) => set = choice,
                            Err(err) => eprintln!("error: {err}"),
                        },
                    }
                } else if input == ":defs" {
                    env.definitions()
                        .for_each(|definition| println!("{definition}"));
                } else if let Some(name) = input.strip_prefix(":clear") {
                    match name.trim() {
                        "" => env.clear(),
                        name if env.remove(name) => {}
                        name => eprintln!("error: `{name}` is not defined"),
                    }
                } else {
                    eval(input, set, typst, &mut env);
                }
            }
        }
    }
    Ok(ExitCode::SUCCESS)
}
