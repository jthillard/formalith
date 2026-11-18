//! A minimal command line interface evaluating expressions in a chosen set (the reals by default).
//!
//! Expressions given as arguments are evaluated and printed, otherwise expressions are read line by line,
//! with line editing and history. The set is chosen with `--set <name>` on the command line, or `:set <name>`
//! in the interactive mode. Typst math output is enabled with `--typst`, or toggled with `:typst`.

use std::{panic, process::ExitCode, str::FromStr};

use formalith::{
    field::{Set, complex::C, integer::Z, matrix::M, natural::N, real::R},
    printer::{Print, PrintOptions},
    try_parse,
};
use rustyline::{DefaultEditor, error::ReadlineError};

/// The sets expressions can be evaluated in.
#[derive(Clone, Copy)]
enum SetChoice {
    N,
    Z,
    R,
    C,
    M,
}

impl SetChoice {
    const ALL: [Self; 5] = [Self::N, Self::Z, Self::R, Self::C, Self::M];

    const fn name(self) -> &'static str {
        match self {
            Self::N => "N",
            Self::Z => "Z",
            Self::R => "R",
            Self::C => "C",
            Self::M => "M",
        }
    }

    const fn description(self) -> &'static str {
        match self {
            Self::N => "natural integers",
            Self::Z => "integers",
            Self::R => "rationals",
            Self::C => "complex numbers, `i` is the imaginary unit",
            Self::M => "matrices with rational coefficients, like [[1, 2], [3, 4]]",
        }
    }

    fn eval(self, input: &str, typst: bool) -> Result<String, String> {
        match self {
            Self::N => eval_in(input, N, typst),
            Self::Z => eval_in(input, Z, typst),
            Self::R => eval_in(input, R, typst),
            Self::C => eval_in(input, C, typst),
            Self::M => eval_in(input, M, typst),
        }
    }
}

impl FromStr for SetChoice {
    type Err = String;

    fn from_str(name: &str) -> Result<Self, Self::Err> {
        Self::ALL
            .into_iter()
            .find(|set| set.name().eq_ignore_ascii_case(name))
            .ok_or_else(|| format!("unknown set `{name}`\n{}", sets_help()))
    }
}

fn sets_help() -> String {
    let mut help = String::from("available sets:");
    for set in SetChoice::ALL {
        help.push_str(&format!("\n  {}  {}", set.name(), set.description()));
    }
    help
}

fn eval_in<E: Set>(input: &str, set: E, typst: bool) -> Result<String, String> {
    try_parse!(input, set)
        .map(|term| {
            if typst {
                term.with_options(PrintOptions::typst()).to_string()
            } else {
                term.to_string()
            }
        })
        .map_err(|err| err.to_string())
}

/// Evaluate and print an expression. Operations unsupported by the set panic, so panics are caught to keep the
/// interface running.
fn eval(input: &str, set: SetChoice, typst: bool) {
    match panic::catch_unwind(|| set.eval(input, typst)) {
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
    let args: Vec<String> = args.collect();
    if !args.is_empty() {
        args.iter().for_each(|arg| eval(arg, set, typst));
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
                } else {
                    eval(input, set, typst);
                }
            }
        }
    }
    Ok(ExitCode::SUCCESS)
}
