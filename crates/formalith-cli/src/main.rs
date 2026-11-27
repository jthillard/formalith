//! A minimal command line interface evaluating expressions in a chosen set (the reals by default).
//!
//! Expressions given as arguments are evaluated and printed, otherwise expressions are read line by line,
//! with line editing and history. The set is chosen with `--set <name>` on the command line, or `:set <name>`
//! in the interactive mode. Typst math output is enabled with `--typst`, or toggled with `:typst`. The other
//! commands are those of [`Session::run`], listed by `help`. Tab completes builtins, definitions, commands and
//! sets (see [`Session::complete`]).

use std::process::ExitCode;

use formalith_session::{Output, Session, formalith::printer::PrintOptions, sets_help};
use rustyline::{
    CompletionType, Config, Context, Editor, Helper, completion::Completer, error::ReadlineError,
    highlight::Highlighter, hint::Hinter, history::DefaultHistory, validate::Validator,
};

/// The line editor helper of the interactive mode, owning its session to complete lines with it.
struct Repl {
    session: Session,
}

impl Completer for Repl {
    type Candidate = String;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _: &Context<'_>,
    ) -> rustyline::Result<(usize, Vec<String>)> {
        Ok(self.session.complete(line, pos))
    }
}

impl Hinter for Repl {
    type Hint = String;
}

impl Highlighter for Repl {}

impl Validator for Repl {}

impl Helper for Repl {}

/// Run a line in `session` and print the answer, results being cut at the width of the terminal (when stdout is
/// one) rather than wrapped by it, which would mix the rows of their 2D layout.
fn run(session: &mut Session, line: &str) {
    match session.run(line).output {
        Output::None => {}
        Output::Error(err) => eprintln!("error: {err}"),
        Output::Result {
            result,
            typst: false,
        } => {
            let width = terminal_size::terminal_size_of(std::io::stdout())
                .map(|(width, _)| usize::from(width.0));
            println!(
                "{}",
                result.print(PrintOptions::default().with_width(width))
            );
        }
        output => println!("{output}"),
    }
}

fn main() -> Result<ExitCode, ReadlineError> {
    let mut args = std::env::args().skip(1).peekable();
    let mut session = Session::new();
    while let Some(flag) =
        args.next_if(|arg| ["--set", "-s", "--typst", "-t"].contains(&arg.as_str()))
    {
        if flag == "--typst" || flag == "-t" {
            session.set_typst(true);
            continue;
        }
        match args.next().as_deref().map(str::parse) {
            Some(Ok(set)) => session.set_set(set),
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
        args.iter().for_each(|arg| run(&mut session, arg));
        return Ok(ExitCode::SUCCESS);
    }

    let config = Config::builder()
        .completion_type(CompletionType::List)
        .build();
    let mut editor: Editor<Repl, DefaultHistory> = Editor::with_config(config)?;
    editor.set_helper(Some(Repl { session }));
    loop {
        let prompt = editor
            .helper()
            .map(|repl| format!("{}> ", repl.session.set()))
            .unwrap_or_default();
        let line = match editor.readline(&prompt) {
            Ok(line) => line,
            Err(ReadlineError::Eof | ReadlineError::Interrupted) => break,
            Err(err) => return Err(err),
        };
        match line.trim() {
            "" => {}
            "exit" | "quit" => break,
            input => {
                editor.add_history_entry(input)?;
                if let Some(repl) = editor.helper_mut() {
                    run(&mut repl.session, input);
                }
                if matches!(input, "help" | ":help") {
                    println!("Tab completes names, exit or quit (also Ctrl+D) leaves");
                }
            }
        }
    }
    Ok(ExitCode::SUCCESS)
}
