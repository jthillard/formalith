//! Interactive Formalith sessions, shared by the command line and web interfaces: the current set, definitions,
//! assumptions and output options, with the `:` commands changing them.
//!
//! ```
//! use formalith_session::{Output, Session};
//!
//! let mut session = Session::new();
//! session.run("f(x) := x^2");
//! assert_eq!(session.run("f(3)").output.to_string(), "9");
//! session.run(":set Z/7");
//! assert_eq!(session.run("3*5").output.to_string(), "1");
//! assert!(matches!(session.run("1 +").output, Output::Error(_)));
//! ```

#![warn(
    rustdoc::all,
    missing_docs,
    clippy::cargo,
    clippy::pedantic,
    clippy::nursery
)]

/// A profiling scope named `$name`, optionally with dynamic `$data`, lasting until the end of the enclosing block.
/// Nothing without the feature `profile`.
macro_rules! profile_scope {
    ($name:expr $(, $data:expr)?) => {
        #[cfg(feature = "profile")]
        profiling::scope!($name $(, $data)?);
    };
}

pub mod graph;

use std::{
    fmt::{self, Write},
    panic::{self, AssertUnwindSafe},
};

pub use formalith;
pub use formalith::dynamic::{Coefficients, SetChoice, sets_help};
pub use formalith::parser::environment::Environment;
use formalith::{
    context::{
        Context,
        assumptions::Assumptions,
        docs::{self, BUILTIN_DOCS, Category},
    },
    dynamic::{self, Evaluated, StatementKind},
    parser::{ParserError, syntax::input_typst},
    printer::PrintOptions,
};
use graph::Graph;

/// The commands of a session, with their description.
pub const COMMANDS: [(&str, &str); 9] = [
    (":defs", "list definitions and assumptions made"),
    (":assumptions", "list every assumption, defaults included"),
    (
        ":clear [name]",
        "remove a definition or assumptions, or reset all",
    ),
    (":set", "show the current set"),
    (":set <name>", "evaluate in another set"),
    (":typst", "toggle Typst math output"),
    ("help", "show this help"),
    ("help builtins", "list the builtin functions"),
    ("help <name>", "show the documentation of a builtin"),
];

/// An interactive session: inputs are evaluated in the current set, with the definitions and assumptions made
/// before.
#[derive(Debug)]
pub struct Session {
    set: SetChoice,
    env: Environment,
    typst: bool,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    /// A session in `R`, without definitions, with the default assumptions (`k`, `m`, `n` integers), printing on
    /// one line.
    #[must_use]
    pub fn new() -> Self {
        Self {
            set: SetChoice::R,
            env: Environment::with_default_assumptions(Assumptions::defaults()),
            typst: false,
        }
    }

    /// The set inputs are evaluated in.
    #[must_use]
    pub const fn set(&self) -> SetChoice {
        self.set
    }

    /// Evaluate the next inputs in `set`.
    pub const fn set_set(&mut self, set: SetChoice) {
        self.set = set;
    }

    /// Check if results should be printed as Typst math source.
    #[must_use]
    pub const fn typst(&self) -> bool {
        self.typst
    }

    /// Print results as Typst math source if `typst` is set.
    pub const fn set_typst(&mut self, typst: bool) {
        self.typst = typst;
    }

    /// The input `line` as Typst math source, as it was typed, to show it typeset before its result: `None` unless
    /// results are printed as Typst and `line` is an input to evaluate (not a command) which parses, see
    /// [`input_typst`]. Nothing is evaluated.
    #[must_use]
    pub fn typeset_input(&self, line: &str) -> Option<String> {
        let line = line.trim();
        if !self.typst
            || line.is_empty()
            || line.starts_with(':')
            || command_argument(line, "help").is_some()
        {
            return None;
        }
        input_typst(line)
    }

    /// The definitions and assumptions of the session.
    #[must_use]
    pub const fn environment(&self) -> &Environment {
        &self.env
    }

    /// The completions of the word ending at byte `pos` of `line`, for Tab completion: the byte where the word
    /// starts and the candidates replacing it, sorted. Words of expressions complete to builtins and definitions
    /// (functions with an opening parenthesis, unless one follows), the first word to commands, and the argument
    /// of `:set`, `help` or `:clear` to sets, builtins or definitions.
    ///
    /// ```
    /// use formalith_session::Session;
    ///
    /// let session = Session::new();
    /// assert_eq!(session.complete("1 + integ", 9), (4, vec!["integrate(".to_owned()]));
    /// assert_eq!(session.complete(":se", 3), (0, vec![":set".to_owned()]));
    /// ```
    #[must_use]
    pub fn complete(&self, line: &str, pos: usize) -> (usize, Vec<String>) {
        let mut pos = pos.min(line.len());
        while !line.is_char_boundary(pos) {
            pos -= 1;
        }
        let before = &line[..pos];
        let indent = before.len() - before.trim_start().len();
        let typed = &before[indent..];
        let mut candidates: Vec<String> = if let Some((command, argument)) = typed
            .split_once(char::is_whitespace)
            .filter(|(command, _)| command.starts_with(':') || *command == "help")
        {
            let names: Vec<String> = match command {
                ":set" => dynamic::sets().into_iter().map(|(name, _)| name).collect(),
                "help" | ":help" => BUILTIN_DOCS
                    .iter()
                    .map(|doc| doc.name().to_owned())
                    .chain(["builtins".to_owned()])
                    .collect(),
                ":clear" => self
                    .env
                    .definitions()
                    .map(|definition| definition.name().name().to_owned())
                    .collect(),
                _ => Vec::new(),
            };
            let argument = argument.trim_start();
            let start = pos - argument.len();
            let mut candidates: Vec<String> = names
                .into_iter()
                .filter(|name| {
                    name.get(..argument.len())
                        .is_some_and(|prefix| prefix.eq_ignore_ascii_case(argument))
                })
                .collect();
            candidates.sort();
            candidates.dedup();
            return (start, candidates);
        } else if typed.starts_with(':') || (!typed.is_empty() && "help".starts_with(typed)) {
            return (
                indent,
                COMMANDS
                    .iter()
                    .filter_map(|(command, _)| command.split_whitespace().next())
                    .filter(|command| command.starts_with(typed))
                    .fold(Vec::new(), |mut commands, command| {
                        if !commands.iter().any(|known| known == command) {
                            commands.push(command.to_owned());
                        }
                        commands
                    }),
            );
        } else {
            Vec::new()
        };
        let start = before
            .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .map_or(0, |i| i + 1);
        let word = &before[start..];
        if !word.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
            return (start, Vec::new());
        }
        let paren = if line[pos..].starts_with('(') {
            ""
        } else {
            "("
        };
        let builtins = BUILTIN_DOCS.iter().map(|doc| {
            let function = !Context::is_builtin_constant(doc.symbol);
            (doc.name(), function)
        });
        let definitions = self
            .env
            .definitions()
            .map(|definition| (definition.name().name(), !definition.params().is_empty()));
        candidates.extend(
            builtins
                .chain(definitions)
                .filter(|(name, _)| name.starts_with(word))
                .map(|(name, function)| {
                    if function {
                        format!("{name}{paren}")
                    } else {
                        name.to_owned()
                    }
                }),
        );
        candidates.sort();
        candidates.dedup();
        (start, candidates)
    }

    /// The help of a session: inputs and commands.
    #[must_use]
    pub fn help() -> String {
        let mut help = String::from(
            "Enter an expression to evaluate it, like `expand((x+1)^3)` or `factor(x^2-1)`.\n\
             Define variables and functions with `a := x^2` or `f(x, y) := x*y`.\n\
             Solve systems with `x + y = 3, x*y = 2` (one solution per line), or `solve(a*x^2 = 1, x)` for chosen \
             unknowns.\n\
             Declare assumptions with `assume(a > 0, b != 0, c > d + 1, n integer)`, like `sqrt(a^2) = a`. `k`, `m` and `n` \
             are integers by default (`:clear n` drops it).\n\
             commands:",
        );
        for (command, description) in COMMANDS {
            let _ = write!(help, "\n  {command:<13} {description}");
        }
        help.push('\n');
        help.push_str(&sets_help());
        help
    }

    /// Run a line: a command like `:set Z/7`, or an input evaluated in the current set.
    ///
    /// Operations unsupported by the set panic. The panic is caught (unless panics abort, as in wasm) and
    /// reported as an error.
    pub fn run(&mut self, line: &str) -> Response {
        profile_scope!("Session::run");
        let line = line.trim();
        let (output, changes_state) = match line {
            "" => (Output::None, false),
            ":typst" => {
                self.typst = !self.typst;
                let state = if self.typst { "enabled" } else { "disabled" };
                (Output::Message(format!("typst output {state}")), true)
            }
            "help" | ":help" => (Output::Message(Self::help()), false),
            "help builtins" | ":help builtins" => (Output::Message(builtins_help()), false),
            ":defs" => {
                let definitions = dynamic::definitions(&self.env);
                let definitions = if definitions.is_empty() {
                    "no definitions".to_owned()
                } else {
                    definitions
                };
                (Output::Message(definitions), false)
            }
            ":assumptions" => (Output::Message(dynamic::assumptions(&self.env)), false),
            _ => {
                if let Some(name) =
                    command_argument(line, "help").or_else(|| command_argument(line, ":help"))
                {
                    let output = builtin_help(name).map_or_else(
                        || Output::Error(format!("unknown builtin `{name}`, see `help builtins`")),
                        Output::Message,
                    );
                    (output, false)
                } else if let Some(name) = command_argument(line, ":set") {
                    self.set_command(name)
                } else if let Some(name) = command_argument(line, ":clear") {
                    match dynamic::clear_definitions(&mut self.env, name) {
                        Ok(()) => (Output::None, true),
                        Err(err) => (Output::Error(err), false),
                    }
                } else if line.starts_with(':') {
                    let command = line.split_whitespace().next().unwrap_or(line);
                    (
                        Output::Error(format!("unknown command `{command}`, see `help`")),
                        false,
                    )
                } else {
                    self.evaluate(line)
                }
            }
        };
        Response {
            output,
            replay: changes_state,
        }
    }

    /// The `:set` command, showing the current set or changing it to `name`.
    fn set_command(&mut self, name: &str) -> (Output, bool) {
        if name.is_empty() {
            return (
                Output::Message(format!("current set: {}\n{}", self.set, sets_help())),
                false,
            );
        }
        match name.parse() {
            Ok(set) => {
                self.set = set;
                (Output::None, true)
            }
            Err(err) => (Output::Error(err), false),
        }
    }

    /// Run a line like [`Session::run`], with its graph when the set is `R` or `C`, see [`graph`].
    ///
    /// Relations in `y`, like `y = x^2` or `x^2 + y^2 < 1`, and points `(a, b)` are kept as they are rather than
    /// solved.
    pub fn graph(&mut self, line: &str) -> (Response, Option<Graph>) {
        profile_scope!("Session::graph");
        let line = line.trim();
        let evaluate = match self.set {
            SetChoice::R => graph::evaluate,
            SetChoice::C => graph::evaluate_complex,
            _ => return (self.run(line), None),
        };
        if line.is_empty() || line.starts_with(':') || line == "help" {
            return (self.run(line), None);
        }
        let env = &mut self.env;
        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            evaluate(line, env).map_err(|err| err.or_hint(SetChoice::R.hint(line)))
        }));
        let (output, changes_state, graph) = self.respond(line, result);
        let response = Response {
            output,
            replay: changes_state,
        };
        (response, graph.flatten())
    }

    /// Evaluate `input` in the current set, catching panics.
    fn evaluate(&mut self, input: &str) -> (Output, bool) {
        let set = self.set;
        let env = &mut self.env;
        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            set.try_evaluate(input, env).map(|result| (result, ()))
        }));
        let (output, changes_state, _) = self.respond(input, result);
        (output, changes_state)
    }

    /// The output of an evaluation, whether it changed the state of the session, and its extra result.
    fn respond<T>(
        &self,
        input: &str,
        result: std::thread::Result<Result<(Evaluated, T), ParserError>>,
    ) -> (Output, bool, Option<T>) {
        match result {
            Ok(Ok((result, extra))) => {
                let changes_state = matches!(
                    result.kind(),
                    StatementKind::Definition | StatementKind::Assumption
                );
                let output = Output::Result {
                    result,
                    typst: self.typst,
                };
                (output, changes_state, Some(extra))
            }
            Ok(Err(err)) => (Output::Error(error_report(input, &err)), false, None),
            Err(_) => (
                Output::Error(format!("this operation is not supported in {}", self.set)),
                false,
                None,
            ),
        }
    }
}

/// The message of `error` about `input`, with the part of `input` it is about underlined, and its hint:
///
/// ```text
/// unexpected `$`
///   2 $ 3
///     ^
/// ```
fn error_report(input: &str, error: &ParserError) -> String {
    let mut report = error.message().to_owned();
    if let Some(span) = error.span()
        && span.end <= input.len()
        && input.is_char_boundary(span.start)
        && input.is_char_boundary(span.end)
    {
        let column = input[..span.start].chars().count();
        let width = input[span].chars().count().max(1);
        let _ = write!(
            report,
            "\n  {input}\n  {}^{}",
            " ".repeat(column),
            "~".repeat(width - 1)
        );
    }
    if let Some(hint) = error.hint() {
        let _ = write!(report, "\nhint: {hint}");
    }
    report
}

/// The argument of `command` in `line`, if `line` is this command.
/// The list of builtins by category, with their summary.
fn builtins_help() -> String {
    let mut help = String::from("builtins (`help <name>` for details):");
    for category in Category::ALL {
        let _ = write!(help, "\n{}:", category.title());
        for doc in category.builtins() {
            let _ = write!(help, "\n  {:<13} {}", doc.name(), doc.summary);
        }
    }
    help
}

/// The documentation of the builtin `name`: signature, description and examples.
fn builtin_help(name: &str) -> Option<String> {
    let doc = docs::find(name)?;
    let mut help = format!("{}\n  {}", doc.signature, doc.summary);
    if !doc.details.is_empty() {
        help.push('\n');
        help.push_str(&wrap(doc.details, 2, 100));
    }
    help.push_str("\nexamples:");
    for example in doc.examples {
        let set = if example.set == "R" {
            String::new()
        } else {
            format!(" (in {})", example.set)
        };
        let _ = write!(help, "\n  {} → {}{set}", example.input, example.result);
    }
    Some(help)
}

/// `text` cut into lines of at most `width` characters (unless a word is longer), indented by `indent` spaces.
fn wrap(text: &str, indent: usize, width: usize) -> String {
    let mut lines = vec![String::new()];
    for word in text.split_whitespace() {
        let line = lines.last_mut().unwrap();
        if !line.is_empty() && indent + line.chars().count() + 1 + word.chars().count() > width {
            lines.push(word.to_owned());
        } else {
            if !line.is_empty() {
                line.push(' ');
            }
            line.push_str(word);
        }
    }
    lines
        .iter()
        .map(|line| format!("{:indent$}{line}", ""))
        .collect::<Vec<_>>()
        .join("\n")
}

fn command_argument<'a>(line: &'a str, command: &str) -> Option<&'a str> {
    let argument = line.strip_prefix(command)?;
    (argument.is_empty() || argument.starts_with(char::is_whitespace)).then(|| argument.trim())
}

/// The answer of a session to a line.
#[derive(Debug)]
pub struct Response {
    /// What to show.
    pub output: Output,
    /// Whether the line changed the state of the session (a definition, an assumption, a command changing the
    /// set...). Running these lines again in a new session restores the state, like after a panic in wasm.
    pub replay: bool,
}

/// What a session shows in answer to a line.
#[derive(Debug)]
pub enum Output {
    /// Nothing, like after a set change.
    None,
    /// The result of an evaluation.
    Result {
        /// The evaluated statement.
        result: Evaluated,
        /// Whether the session prints results as Typst math source.
        typst: bool,
    },
    /// Information, like the list of definitions.
    Message(String),
    /// An error message.
    Error(String),
}

impl Output {
    /// Print with `options` if it is a result, otherwise print the message.
    #[must_use]
    pub fn print(&self, options: PrintOptions) -> String {
        profile_scope!("print");
        match self {
            Self::None => String::new(),
            Self::Result { result, .. } => result.print(options),
            Self::Message(message) | Self::Error(message) => message.clone(),
        }
    }
}

impl fmt::Display for Output {
    /// Display results (colored if stdout supports colors), or print them as Typst math source if the session
    /// prints Typst.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Result {
                result,
                typst: true,
            } => f.write_str(&result.print(PrintOptions::typst())),
            Self::Result { result, .. } => write!(f, "{result}"),
            _ => f.write_str(&self.print(PrintOptions::plain())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn panics_are_errors() {
        let session = Session::new();
        let panic: std::thread::Result<Result<(Evaluated, ()), ParserError>> = Err(Box::new(()));
        let (output, changes_state, extra) = session.respond("", panic);
        assert!(matches!(output, Output::Error(_)));
        assert!(!changes_state);
        assert!(extra.is_none());
    }

    fn completions(session: &Session, line: &str) -> (usize, Vec<String>) {
        session.complete(line, line.len())
    }

    #[test]
    fn completes_builtins_and_definitions() {
        let mut session = Session::new();
        assert_eq!(
            completions(&session, "inte"),
            (0, vec!["integrate(".to_owned()])
        );
        let (start, candidates) = completions(&session, "sin(co");
        assert_eq!(start, 4);
        assert!(candidates.contains(&"cos(".to_owned()));
        let (_, candidates) = completions(&session, "p");
        assert!(candidates.contains(&"pi".to_owned()));
        assert!(candidates.contains(&"piecewise(".to_owned()));
        assert_eq!(completions(&session, "2x"), (0, Vec::new()));
        assert_eq!(completions(&session, "1 + "), (4, Vec::new()));
        assert_eq!(
            session.complete("integ(x)", 5),
            (0, vec!["integrate".to_owned()])
        );
        session.run("f(x) := x^2");
        session.run("a := 3");
        let (_, candidates) = completions(&session, "f");
        assert!(candidates.contains(&"f(".to_owned()));
        assert!(candidates.contains(&"factor(".to_owned()));
        let (_, candidates) = completions(&session, "a");
        assert!(candidates.contains(&"a".to_owned()));
        assert_eq!(
            completions(&session, ":clear "),
            (7, vec!["a".to_owned(), "f".to_owned()])
        );
    }

    #[test]
    fn completes_commands() {
        let session = Session::new();
        assert_eq!(completions(&session, ":se"), (0, vec![":set".to_owned()]));
        assert_eq!(completions(&session, "  hel"), (2, vec!["help".to_owned()]));
        assert_eq!(
            completions(&session, ":set z"),
            (5, vec!["Z".to_owned(), "Z/n".to_owned()])
        );
        assert_eq!(
            completions(&session, "help integ"),
            (5, vec!["integrate".to_owned()])
        );
        assert_eq!(
            completions(&session, "help bui"),
            (5, vec!["builtins".to_owned()])
        );
    }
}
