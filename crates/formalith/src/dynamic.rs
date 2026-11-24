//! Evaluation of expressions in a set chosen at runtime, by name (`Z/7`, `R[x]`...), used by interactive sessions.

use std::{
    fmt::{self, Write},
    str::FromStr,
};

use crate::{
    context::{Context, Symbol},
    field::{
        Set, SetParseExpression, complex::C, integer::Z, matrix::M, modular::Zn, natural::N,
        real::R,
    },
    parser::environment::{Environment, Statement, head, integers_line},
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    solve::inequality::Inequality,
    term::{Term, TermSet, relation::Relation},
};

/// The sets expressions can be evaluated in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetChoice {
    /// Natural integers.
    N,
    /// Integers.
    Z,
    /// Rationals.
    R,
    /// Complex numbers.
    C,
    /// Matrices with rational coefficients.
    M,
    /// Matrices with integer coefficients.
    MZ,
    /// Matrices with coefficients modulo `n`.
    MZn(u64),
    /// Integers modulo `n`.
    Zn(u64),
    /// Polynomials in a variable, with coefficients in a set.
    Poly(Coefficients, Symbol),
}

/// The sets of coefficients of polynomials which can be evaluated in [`SetChoice::Poly`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coefficients {
    /// Rationals.
    R,
    /// Complex numbers.
    C,
    /// Integers modulo `n`.
    Zn(u64),
}

impl SetChoice {
    /// Every set which isn't parameterized.
    pub const ALL: [Self; 6] = [Self::N, Self::Z, Self::R, Self::C, Self::M, Self::MZ];

    /// The name used to select the set, like `Z/7` or `R[x]`.
    #[must_use]
    pub fn name(self) -> String {
        self.to_string()
    }

    /// A short description of the set.
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::N => "natural integers",
            Self::Z => "integers",
            Self::R => "rationals",
            Self::C => "complex numbers, `i` is the imaginary unit",
            Self::M => "matrices with rational coefficients, like [[1, 2], [3, 4]]",
            Self::MZ => "matrices with integer coefficients, with hermite and smith normal forms",
            Self::MZn(_) => "matrices with coefficients modulo n, like M(Z/6)",
            Self::Zn(_) => "integers modulo n, a field when n is prime, like Z/7",
            Self::Poly(..) => {
                "polynomials in x with coefficients in K = R, C or Z/n, like R[x] or Z/2[t]"
            }
        }
    }

    /// Parse and evaluate `input` in this set, printed as Typst math source if `typst` is set.
    ///
    /// `input` can also be a definition, like `f(x) := x^2`, or assumptions, like `assume(a > 0)`, stored in
    /// `env`, or a system of equations, like `x + y = 3, x - y = 1`, which is solved.
    ///
    /// # Errors
    /// Returns the parsing error message if `input` is not a valid expression or definition.
    ///
    /// # Panics
    /// Panics if an operation is not supported by the set.
    pub fn eval(self, input: &str, typst: bool, env: &mut Environment) -> Result<String, String> {
        self.evaluate(input, env).map(|result| {
            if typst {
                result.print(PrintOptions::typst())
            } else {
                result.to_string()
            }
        })
    }

    /// Parse and evaluate `input` in this set like [`SetChoice::eval`], to be printed later.
    ///
    /// # Errors
    /// Returns the parsing error message if `input` is not a valid expression or definition.
    ///
    /// # Panics
    /// Panics if an operation is not supported by the set.
    pub fn evaluate(self, input: &str, env: &mut Environment) -> Result<Evaluated, String> {
        match self {
            Self::N => eval_in(input, N, env),
            Self::Z => eval_in(input, Z, env),
            Self::R => eval_in(input, R, env),
            Self::C => eval_in(input, C, env),
            Self::M => eval_in(input, M, env),
            Self::MZ => eval_in(input, M::new(TermSet::new(Z)), env),
            Self::MZn(n) => eval_in(input, M::new(TermSet::new(Zn::new(n))), env),
            Self::Zn(n) => eval_in(input, Zn::new(n), env),
            Self::Poly(Coefficients::R, x) => eval_in(input, R.get_polynomial_ring(x), env),
            Self::Poly(Coefficients::C, x) => eval_in(input, C.get_polynomial_ring(x), env),
            Self::Poly(Coefficients::Zn(n), x) => {
                eval_in(input, Zn::new(n).get_polynomial_ring(x), env)
            }
        }
    }
}

/// The kind of statement an evaluated input was.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementKind {
    /// An expression.
    Expression,
    /// A definition, like `f(x) := x^2`.
    Definition,
    /// Assumptions, like `assume(a > 0)`.
    Assumption,
    /// Solved equations, inequalities or differential equations.
    Solution,
}

/// An evaluated statement, which can be printed with any [`PrintOptions`], or displayed like its result is
/// (colored if stdout supports colors).
pub struct Evaluated {
    kind: StatementKind,
    print: Box<dyn Fn(Option<PrintOptions>) -> String>,
}

impl Evaluated {
    /// An evaluated statement, see [`Environment::eval`].
    #[must_use]
    pub fn new<E: SetParseExpression>(statement: Statement<E>) -> Self {
        let kind = match statement {
            Statement::Expression(_) => StatementKind::Expression,
            Statement::Definition { .. } => StatementKind::Definition,
            Statement::Assume(_) => StatementKind::Assumption,
            Statement::System { .. }
            | Statement::Extrema { .. }
            | Statement::Inequalities { .. }
            | Statement::Ode { .. } => StatementKind::Solution,
        };
        Self {
            kind,
            print: Box::new(move |options| print_statement(&statement, options)),
        }
    }

    /// The relation `lhs op rhs`, left unsolved, like the equation of a curve.
    #[must_use]
    pub fn relation<E: SetParseExpression>(lhs: Term<E>, relation: Relation, rhs: Term<E>) -> Self {
        Self::relations(vec![(lhs, relation, rhs)])
    }

    /// The relations `lhs op rhs`, all holding, left unsolved, like the inequalities of a region.
    #[must_use]
    pub fn relations<E: SetParseExpression>(relations: Vec<(Term<E>, Relation, Term<E>)>) -> Self {
        let relations = Relations(
            relations
                .into_iter()
                .map(|(lhs, relation, rhs)| Inequality::new(lhs, relation, rhs))
                .collect(),
        );
        Self {
            kind: StatementKind::Expression,
            print: Box::new(move |options| print_with(&relations, options)),
        }
    }

    /// The point `(x, y)`.
    #[must_use]
    pub fn point<E: SetParseExpression>(x: Term<E>, y: Term<E>) -> Self {
        let point = Point(x, y);
        Self {
            kind: StatementKind::Expression,
            print: Box::new(move |options| print_with(&point, options)),
        }
    }

    /// The kind of the evaluated statement.
    #[must_use]
    pub const fn kind(&self) -> StatementKind {
        self.kind
    }

    /// Print the statement with `options`.
    #[must_use]
    pub fn print(&self, options: PrintOptions) -> String {
        (self.print)(Some(options))
    }
}

impl fmt::Display for Evaluated {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&(self.print)(None))
    }
}

impl fmt::Debug for Evaluated {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Evaluated")
            .field("kind", &self.kind)
            .field("print", &self.print(PrintOptions::plain()))
            .finish()
    }
}

impl fmt::Display for SetChoice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::N => f.write_str("N"),
            Self::Z => f.write_str("Z"),
            Self::R => f.write_str("R"),
            Self::C => f.write_str("C"),
            Self::M => f.write_str("M"),
            Self::MZ => f.write_str("M(Z)"),
            Self::MZn(n) => write!(f, "M(Z/{n})"),
            Self::Zn(n) => write!(f, "Z/{n}"),
            Self::Poly(coefficients, x) => {
                let coefficients = match coefficients {
                    Coefficients::R => Self::R,
                    Coefficients::C => Self::C,
                    Coefficients::Zn(n) => Self::Zn(*n),
                };
                write!(f, "{coefficients}[{}]", x.name())
            }
        }
    }
}

/// Check if `name` is an identifier which can be used as a polynomial variable.
fn is_variable_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !["true", "false"].contains(&name)
}

impl FromStr for SetChoice {
    type Err = String;

    /// Parse a set name, like `R`, `Z/7` (or `Z/7Z`) or `Z/2[x]`, ignoring the case of set letters.
    fn from_str(name: &str) -> Result<Self, Self::Err> {
        let name = name.trim();
        if let Some(entries) = name
            .strip_prefix(['M', 'm'])
            .and_then(|n| n.trim_start().strip_prefix('('))
            .and_then(|n| n.strip_suffix(')'))
        {
            return match entries.parse()? {
                Self::R => Ok(Self::M),
                Self::Z => Ok(Self::MZ),
                Self::Zn(n) => Ok(Self::MZn(n)),
                entries => Err(format!(
                    "matrices with coefficients in {entries} are not supported, use R, Z or Z/n"
                )),
            };
        }
        if let Some((base, variable)) = name.strip_suffix(']').and_then(|n| n.split_once('[')) {
            let variable = variable.trim();
            let coefficients = match base.trim().parse()? {
                Self::R => Coefficients::R,
                Self::C if variable != "i" => Coefficients::C,
                Self::C => return Err("`i` is the imaginary unit of C".to_owned()),
                Self::Zn(n) => Coefficients::Zn(n),
                base => {
                    return Err(format!(
                        "polynomials with coefficients in {base} are not supported, use R, C or Z/n"
                    ));
                }
            };
            if !is_variable_name(variable) {
                return Err(format!("invalid variable `{variable}`"));
            }
            let variable = Symbol::new(variable);
            if Context::builtin_arity(variable).is_some() {
                let kind = if Context::is_builtin_constant(variable) {
                    "constant"
                } else {
                    "function"
                };
                return Err(format!("`{}` is a builtin {kind}", variable.name()));
            }
            return Ok(Self::Poly(coefficients, variable));
        }
        if let Some(modulus) = name
            .strip_prefix(['Z', 'z'])
            .and_then(|n| n.trim_start().strip_prefix('/'))
        {
            let modulus = modulus.trim();
            let modulus = modulus.strip_suffix(['Z', 'z']).unwrap_or(modulus).trim();
            return match modulus.parse::<u64>() {
                Ok(n) if (2..=1 << 63).contains(&n) => Ok(Self::Zn(n)),
                _ => Err(format!(
                    "invalid modulus `{modulus}`, expected an integer between 2 and 2^63"
                )),
            };
        }
        Self::ALL
            .into_iter()
            .find(|set| set.name().eq_ignore_ascii_case(name))
            .ok_or_else(|| format!("unknown set `{name}`\n{}", sets_help()))
    }
}

/// The available sets, as their name (`Z/n` for every modulus...) and description.
#[must_use]
pub fn sets() -> Vec<(String, &'static str)> {
    let x = Symbol::new("x");
    SetChoice::ALL
        .into_iter()
        .map(|set| (set.name(), set))
        .chain([
            ("Z/n".to_owned(), SetChoice::Zn(2)),
            ("M(Z/n)".to_owned(), SetChoice::MZn(2)),
            ("K[x]".to_owned(), SetChoice::Poly(Coefficients::R, x)),
        ])
        .map(|(name, set)| (name, set.description()))
        .collect()
}

/// List the available sets with their description.
#[must_use]
pub fn sets_help() -> String {
    let mut help = String::from("available sets:");
    for (name, description) in sets() {
        let _ = write!(help, "\n  {name:<6} {description}");
    }
    help
}

fn eval_in<E: SetParseExpression>(
    input: &str,
    set: E,
    env: &mut Environment,
) -> Result<Evaluated, String> {
    let statement = env.eval(input, set).map_err(|err| err.to_string())?;
    Ok(Evaluated::new(statement))
}

/// Print `value` with `options`, or with its `Display` implementation.
fn print_with<P: PrettyPrint + fmt::Display>(value: &P, options: Option<PrintOptions>) -> String {
    options.map_or_else(
        || value.to_string(),
        |options| value.with_options(options).to_string(),
    )
}

/// A definition `name(params) := body`, the body laid out with the head when pretty printed.
struct DefinitionPrinter<'a, E: Set> {
    head: String,
    body: &'a Term<E>,
}

impl<E: Set> Print for DefinitionPrinter<'_, E> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} := ", self.head)?;
        self.body.print(options, f)
    }
}

impl<E: Set> PrettyPrint for DefinitionPrinter<'_, E> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        let mut res = PrettyPrinter::from(self.head.clone());
        res.concat(":=", true, &self.body.pretty_print(options));
        res
    }
}

impl<E: Set> fmt::Display for DefinitionPrinter<'_, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// A point `(x, y)`.
struct Point<E: Set>(Term<E>, Term<E>);

impl<E: Set> Print for Point<E> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("(")?;
        self.0.print(options, f)?;
        f.write_str(", ")?;
        self.1.print(options, f)?;
        f.write_str(")")
    }
}

impl<E: Set> PrettyPrint for Point<E> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        let mut res = self.0.pretty_print(options);
        res.concat(", ", false, &self.1.pretty_print(options));
        res.paren();
        res
    }
}

impl<E: Set> fmt::Display for Point<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// Relations separated by commas.
struct Relations<E: Set>(Vec<Inequality<E>>);

impl<E: Set> Print for Relations<E> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, relation) in self.0.iter().enumerate() {
            if i != 0 {
                f.write_str(", ")?;
            }
            relation.print(options, f)?;
        }
        Ok(())
    }
}

impl<E: Set> PrettyPrint for Relations<E> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        let mut res = PrettyPrinter::empty();
        for relation in &self.0 {
            res.concat(", ", false, &relation.pretty_print(options));
        }
        res
    }
}

impl<E: Set> fmt::Display for Relations<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// Print an evaluated statement with `options`, or with the `Display` implementations of its parts.
fn print_statement<E: SetParseExpression>(
    statement: &Statement<E>,
    options: Option<PrintOptions>,
) -> String {
    let typst = options.as_ref().is_some_and(|options| options.typst);
    let print =
        |value: &dyn Fn(PrintOptions) -> String, display: String| options.map_or(display, value);
    match statement {
        Statement::Expression(term) => print(
            &|options| term.with_options(options).to_string(),
            term.to_string(),
        ),
        Statement::Definition {
            name, params, body, ..
        } => print_with(
            &DefinitionPrinter {
                head: head(*name, params),
                body,
            },
            options,
        ),
        Statement::System {
            solution, integers, ..
        } => {
            let mut res = print(
                &|options| solution.with_options(options).to_string(),
                solution.to_string(),
            );
            if !integers.is_empty() {
                res.push_str(if typst { " \\ " } else { "\n" });
                res.push_str(&integers_line(integers, typst));
            }
            res
        }
        Statement::Extrema { extrema, integers } => {
            let mut res = print(
                &|options| extrema.with_options(options).to_string(),
                extrema.to_string(),
            );
            if !integers.is_empty() {
                res.push_str(if typst { " \\ " } else { "\n" });
                res.push_str(&integers_line(integers, typst));
            }
            res
        }
        Statement::Inequalities { solution, .. } => print(
            &|options| solution.with_options(options).to_string(),
            solution.to_string(),
        ),
        Statement::Ode { solution, .. } => print(
            &|options| solution.with_options(options).to_string(),
            solution.to_string(),
        ),
        Statement::Assume(assumptions) if assumptions.is_empty() => if typst {
            "\"no assumption\""
        } else {
            "no assumption"
        }
        .to_owned(),
        Statement::Assume(assumptions) => assumptions.describe(typst),
    }
}

/// The definitions of `env`, one per line, then its assumptions other than the defaults as an `assume` statement.
#[must_use]
pub fn definitions(env: &Environment) -> String {
    let mut lines: Vec<_> = env.definitions().map(ToString::to_string).collect();
    let assumptions = env.assumptions().difference(env.default_assumptions());
    if !assumptions.is_empty() {
        lines.push(format!("assume({assumptions})"));
    }
    lines.join("\n")
}

/// Every assumption of `env`, one symbol per line sorted by name, like `a > 0` or `n integer (default)` for a
/// default assumption, or `no assumptions`.
#[must_use]
pub fn assumptions(env: &Environment) -> String {
    let mut symbols: Vec<_> = env.assumptions().iter().collect();
    if symbols.is_empty() {
        return "no assumptions".to_owned();
    }
    symbols.sort_by_key(|(symbol, _)| symbol.name());
    let defaults = env.default_assumptions();
    let lines: Vec<String> = symbols
        .into_iter()
        .map(|(symbol, assumption)| {
            let line = assumption.describe(symbol.name(), false).join(", ");
            let is_default = defaults
                .iter()
                .any(|default| default == (symbol, assumption));
            if is_default {
                format!("{line} (default)")
            } else {
                line
            }
        })
        .collect();
    lines.join("\n")
}

/// Remove the definition and assumptions of `name` from `env`, or every definition if `name` is empty, the
/// assumptions going back to the defaults.
///
/// # Errors
/// Returns an error message if `name` is neither defined nor has assumptions.
pub fn clear_definitions(env: &mut Environment, name: &str) -> Result<(), String> {
    if name.is_empty() {
        env.clear();
        Ok(())
    } else if env.remove(name) | env.remove_assumptions(name) {
        Ok(())
    } else {
        Err(format!("`{name}` is not defined"))
    }
}
