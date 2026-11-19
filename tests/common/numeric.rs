//! Numerical evaluation of results through the REPL, and numerical equivalence of two expressions.
//!
//! Everything works on the printed (one line, plain) form of results: an expression is turned into a function by
//! a definition `chk_f(x, y) := ...`, then evaluated with `approx(chk_f(3/7, -2/5), 30)` and read back as a float.
//! An output that isn't a plain number (`undefined`, `oo`, `ln(-2.0)`, a leftover symbol, an error or a panic)
//! makes the point invalid, so it is skipped.
use formalith::{
    context::{Symbol, assumptions::SignSet},
    field::{
        Set, SetParseExpression, complex::C, integer::Z, matrix::M, modular::Zn, natural::N,
        real::R,
    },
    parser::environment::{Environment, Statement, integers_line},
    printer::{Print, PrintOptions},
    repl::{Coefficients, SetChoice},
    term::TermSet,
};

use super::{guard::no_panic, rng::Rng};

/// Digits used by `approx` in checks.
pub const DIGITS: usize = 30;
/// Name of the definitions made by checks.
const FUNCTION: &str = "chk_f";

/// Evaluate `input` in `R` with `env`, printed plainly on one line (solutions one per line).
pub fn eval(env: &mut Environment, input: &str) -> Result<String, String> {
    eval_in(SetChoice::R, env, input)
}

/// Evaluate `input` in `set` with `env`, printed plainly like [`eval`].
pub fn eval_in(set: SetChoice, env: &mut Environment, input: &str) -> Result<String, String> {
    match set {
        SetChoice::N => eval_plain(input, N, env),
        SetChoice::Z => eval_plain(input, Z, env),
        SetChoice::R => eval_plain(input, R, env),
        SetChoice::C => eval_plain(input, C, env),
        SetChoice::M => eval_plain(input, M, env),
        SetChoice::MZ => eval_plain(input, M::new(TermSet::new(Z)), env),
        SetChoice::MZn(n) => eval_plain(input, M::new(TermSet::new(Zn::new(n))), env),
        SetChoice::Zn(n) => eval_plain(input, Zn::new(n), env),
        SetChoice::Poly(Coefficients::R, x) => eval_plain(input, R.get_polynomial_ring(x), env),
        SetChoice::Poly(Coefficients::C, x) => eval_plain(input, C.get_polynomial_ring(x), env),
        SetChoice::Poly(Coefficients::Zn(n), x) => {
            eval_plain(input, Zn::new(n).get_polynomial_ring(x), env)
        }
    }
}

/// Evaluate `input` in `set`, printing every kind of statement on plain lines.
fn eval_plain<E: SetParseExpression>(
    input: &str,
    set: E,
    env: &mut Environment,
) -> Result<String, String> {
    let plain = PrintOptions::plain();
    Ok(match env.eval(input, set).map_err(|err| err.to_string())? {
        Statement::Expression(term) => term.with_options(plain).to_string(),
        Statement::Definition { body, .. } => format!(":= {}", body.with_options(plain)),
        Statement::System {
            solution, integers, ..
        } => {
            let mut res = solution.with_options(plain).to_string();
            if !integers.is_empty() {
                res.push('\n');
                res.push_str(&integers_line(&integers, false));
            }
            res
        }
        Statement::Inequalities { solution, .. } => solution.with_options(plain).to_string(),
        Statement::Ode { solution, .. } => solution.with_options(plain).to_string(),
        Statement::Assume(assumptions) => assumptions.describe(false),
    })
}

/// An environment where `statements` (definitions, assumptions) were evaluated in `R`.
pub fn env_with(statements: &[&str]) -> Environment {
    let mut env = Environment::new();
    for statement in statements {
        eval(&mut env, statement).unwrap_or_else(|e| panic!("setup `{statement}` failed: {e}"));
    }
    env
}

/// Read an `approx` output as a finite float.
///
/// Note: arguments given as approximations (`approx(1/10^3, 80)`) only get about 15 digits through builtins, so
/// checks evaluate at exact points.
pub fn parse_number(output: &str) -> Option<f64> {
    let value: f64 = output.trim().parse().ok()?;
    value.is_finite().then_some(value)
}

/// The value of the constant expression `expr`, by `approx`.
pub fn number(env: &Environment, expr: &str) -> Option<f64> {
    let mut env = env.clone();
    no_panic(|| eval(&mut env, &format!("approx({expr}, {DIGITS})")))?
        .ok()
        .and_then(|s| parse_number(&s))
}

/// An expression made a function of some of its symbols, to evaluate it at points.
pub struct Function {
    env: Environment,
    arity: usize,
    name: String,
    /// The expression.
    pub expr: String,
}

/// Counter making the names of [`Function`]s unique, so that several can live in one environment.
static NEXT_FUNCTION: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

impl Function {
    /// Make `expr` a function of `params` (in this order), or the definition error.
    pub fn new(env: &Environment, expr: &str, params: &[&str]) -> Result<Self, String> {
        Self::new_in(&mut env.clone(), expr, params)
    }

    /// Like [`Self::new`], also adding the definition to `env`, so that functions defined after it in `env` can
    /// be combined with it in [`Self::number_of`].
    pub fn new_in(env: &mut Environment, expr: &str, params: &[&str]) -> Result<Self, String> {
        let name = format!(
            "{FUNCTION}_{}",
            NEXT_FUNCTION.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        );
        if !params.is_empty() {
            let def = format!("{name}({}) := {expr}", params.join(", "));
            no_panic(|| eval(env, &def))
                .ok_or_else(|| format!("panic in `{def}`"))?
                .map_err(|e| format!("`{def}`: {e}"))?;
        }
        Ok(Self {
            env: env.clone(),
            arity: params.len(),
            name,
            expr: expr.to_owned(),
        })
    }

    /// The call of this function on `args` (expressions), to embed in a bigger expression.
    pub fn call(&self, args: &[String]) -> String {
        assert_eq!(args.len(), self.arity);
        if self.arity == 0 {
            format!("({})", self.expr)
        } else {
            let args: Vec<_> = args.iter().map(|a| format!("({a})")).collect();
            format!("{}({})", self.name, args.join(", "))
        }
    }

    /// The value at `args` (expressions of numbers), by `approx`.
    pub fn at(&self, args: &[String]) -> Option<f64> {
        let call = self.call(args);
        let mut env = self.env.clone();
        no_panic(|| eval(&mut env, &format!("approx({call}, {DIGITS})")))?
            .ok()
            .and_then(|s| parse_number(&s))
    }

    /// The value at `args` given as approximations with `digits` digits, so that powers like `(1 + 10^-7)^(10^7)`
    /// are computed approximately (the exact rational would be huge).
    pub fn at_approx(&self, args: &[String], digits: usize) -> Option<f64> {
        let args: Vec<_> = args
            .iter()
            .map(|a| format!("approx({a}, {digits})"))
            .collect();
        self.at(&args)
    }

    /// The value of `expr`, an expression using [`Self::call`]s, by `approx`.
    pub fn number_of(&self, expr: &str) -> Option<f64> {
        let mut env = self.env.clone();
        no_panic(|| eval(&mut env, &format!("approx({expr}, {DIGITS})")))?
            .ok()
            .and_then(|s| parse_number(&s))
    }

    /// The derivative of a function of one variable at `x0`, by a central difference with a tiny step (`approx`
    /// raises its precision for the cancellation, so this doesn't use the derivative engine).
    pub fn derivative_at(&self, x0: &str) -> Option<f64> {
        let h = "(1/10^10)";
        let plus = self.call(&[format!("{x0} + {h}")]);
        let minus = self.call(&[format!("{x0} - {h}")]);
        self.number_of(&format!("({plus} - {minus})/(2*{h})"))
    }

    /// The integral on `[a, b]` by composite 8-point Gauss-Legendre quadrature on `pieces` subintervals, or `None`
    /// if a node doesn't evaluate.
    pub fn quadrature(&self, a: f64, b: f64, pieces: usize) -> Option<f64> {
        const NODES: [(f64, f64); 4] = [
            (0.183_434_642_495_649_8, 0.362_683_783_378_362),
            (0.525_532_409_916_329, 0.313_706_645_877_887_3),
            (0.796_666_477_413_626_7, 0.222_381_034_453_374_5),
            (0.960_289_856_497_536_3, 0.101_228_536_290_376_26),
        ];
        let width = (b - a) / pieces as f64;
        let mut total = 0.0;
        for piece in 0..pieces {
            let center = a + width * (piece as f64 + 0.5);
            for (node, weight) in NODES {
                for sign in [-1.0, 1.0] {
                    let x = center + sign * node * width / 2.0;
                    total += weight * width / 2.0 * self.at(&[decimal(x)])?;
                }
            }
        }
        Some(total)
    }

    /// The exact value at `args`, printed.
    pub fn exact_at(&self, args: &[String]) -> Option<String> {
        let call = self.call(args);
        let mut env = self.env.clone();
        no_panic(|| eval(&mut env, &call))?.ok()
    }
}

/// A float as an exact rational expression with 12 decimals (enough for checks at a `1e-7` tolerance, and
/// cheaper to evaluate exactly than longer ones).
pub fn decimal(x: f64) -> String {
    let scaled = (x * 1e12).round() as i128;
    format!("{scaled}/10^12")
}

/// Where a variable is sampled.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Domain {
    /// Non-zero rationals in `[-3, 3]`.
    Any,
    /// Rationals in `(0, 4]`.
    Positive,
    /// Rationals in `[-4, 0)`.
    Negative,
    /// Integers in `lo..=hi`.
    Integer(i64, i64),
    /// Rationals in `[lo, hi]`.
    Range(f64, f64),
}

impl Domain {
    /// A random rational of the domain, as an expression.
    pub fn sample(self, rng: &mut Rng) -> String {
        let (p, q) = match self {
            Self::Integer(lo, hi) => return rng.range(lo, hi).to_string(),
            Self::Any => {
                let (p, q) = rng.rational_in(0.1, 3.0);
                if rng.chance(0.5) { (p, q) } else { (-p, q) }
            }
            Self::Positive => rng.rational_in(0.1, 4.0),
            Self::Negative => {
                let (p, q) = rng.rational_in(0.1, 4.0);
                (-p, q)
            }
            Self::Range(lo, hi) => rng.rational_in(lo, hi),
        };
        format!("{p}/{q}")
    }

    /// The domain of `name` given the assumptions of `env`.
    pub fn assumed(env: &Environment, name: &str) -> Self {
        let assumption = env.assumptions().get(Symbol::new(name));
        let sign = assumption.sign;
        let positive = sign.is_subset(SignSet::NONNEGATIVE);
        let negative = sign.is_subset(SignSet::NONPOSITIVE);
        match (assumption.integer, positive, negative) {
            (true, true, _) => Self::Integer(1, 6),
            (true, _, true) => Self::Integer(-6, -1),
            (true, _, _) => Self::Integer(-6, 6),
            (false, true, _) => Self::Positive,
            (false, _, true) => Self::Negative,
            _ => Self::Any,
        }
    }
}

/// Variables with their domains taken from the assumptions of `env`.
pub fn assumed_vars<'a>(env: &Environment, names: &[&'a str]) -> Vec<(&'a str, Domain)> {
    names
        .iter()
        .map(|&n| (n, Domain::assumed(env, n)))
        .collect()
}

/// Whether two values are equal up to the tolerance of checks.
pub fn close(a: f64, b: f64, tolerance: f64) -> bool {
    (a - b).abs() <= tolerance * 1f64.max(a.abs()).max(b.abs())
}

/// Default relative tolerance.
pub const TOLERANCE: f64 = 1e-9;
/// Points tried by [`equivalent`].
pub const POINTS: usize = 8;
/// Valid points [`equivalent`] needs to conclude.
pub const MIN_VALID: usize = 3;

/// Result of a numerical comparison.
#[derive(Debug)]
pub enum Check {
    /// Both sides agree on enough points.
    Equal,
    /// The sides differ at a point.
    Differ(String),
    /// Not enough points could be evaluated.
    Inconclusive(String),
}

impl Check {
    /// Whether the sides surely differ.
    pub const fn is_differ(&self) -> bool {
        matches!(self, Self::Differ(_))
    }
}

/// Compare `a` and `b` numerically at random points of `vars`.
pub fn equivalent(
    env: &Environment,
    a: &str,
    b: &str,
    vars: &[(&str, Domain)],
    rng: &mut Rng,
) -> Check {
    let names: Vec<_> = vars.iter().map(|(n, _)| *n).collect();
    let (fa, fb) = match (Function::new(env, a, &names), Function::new(env, b, &names)) {
        (Ok(fa), Ok(fb)) => (fa, fb),
        (Err(e), _) | (_, Err(e)) => return Check::Inconclusive(e),
    };
    let mut valid = 0;
    for _ in 0..POINTS {
        let point: Vec<_> = vars.iter().map(|(_, d)| d.sample(rng)).collect();
        let (Some(va), Some(vb)) = (fa.at(&point), fb.at(&point)) else {
            continue;
        };
        if !close(va, vb, TOLERANCE) {
            let at: Vec<_> = names
                .iter()
                .zip(&point)
                .map(|(n, v)| format!("{n} = {v}"))
                .collect();
            return Check::Differ(format!(
                "`{a}` = {va} but `{b}` = {vb} at {}",
                at.join(", ")
            ));
        }
        valid += 1;
        if valid >= MIN_VALID + 2 {
            break;
        }
    }
    if valid >= MIN_VALID {
        Check::Equal
    } else {
        Check::Inconclusive(format!("only {valid} valid points for `{a}` vs `{b}`"))
    }
}

/// Whether `output` is exactly zero, or a zero matrix.
pub fn is_zero(output: &str) -> bool {
    output
        .chars()
        .filter(|c| !matches!(c, '[' | ']' | ',' | ' '))
        .all(|c| c == '0')
        && output.contains('0')
}

/// Split `s` at `separator` outside of parentheses and brackets.
pub fn split_top(s: &str, separator: char) -> Vec<String> {
    let mut parts = vec![String::new()];
    let mut depth = 0i32;
    for c in s.chars() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ => {}
        }
        if c == separator && depth == 0 {
            parts.push(String::new());
        } else {
            parts.last_mut().unwrap().push(c);
        }
    }
    parts.into_iter().map(|p| p.trim().to_owned()).collect()
}

/// The identifiers of `expr` which aren't builtins, in order of appearance, without repetitions.
pub fn symbols(expr: &str) -> Vec<String> {
    let mut res: Vec<String> = Vec::new();
    let chars: Vec<char> = expr.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i].is_ascii_alphabetic() || chars[i] == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let name: String = chars[start..i].iter().collect();
            if formalith::context::Context::builtin_arity(Symbol::new(&name)).is_none()
                && !res.contains(&name)
            {
                res.push(name);
            }
        } else {
            i += 1;
        }
    }
    res
}
