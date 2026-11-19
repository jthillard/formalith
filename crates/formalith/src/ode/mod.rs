//! Ordinary differential equations, like `dsolve(y' = x y)` or `dsolve(y'' + y = 0, y(0) = 1, y'(0) = 0)`.
//!
//! The equation is written with placeholders `@y0, @y1, ...` for `{$y(x), y'(x), ...$}`. First-order equations
//! are solved for `{$y'$}` with [`Solve::solve_for`], then each `{$y' = F(x, y)$}` is solved as a linear
//! equation (integrating factor) or as a separable one, `{$integral dy / g(y) = integral f(x) dx + c_1$}` being
//! solved for `y` when possible, and kept implicit otherwise. Linear equations of any order with constant
//! coefficients are solved with the roots of their characteristic polynomial, a particular solution being found by
//! variation of parameters. Integration constants are `c_1, c_2, ...`, and initial conditions like `y'(0) = 1` are
//! solved for them.
//!
//! ```
//! use formalith::{field::real::R, ode::{Dsolve, OdeBranch}, parse, solve::Equation, symbol};
//!
//! let (y, x) = (symbol!("y"), symbol!("x"));
//! // `{$y' = y$}`, with `y(x)` and its derivative written as functions
//! let equation = Equation::new(parse!("diff(y(x), x)", R), parse!("y(x)", R));
//! let solution = R.dsolve(&equation, &[], y, x).unwrap();
//! assert_eq!(solution.branches, vec![OdeBranch::Explicit(parse!("c_1*exp(x)", R))]);
//! ```

mod first_order;
mod linear;

use std::{cell::Cell, error::Error, fmt};

use crate::{
    context::{Context, Symbol},
    field::{
        Set,
        real::{
            R,
            expr::{
                Expr, Real, depends, fun, map_tree, size, subs, try_map_operands, variable, zero,
            },
        },
    },
    parser::ParserError,
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    solve::{Equation, Solution, Solve, plain},
    sum::is_rational_function,
    term::{Expand, Fun, Normalize, SymbolTerm, Term},
};

/// An initial condition `{$y^((k))(a) = b$}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Condition<T: Set> {
    /// The order `k` of the derivative.
    pub order: usize,
    /// The point `a`.
    pub point: Term<T>,
    /// The value `b`.
    pub value: Term<T>,
}

/// A solution of a differential equation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OdeBranch<T: Set> {
    /// `{$y(x) = f(x)$}`.
    Explicit(Term<T>),
    /// An equation satisfied by `y(x)`, which couldn't be solved for it.
    Implicit(Equation<T>),
}

/// The solutions of a differential equation for `function(variable)`, depending on the constants `c_1, c_2, ...`
/// not fixed by initial conditions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OdeSolution<T: Set> {
    /// The unknown function.
    pub function: Symbol,
    /// Its variable.
    pub variable: Symbol,
    /// The solutions, at least one.
    pub branches: Vec<OdeBranch<T>>,
}

impl<T: Set> OdeSolution<T> {
    /// Each solution as an equation, `{$y(x) = f(x)$}` for explicit ones.
    fn equations(&self) -> impl Iterator<Item = Equation<T>> {
        self.branches.iter().map(|branch| match branch {
            OdeBranch::Explicit(f) => {
                let set = f.get_set();
                let x = Term::Symbol(SymbolTerm::new(self.variable, set));
                let y = Term::Fun(Box::new(Fun::new(self.function, vec![x], set)));
                Equation::new(y, f.clone())
            }
            OdeBranch::Implicit(equation) => equation.clone(),
        })
    }
}

impl<T: Set> Print for OdeSolution<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // One solution per line, `\` being a line break in Typst
        for (i, equation) in self.equations().enumerate() {
            if i != 0 {
                f.write_str(if options.typst { " \\ " } else { "\n" })?;
            }
            equation.print(options, f)?;
        }
        Ok(())
    }
}

impl<T: Set> PrettyPrint for OdeSolution<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        let mut res = PrettyPrinter::empty();
        for equation in self.equations() {
            res.stack(&equation.pretty_print(options));
        }
        res
    }
}

impl<T: Set> fmt::Display for OdeSolution<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// An error raised while solving a differential equation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OdeError {
    /// The equation isn't of a supported kind, or a step failed, like an integral without antiderivative.
    Unsupported(String),
    /// No solution satisfies the initial conditions.
    NoSolution,
    /// Differential equations can't be solved in this set.
    UnsupportedSet,
}

impl fmt::Display for OdeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(message) => f.write_str(message),
            Self::NoSolution => f.write_str("no solution satisfies the initial conditions"),
            Self::UnsupportedSet => {
                f.write_str("differential equations can't be solved in this set")
            }
        }
    }
}

impl Error for OdeError {}

impl From<OdeError> for ParserError {
    fn from(value: OdeError) -> Self {
        Self::new(value.to_string())
    }
}

/// The result of solving a differential equation.
pub type OdeResult<T> = Result<T, OdeError>;

/// Sets in which differential equations can be solved: only [`R`], other sets fail at runtime.
pub trait Dsolve: Set {
    /// Solve `equation` for `function(x)`, written as the function `function(x)` and its derivatives
    /// `diff(function(x), x)`, with initial `conditions`.
    ///
    /// # Errors
    /// [`OdeError::Unsupported`] when the equation is neither a first-order linear or separable equation, nor a
    /// linear equation with constant coefficients, or when it can't be solved, [`OdeError::NoSolution`] when the
    /// initial conditions can't be satisfied.
    fn dsolve(
        &self,
        equation: &Equation<Self>,
        conditions: &[Condition<Self>],
        function: Symbol,
        x: Symbol,
    ) -> OdeResult<OdeSolution<Self>>;
}

impl<T: Set> Dsolve for T {
    default fn dsolve(
        &self,
        _: &Equation<Self>,
        _: &[Condition<Self>],
        _: Symbol,
        _: Symbol,
    ) -> OdeResult<OdeSolution<Self>> {
        Err(OdeError::UnsupportedSet)
    }
}

impl Dsolve for Real {
    fn dsolve(
        &self,
        equation: &Equation<Self>,
        conditions: &[Condition<Self>],
        function: Symbol,
        x: Symbol,
    ) -> OdeResult<OdeSolution<Self>> {
        let e = (equation.lhs.clone() - equation.rhs.clone()).normalize();
        let order = Cell::new(0);
        let e = map_tree(&e, &|t| {
            let k = derivative_order(t, function, x)?;
            order.set(order.get().max(k));
            Some(variable(placeholder(k)))
        });
        let name = function.name();
        if mentions(&e, function) {
            return Err(OdeError::Unsupported(format!(
                "`{name}` must only appear as `{name}({})` and its derivatives",
                x.name()
            )));
        }
        let order = order.get();
        if order == 0 {
            return Err(OdeError::Unsupported(format!(
                "the equation contains no derivative of `{name}`"
            )));
        }
        if conditions.len() > order {
            return Err(OdeError::Unsupported(format!(
                "too many initial conditions for an equation of order {order}"
            )));
        }
        if let Some(condition) = conditions.iter().find(|c| c.order >= order) {
            return Err(OdeError::Unsupported(format!(
                "the initial condition on the derivative of order {} is not determined by an equation of order \
                 {order}",
                condition.order
            )));
        }
        let used = e.symbols();
        let constants: Vec<_> = (1..)
            .map(|i| Symbol::new(format!("c_{i}")))
            .filter(|c| !used.contains(c))
            .take(order)
            .collect();
        let branches = if order == 1 {
            first_order::solve(&e, x, constants[0])?
        } else {
            linear::solve(&e, order, x, &constants)?
        };
        let branches = apply_conditions(branches, conditions, x, &constants)?;
        let y = Term::Fun(Box::new(Fun::new(function, vec![variable(x)], R))).normalize();
        let y0 = placeholder(0);
        Ok(OdeSolution {
            function,
            variable: x,
            branches: branches
                .into_iter()
                .map(|branch| match branch {
                    OdeBranch::Explicit(f) => OdeBranch::Explicit(f),
                    OdeBranch::Implicit(equation) => OdeBranch::Implicit(Equation::new(
                        subs(&equation.lhs, y0, &y),
                        subs(&equation.rhs, y0, &y),
                    )),
                })
                .collect(),
        })
    }
}

/// The placeholder `@y<k>` for the `k`-th derivative of the unknown function.
fn placeholder(k: usize) -> Symbol {
    Symbol::new(format!("@y{k}"))
}

/// `k` if `term` is the `k`-th derivative of `function(x)`.
fn derivative_order(term: &Expr, function: Symbol, x: Symbol) -> Option<usize> {
    let Term::Fun(f) = term else {
        return None;
    };
    let args = f.get_args::<Real>()?;
    match (f.get_ident(), args.as_slice()) {
        (ident, [Term::Symbol(s)]) if ident == function && s.symbol == x => Some(0),
        (Context::DIFF, [inner, Term::Symbol(s)]) if s.symbol == x => {
            Some(derivative_order(inner, function, x)? + 1)
        }
        _ => None,
    }
}

/// Whether the function `function` (possibly a builtin) appears in `term`.
fn mentions(term: &Expr, function: Symbol) -> bool {
    if let Term::Fun(f) = term
        && f.get_ident() == function
    {
        return true;
    }
    try_map_operands(term, |operand| {
        if mentions(operand, function) {
            Err(())
        } else {
            Ok(operand.clone())
        }
    })
    .is_err()
}

/// Fix the constants of each solution with the initial conditions, dropping the solutions which can't satisfy them.
fn apply_conditions(
    branches: Vec<OdeBranch<Real>>,
    conditions: &[Condition<Real>],
    x: Symbol,
    constants: &[Symbol],
) -> OdeResult<Vec<OdeBranch<Real>>> {
    if conditions.is_empty() {
        return Ok(branches);
    }
    let y0 = placeholder(0);
    let mut res = vec![];
    for branch in branches {
        let equations: Vec<_> = match &branch {
            OdeBranch::Explicit(f) => conditions
                .iter()
                .map(|condition| {
                    let derivative = (0..condition.order).fold(f.clone(), |f, _| f.derivative(x));
                    Equation::new(
                        subs(&derivative, x, &condition.point),
                        condition.value.clone(),
                    )
                })
                .collect(),
            OdeBranch::Implicit(equation) => conditions
                .iter()
                .map(|condition| {
                    if condition.order != 0 {
                        return Err(OdeError::Unsupported(
                            "initial conditions on derivatives need an explicit solution"
                                .to_owned(),
                        ));
                    }
                    let at =
                        |side: &Expr| subs(&subs(side, x, &condition.point), y0, &condition.value);
                    Ok(Equation::new(at(&equation.lhs), at(&equation.rhs)))
                })
                .collect::<OdeResult<_>>()?,
        };
        let unknowns: Vec<_> = constants
            .iter()
            .copied()
            .filter(|c| {
                equations
                    .iter()
                    .any(|e| depends(&e.lhs, *c) || depends(&e.rhs, *c))
            })
            .collect();
        if unknowns.is_empty() {
            if equations
                .iter()
                .all(|e| (e.lhs.clone() - e.rhs.clone()).expand().is_zero())
            {
                res.push(branch);
            }
            continue;
        }
        let solution = R.solve_for(&equations, &unknowns).map_err(|err| {
            OdeError::Unsupported(format!("can't solve the initial conditions: {err}"))
        })?;
        let assignments = match solution {
            Solution::NoSolution => vec![],
            Solution::Assignments(assignments) => vec![assignments],
            Solution::Alternatives(branches) => branches,
        };
        for assignments in assignments {
            let fix = |t: &Expr| {
                assignments
                    .iter()
                    .fold(t.clone(), |t, (c, value)| subs(&t, *c, value))
            };
            res.push(match &branch {
                OdeBranch::Explicit(f) => OdeBranch::Explicit(tidy(&fix(f))),
                OdeBranch::Implicit(equation) => OdeBranch::Implicit(Equation::new(
                    tidy(&fix(&equation.lhs)),
                    tidy(&fix(&equation.rhs)),
                )),
            });
        }
    }
    if res.is_empty() {
        return Err(OdeError::NoSolution);
    }
    res.dedup();
    Ok(res)
}

/// Integrate `f` with respect to `x`, failing with a readable error.
fn integrate(f: &Expr, x: Symbol) -> OdeResult<Expr> {
    if f.is_zero() {
        return Ok(zero());
    }
    f.integrate(x).map_err(|_| {
        OdeError::Unsupported(format!(
            "can't integrate `{}` with respect to `{}`",
            plain(f),
            x.name()
        ))
    })
}

/// The smallest of the result, its expansion, and its simplification (as a rational function when it is one, and
/// by [`simplify_trigonometric`]).
fn tidy(res: &Expr) -> Expr {
    let expanded = res.expand();
    let mut candidates = vec![];
    candidates.extend(simplify_trigonometric(&expanded));
    if is_rational_function(&expanded) {
        candidates.push(res.simplify());
    }
    candidates.push(expanded);
    candidates.into_iter().fold(res.clone(), |best, candidate| {
        if size(&candidate) < size(&best) {
            candidate
        } else {
            best
        }
    })
}

/// The builtin `simplify` of the expanded term, using `{$sin^2 + cos^2 = 1$}`, if it contains `sin` or `cos`
/// (`simplify` may not terminate on other terms).
fn simplify_trigonometric(term: &Expr) -> Option<Expr> {
    (mentions(term, Context::SIN) || mentions(term, Context::COS))
        .then(|| fun(Context::SIMPLIFY, term.expand()))
}
