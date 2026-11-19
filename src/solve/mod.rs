//! Solving systems of equations, like `x + y = 3, x - y = 1`.
//!
//! Systems are solved for every symbol they contain ([`Solve::solve`]), or for chosen unknowns, other symbols being
//! parameters ([`Solve::solve_for`]). Linear systems are solved by Gaussian elimination, other polynomial systems
//! by splitting factored equations into cases, substituting unknowns and eliminating them with resultants. A system
//! can have several solutions, like `x = -1` and `x = 1` for `x^2 = 1` ([`Solution::Alternatives`]).
//!
//! ```
//! use formalith::{field::real::R, parse, solve::{Equation, Solution, Solve}, symbol};
//!
//! let equations = [
//!     Equation::new(parse!("x + y", R), parse!("3", R)),
//!     Equation::new(parse!("x - y", R), parse!("1", R)),
//! ];
//! assert_eq!(
//!     R.solve(&equations),
//!     Ok(Solution::Assignments(vec![
//!         (symbol!("x"), parse!("2", R)),
//!         (symbol!("y"), parse!("1", R)),
//!     ]))
//! );
//! ```

mod lattice;
mod linear;
pub(crate) mod polynomial;

use std::{cmp::Ordering, collections::BTreeSet, error::Error, fmt};

use crate::{
    context::{Context, Symbol},
    field::{Group, Ring, Set, matrix::M},
    parser::ParserError,
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Expand, Normalize, SymbolTerm, Term},
};

use polynomial::Assumed;

/// An equation `lhs = rhs`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Equation<T: Set> {
    /// The left side.
    pub lhs: Term<T>,
    /// The right side.
    pub rhs: Term<T>,
}

impl<T: Set> Equation<T> {
    /// Create the equation `lhs = rhs`.
    #[must_use]
    pub const fn new(lhs: Term<T>, rhs: Term<T>) -> Self {
        Self { lhs, rhs }
    }
}

impl<T: Set> Print for Equation<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lhs.print(options, f)?;
        f.write_str(" ")?;
        Self::operator("=", options, f)?;
        f.write_str(" ")?;
        self.rhs.print(options, f)
    }
}

impl<T: Set> PrettyPrint for Equation<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        let mut res = self.lhs.pretty_print(options);
        res.concat("=", true, &self.rhs.pretty_print(options));
        res
    }
}

impl<T: Set> fmt::Display for Equation<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// The unknowns of a solution, each given in terms of the unknowns which aren't listed.
pub type Assignments<T> = Vec<(Symbol, Term<T>)>;

/// The solutions of a system.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Solution<T: Set> {
    /// The system has no solution.
    NoSolution,
    /// Each listed unknown is given in terms of the unknowns which aren't listed, which can take any value.
    /// Every value is a solution if the list is empty.
    Assignments(Assignments<T>),
    /// At least two distinct solutions, each one being like [`Solution::Assignments`], like `x = -1` and `x = 1`
    /// for `x^2 = 1`.
    Alternatives(Vec<Assignments<T>>),
}

impl<T: Group> Solution<T> {
    /// Build the solution made of `branches`, removing duplicates and sorting them.
    #[must_use]
    pub fn from_branches(mut branches: Vec<Assignments<T>>) -> Self {
        // `Term::cmp` ignores coefficients, like in `x = sqrt(2)` and `x = -sqrt(2)`, which are then sorted as text
        let cmp = |a: &Assignments<T>, b: &Assignments<T>| {
            a.len().cmp(&b.len()).then_with(|| {
                a.iter()
                    .zip(b)
                    .map(|((x, u), (y, v))| {
                        x.cmp(y)
                            .then_with(|| u.cmp(v))
                            .then_with(|| plain(u).cmp(&plain(v)))
                    })
                    .find(|ordering| ordering.is_ne())
                    .unwrap_or(Ordering::Equal)
            })
        };
        branches.sort_by(cmp);
        branches.dedup();
        match branches.len() {
            0 => Self::NoSolution,
            1 => Self::Assignments(branches.pop().expect("There is one branch")),
            _ => Self::Alternatives(branches),
        }
    }
}

impl<T: Set> Solution<T> {
    /// The assignments as equations `x = value`.
    fn equations(assignments: &[(Symbol, Term<T>)]) -> impl Iterator<Item = Equation<T>> {
        assignments.iter().map(|(symbol, value)| {
            Equation::new(
                Term::Symbol(SymbolTerm::new(*symbol, value.get_set())),
                value.clone(),
            )
        })
    }

    /// The printed solutions, each one being a list of assignments.
    fn branches(&self) -> &[Assignments<T>] {
        match self {
            Self::NoSolution => &[],
            Self::Assignments(assignments) => std::slice::from_ref(assignments),
            Self::Alternatives(branches) => branches,
        }
    }

    /// The text printed when there isn't any assignment.
    fn text(&self, options: &PrintOptions) -> Option<String> {
        let text = match self {
            Self::NoSolution => "no solution",
            Self::Assignments(assignments) if assignments.is_empty() => "true",
            Self::Assignments(_) | Self::Alternatives(_) => return None,
        };
        Some(if options.typst {
            format!("\"{text}\"")
        } else {
            text.to_owned()
        })
    }

    /// Print one solution, its assignments being separated by commas.
    fn print_assignments(
        assignments: &[(Symbol, Term<T>)],
        options: &PrintOptions,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        for (i, equation) in Self::equations(assignments).enumerate() {
            if i != 0 {
                Self::delimiter(",", options, f)?;
                f.write_str(" ")?;
            }
            equation.print(options, f)?;
        }
        Ok(())
    }
}

impl<T: Set> Print for Solution<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(text) = self.text(options) {
            return f.write_str(&text);
        }
        // One solution per line, `\` being a line break in Typst
        for (i, assignments) in self.branches().iter().enumerate() {
            if i != 0 {
                f.write_str(if options.typst { " \\ " } else { "\n" })?;
            }
            Self::print_assignments(assignments, options, f)?;
        }
        Ok(())
    }
}

impl<T: Set> PrettyPrint for Solution<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        if let Some(text) = self.text(options) {
            return text.into();
        }
        let mut res = PrettyPrinter::empty();
        for assignments in self.branches() {
            let mut line = PrettyPrinter::empty();
            for equation in Self::equations(assignments) {
                line.concat(", ", false, &equation.pretty_print(options));
            }
            res.stack(&line);
        }
        res
    }
}

impl<T: Set> fmt::Display for Solution<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// An error raised while solving a system.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveError {
    /// A term of an equation is not linear in the unknowns. Raised by the linear solver, non-linear systems being
    /// then solved as polynomial systems.
    NonLinear(String),
    /// A term of an equation is not polynomial in the unknowns, like `abs(x)` or `2^x`.
    NotPolynomial(String),
    /// An equation can't be solved, like a polynomial of degree 3 without rational roots.
    Unsolvable(String),
    /// A pivot of the elimination is not invertible in the set, like `2` in `Z`.
    NotInvertible,
    /// Equations can't be solved in this set.
    Unsupported,
}

impl fmt::Display for SolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonLinear(term) => {
                write!(
                    f,
                    "`{term}` is not linear, only linear systems can be solved"
                )
            }
            Self::NotPolynomial(term) => write!(
                f,
                "`{term}` is not polynomial in the unknowns, only polynomial systems can be solved"
            ),
            Self::Unsolvable(term) => write!(f, "can't solve `{term} = 0`"),
            Self::NotInvertible => f.write_str("a pivot is not invertible in this set"),
            Self::Unsupported => f.write_str("equations can't be solved in this set"),
        }
    }
}

impl Error for SolveError {}

impl From<SolveError> for ParserError {
    fn from(value: SolveError) -> Self {
        Self::new(value.to_string())
    }
}

/// Print `term` on one line, without colors, for error messages.
pub(crate) fn plain<T: PrettyPrint>(term: &T) -> String {
    term.with_options(PrintOptions::plain()).to_string()
}

/// Sets in which systems of equations can be solved. Implemented for every set, but solving fails at runtime
/// for sets that aren't commutative rings.
pub trait Solve: Set {
    /// Solve `equations` for every symbol they contain except builtin constants like `{$pi$}`, sorted by name.
    ///
    /// # Errors
    /// Returns an error if the system is not supported, like a non-polynomial system or a polynomial without
    /// expressible roots.
    fn solve(&self, equations: &[Equation<Self>]) -> Result<Solution<Self>, SolveError> {
        let mut unknowns: Vec<Symbol> = equations
            .iter()
            .flat_map(|equation| [&equation.lhs, &equation.rhs])
            .flat_map(Term::symbols)
            .filter(|symbol| !Context::is_builtin_constant(*symbol))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        unknowns.sort_by(|a, b| a.name().cmp(b.name()));
        self.solve_for(equations, &unknowns)
    }

    /// Solve `equations` for `unknowns`, without repetition. Other symbols are parameters, assumed generic: a
    /// symbolic pivot, like `a` in `a*x = 1`, is assumed to be non-zero.
    ///
    /// # Errors
    /// Returns an error if the system is not supported, like a non-polynomial system or a polynomial without
    /// expressible roots.
    fn solve_for(
        &self,
        equations: &[Equation<Self>],
        unknowns: &[Symbol],
    ) -> Result<Solution<Self>, SolveError>;
}

impl<T: Set> Solve for T {
    default fn solve_for(
        &self,
        _: &[Equation<Self>],
        _: &[Symbol],
    ) -> Result<Solution<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }
}

impl<T: Ring> Solve for T {
    default fn solve_for(
        &self,
        equations: &[Equation<Self>],
        unknowns: &[Symbol],
    ) -> Result<Solution<Self>, SolveError> {
        // Solve `lhs - rhs = 0`, written as a fraction `n / d`: solutions of `n = 0` where `d` vanishes are dropped
        let (expressions, denominators): (Vec<_>, Vec<_>) = equations
            .iter()
            .map(|equation| {
                let (num, den) = (equation.lhs.clone() - equation.rhs.clone())
                    .normalize()
                    .as_fraction(true);
                (num.expand(), den)
            })
            .unzip();
        let solution = match linear::solve(&expressions, unknowns, *self) {
            Err(SolveError::NonLinear(_)) => polynomial::solve(&expressions, unknowns),
            res => res,
        }?;
        let denominators: Vec<_> = denominators
            .into_iter()
            .filter(|den| den.symbols().iter().any(|s| unknowns.contains(s)))
            .collect();
        // Solutions contradicting the assumptions on the unknowns are dropped too
        let contradicts = |assignments: &Assignments<Self>| {
            assignments
                .iter()
                .any(|(symbol, value)| Self::contradicts(*symbol, value))
        };
        let vanishes = |assignments: &Assignments<Self>| {
            denominators.iter().any(|den| {
                assignments
                    .iter()
                    .try_fold(den.clone(), |den, (symbol, value)| {
                        den.substitute(*symbol, value)
                    })
                    .is_some_and(|den| den.expand().is_zero())
            })
        };
        let branches = match solution {
            Solution::NoSolution => vec![],
            Solution::Assignments(assignments) => vec![assignments],
            Solution::Alternatives(branches) => branches,
        };
        Ok(Solution::from_branches(
            branches
                .into_iter()
                .filter(|assignments| !vanishes(assignments) && !contradicts(assignments))
                .collect(),
        ))
    }
}

// Matrices aren't commutative, so Gaussian elimination doesn't apply
impl<T: Ring> Solve for M<T> {
    fn solve_for(&self, _: &[Equation<Self>], _: &[Symbol]) -> Result<Solution<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }
}
