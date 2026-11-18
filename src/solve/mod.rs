//! Solving systems of equations, like `x + y = 3, x - y = 1`.
//!
//! Systems are solved for every symbol they contain ([`Solve::solve`]), or for chosen unknowns, other symbols being
//! parameters ([`Solve::solve_for`]). Only linear systems are supported for now: new strategies (like polynomial
//! equations) should be added in the implementation of [`Solve::solve_for`] for rings.
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

mod linear;

use std::{collections::BTreeSet, error::Error, fmt};

use crate::{
    context::{Context, Symbol},
    field::{Ring, Set, matrix::M},
    parser::ParserError,
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Expand, Normalize, SymbolTerm, Term},
};

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

/// The solutions of a system.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Solution<T: Set> {
    /// The system has no solution.
    NoSolution,
    /// Each listed unknown is given in terms of the unknowns which aren't listed, which can take any value.
    /// Every value is a solution if the list is empty.
    Assignments(Vec<(Symbol, Term<T>)>),
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

    /// The text printed when there isn't any assignment.
    fn text(&self, options: &PrintOptions) -> Option<String> {
        let text = match self {
            Self::NoSolution => "no solution",
            Self::Assignments(assignments) if assignments.is_empty() => "true",
            Self::Assignments(_) => return None,
        };
        Some(if options.typst {
            format!("\"{text}\"")
        } else {
            text.to_owned()
        })
    }
}

impl<T: Set> Print for Solution<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(text) = self.text(options) {
            return f.write_str(&text);
        }
        let Self::Assignments(assignments) = self else {
            unreachable!()
        };
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

impl<T: Set> PrettyPrint for Solution<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        if let Some(text) = self.text(options) {
            return text.into();
        }
        let Self::Assignments(assignments) = self else {
            unreachable!()
        };
        let mut res = PrettyPrinter::from(String::new());
        for equation in Self::equations(assignments) {
            res.concat(", ", false, &equation.pretty_print(options));
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
    /// A term of an equation is not linear in the unknowns.
    NonLinear(String),
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
    term.with_options(PrintOptions {
        colors: false,
        typst: false,
        pretty_print: false,
    })
    .to_string()
}

/// Sets in which systems of equations can be solved. Implemented for every set, but solving fails at runtime
/// for sets that aren't commutative rings.
pub trait Solve: Set {
    /// Solve `equations` for every symbol they contain, sorted by name.
    ///
    /// # Errors
    /// Returns an error if the system is not supported, like a non-linear system.
    fn solve(&self, equations: &[Equation<Self>]) -> Result<Solution<Self>, SolveError> {
        let mut unknowns: Vec<Symbol> = equations
            .iter()
            .flat_map(|equation| [&equation.lhs, &equation.rhs])
            .flat_map(Term::symbols)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        unknowns.sort_by(|a, b| {
            Context::get_symbol_data(a)
                .name
                .cmp(&Context::get_symbol_data(b).name)
        });
        self.solve_for(equations, &unknowns)
    }

    /// Solve `equations` for `unknowns`, without repetition. Other symbols are parameters, assumed generic: a
    /// symbolic pivot, like `a` in `a*x = 1`, is assumed to be non-zero.
    ///
    /// # Errors
    /// Returns an error if the system is not supported, like a non-linear system.
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
        // Solve `lhs - rhs = 0`
        let expressions: Vec<_> = equations
            .iter()
            .map(|equation| {
                (equation.lhs.clone() - equation.rhs.clone())
                    .normalize()
                    .expand()
            })
            .collect();
        linear::solve(&expressions, unknowns, *self)
    }
}

// Matrices aren't commutative, so Gaussian elimination doesn't apply
impl<T: Ring> Solve for M<T> {
    fn solve_for(&self, _: &[Equation<Self>], _: &[Symbol]) -> Result<Solution<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }
}
