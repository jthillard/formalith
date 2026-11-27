//! Extrema: the points where a function reaches its global minimum or maximum, `argmin(x^4 - 2 x^2, x)`,
//! `argmax(x - x^2, x, 0, 2)` or `argmin(x^2 + y^2 - 2 x, x, y)`, or a local one, `localmin(x^3 - 3 x, x)`.
//!
//! A function of one variable is minimized over ℝ or over `{$[a, b]$}` by comparing its values at its critical
//! points, at the points where it isn't differentiable or stops being defined, and at the bounds, with its limits
//! at the ends of the intervals where it is defined: the minimum isn't reached when a limit is lower. A function
//! of several variables must be a rational function without parameters: the critical point with the lowest value
//! is the minimum when `{$f < m$}` has no solution, found by the cylindrical algebraic decomposition, otherwise
//! there is no minimum, every minimizer of a differentiable function on an open set being a critical point.
//!
//! Local minima of a function of one variable are found by the first derivative test, with the signs of the
//! derivative between its sorted critical points, and at the special points by comparing the value with the
//! one-sided limits. Those of a function of several variables are critical points where the Hessian matrix is
//! positive definite, degenerate ones being local minima when they are global ones.
//!
//! ```
//! use formalith::{field::real::R, optimize::{Extremum, Optimize}, parse, solve::Solution, symbol};
//!
//! let x = symbol!("x");
//! let optimum = R.optimize(&parse!("x^2 - 2*x", R), &[x], None, Extremum::GlobalMin).unwrap();
//! assert_eq!(optimum.solution, Solution::Assignments(vec![(x, parse!("1", R))]));
//! let optimum = R.optimize(&parse!("x^3 - 3*x", R), &[x], None, Extremum::LocalMax).unwrap();
//! assert_eq!(optimum.solution, Solution::Assignments(vec![(x, parse!("-1", R))]));
//! ```
//!
//! Both kinds are listed with the values of the function by [`Optimize::extrema`], `extrema(x^2 - 2 x, x, 0, 3)`
//! or `localextrema(x^3 - 3 x, x)`:
//!
//! ```
//! use formalith::{field::real::R, optimize::Optimize, parse, symbol};
//!
//! let x = symbol!("x");
//! let extrema = R.extrema(&parse!("x^3 - 3*x", R), &[x], None, true).unwrap();
//! assert_eq!(extrema.to_string(), "min: x = 1, f = -2\nmax: x = -1, f = 2");
//! ```

mod multivariate;
pub(crate) mod univariate;

use malachite::{
    Rational,
    base::num::arithmetic::traits::{Abs, Pow, Sign},
};
use std::{cmp::Ordering, fmt};

use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions, SignSet},
    },
    field::{
        Set,
        real::{
            Real,
            approx::approximate_fixed,
            expr::{Expr, constant_sign, depends, fun, map_tree, size, subs, zero},
        },
    },
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    solve::{
        Assignments, Equation, Solution, SolveError, is_integer_parameter, is_natural_parameter,
    },
    symbol,
    term::{Expand, Normalize, SymbolTerm, Term},
};

/// The minimizers or maximizers of a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Optimum<T: Set> {
    /// The equations of the critical points, `{$diff f / diff x_i = 0$}` for each unknown.
    pub equations: Vec<Equation<T>>,
    /// The points where the extremum is reached, [`Solution::NoSolution`] when it isn't, like for `{$e^x$}`.
    pub solution: Solution<T>,
}

/// A point where a function has an extremum, with the value of the function there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtremumPoint<T: Set> {
    /// Whether it is a maximum, otherwise a minimum.
    pub max: bool,
    /// The point, like a solution: unknowns which aren't listed can take any value.
    pub point: Assignments<T>,
    /// The value of the function at the point.
    pub value: Term<T>,
}

/// The minima then the maxima of a function, global or local ones, printed one per line like
/// `min: x = 1, f = -2`, `no extremum` when there is none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extrema<T: Set> {
    /// The equations of the critical points, `{$diff f / diff x_i = 0$}` for each unknown.
    pub equations: Vec<Equation<T>>,
    /// The extrema, minima first.
    pub points: Vec<ExtremumPoint<T>>,
}

impl<T: Set> Extrema<T> {
    /// The symbol `f` standing for the function in the printed values.
    fn function(set: T) -> Term<T> {
        Term::Symbol(SymbolTerm::new(symbol!("f"), set))
    }

    /// The label of `point`, `min:` or `max:`.
    fn label(point: &ExtremumPoint<T>, options: PrintOptions) -> String {
        let label = if point.max { "max:" } else { "min:" };
        if options.typst {
            format!("\"{label}\"")
        } else {
            label.to_owned()
        }
    }

    /// The text printed when there is no extremum.
    fn none(options: PrintOptions) -> String {
        if options.typst {
            "\"no extremum\"".to_owned()
        } else {
            "no extremum".to_owned()
        }
    }
}

impl<T: Set> Print for Extrema<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.points.is_empty() {
            return f.write_str(&Self::none(*options));
        }
        // One extremum per line, `\` being a line break in Typst
        for (i, point) in self.points.iter().enumerate() {
            if i != 0 {
                f.write_str(if options.typst { " \\ " } else { "\n" })?;
            }
            f.write_str(&Self::label(point, *options))?;
            f.write_str(" ")?;
            if !point.point.is_empty() {
                Solution::print_assignments(&point.point, *options, f)?;
                Self::delimiter(",", options, f)?;
                f.write_str(if options.typst { " quad " } else { " " })?;
            }
            Equation::new(Self::function(point.value.get_set()), point.value.clone())
                .print(options, f)?;
        }
        Ok(())
    }
}

impl<T: Set> PrettyPrint for Extrema<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        if self.points.is_empty() {
            return Self::none(*options).into();
        }
        let mut res = PrettyPrinter::empty();
        for point in &self.points {
            let mut line = PrettyPrinter::empty();
            let value = Equation::new(Self::function(point.value.get_set()), point.value.clone());
            for equation in Solution::equations(&point.point).chain([value]) {
                line.concat_breaking(
                    ", ",
                    false,
                    &equation.pretty_print(options),
                    crate::printer::BreakKind::Separator,
                );
            }
            let mut labeled = PrettyPrinter::from(Self::label(point, *options));
            let width = options
                .width
                .map(|width| width.saturating_sub(labeled.width() + 1));
            labeled.concat(" ", false, &line.wrapped(width));
            res.stack(&labeled);
        }
        res
    }
}

impl<T: Set> fmt::Display for Extrema<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// The kind of extremum searched.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Extremum {
    /// The global minimum, `argmin`
    GlobalMin,
    /// The global maximum, `argmax`
    GlobalMax,
    /// Local minima, `localmin`
    LocalMin,
    /// Local maxima, `localmax`
    LocalMax,
}

impl Extremum {
    /// Whether maxima are searched.
    #[must_use]
    pub const fn is_max(self) -> bool {
        matches!(self, Self::GlobalMax | Self::LocalMax)
    }

    /// Whether local extrema are searched.
    #[must_use]
    pub const fn is_local(self) -> bool {
        matches!(self, Self::LocalMin | Self::LocalMax)
    }
}

/// Sets in which extrema can be found: only [`R`](crate::field::real::R), other sets fail at runtime.
pub trait Optimize: Set {
    /// The points where `f` reaches the `extremum` over the real values of `unknowns`, or over `{$[a, b]$}` for
    /// `bounds` `(a, b)` and a single unknown.
    ///
    /// # Errors
    /// [`SolveError::Optimization`] when the extremum can't be decided: equations that can't be solved, values,
    /// limits or signs that can't be compared, several variables in a function that isn't rational or with
    /// parameters for global extrema, degenerate critical points for local ones.
    fn optimize(
        &self,
        f: &Term<Self>,
        unknowns: &[Symbol],
        bounds: Option<&(Term<Self>, Term<Self>)>,
        extremum: Extremum,
    ) -> Result<Optimum<Self>, SolveError>;

    /// The points where `f` has a global minimum or maximum (local ones when `local` is `true`), with the values
    /// of `f` there, like [`Optimize::optimize`] for both kinds.
    ///
    /// # Errors
    /// Those of [`Optimize::optimize`] for either kind.
    fn extrema(
        &self,
        f: &Term<Self>,
        unknowns: &[Symbol],
        bounds: Option<&(Term<Self>, Term<Self>)>,
        local: bool,
    ) -> Result<Extrema<Self>, SolveError>;
}

impl<T: Set> Optimize for T {
    default fn optimize(
        &self,
        _: &Term<Self>,
        _: &[Symbol],
        _: Option<&(Term<Self>, Term<Self>)>,
        _: Extremum,
    ) -> Result<Optimum<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }

    default fn extrema(
        &self,
        _: &Term<Self>,
        _: &[Symbol],
        _: Option<&(Term<Self>, Term<Self>)>,
        _: bool,
    ) -> Result<Extrema<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }
}

impl Optimize for Real {
    fn optimize(
        &self,
        f: &Expr,
        unknowns: &[Symbol],
        bounds: Option<&(Expr, Expr)>,
        extremum: Extremum,
    ) -> Result<Optimum<Self>, SolveError> {
        profile_scope!("optimize");
        let equations: Vec<_> = unknowns
            .iter()
            .map(|x| Equation::new(f.derivative(*x).normalize(), zero()))
            .collect();
        // Maxima of `f` are minima of `-f`
        let f = if extremum.is_max() { -f } else { f.clone() };
        let solution = if unknowns.iter().all(|x| !depends(&f, *x)) {
            // A constant function reaches its extremum everywhere
            Solution::Assignments(vec![])
        } else if let [x] = unknowns {
            let analysis = univariate::Analysis::new(&f, *x, bounds)?;
            if extremum.is_local() {
                analysis.local_min()?
            } else {
                analysis.global_min()?
            }
        } else if bounds.is_some() {
            return Err(error("bounds are only supported for a single variable"));
        } else if extremum.is_local() {
            multivariate::local_min(&f, unknowns, &equations)?
        } else {
            multivariate::argmin(&f, unknowns, &equations)?
        };
        Ok(Optimum {
            equations,
            solution,
        })
    }

    fn extrema(
        &self,
        f: &Expr,
        unknowns: &[Symbol],
        bounds: Option<&(Expr, Expr)>,
        local: bool,
    ) -> Result<Extrema<Self>, SolveError> {
        let (min, max) = if local {
            (Extremum::LocalMin, Extremum::LocalMax)
        } else {
            (Extremum::GlobalMin, Extremum::GlobalMax)
        };
        let minima = self.optimize(f, unknowns, bounds, min)?;
        let maxima = self.optimize(f, unknowns, bounds, max)?;
        let mut points = vec![];
        for (optimum, max) in [(&minima, false), (&maxima, true)] {
            for point in optimum.solution.branches() {
                points.push(ExtremumPoint {
                    max,
                    point: point.clone(),
                    value: value_at(f, point)?,
                });
            }
        }
        Ok(Extrema {
            equations: minima.equations,
            points,
        })
    }
}

/// The value of `f` at `point`, its integer parameters `k`, `k_1`... being assumed integers and its natural
/// parameters `n`, `n_1`... non-negative integers: the smaller of the
/// substituted term and its expansion, not expanded when its roots are nested 3 deep (roots of quartics by Ferrari's
/// method), whose expansion may not finish.
fn value_at(f: &Expr, point: &Assignments<Real>) -> Result<Expr, SolveError> {
    let used = f.symbols();
    let mut assumptions = Assumptions::current();
    for (_, value) in point {
        for k in value.symbols() {
            if used.contains(&k) {
                continue;
            }
            if is_integer_parameter(k) {
                assumptions.assume(k, Assumption::INTEGER).map_err(error)?;
            } else if is_natural_parameter(k) {
                let natural = Assumption::INTEGER
                    .and(Assumption::sign(SignSet::NONNEGATIVE))
                    .expect("They are compatible");
                assumptions.assume(k, natural).map_err(error)?;
            }
        }
    }
    let _guard = assumptions.enter();
    let res = point
        .iter()
        .fold(f.clone(), |res, (symbol, value)| subs(&res, *symbol, value))
        .normalize();
    if root_depth(&res) >= 3 {
        return Ok(res);
    }
    let expanded = res.expand();
    Ok(if size(&expanded) < size(&res) {
        expanded
    } else {
        res
    })
}

/// The nesting depth of the roots of `term`: 1 for a root of a value, 2 for a root of a sum of such roots...
fn root_depth(term: &Expr) -> usize {
    match term {
        Term::Value(_) | Term::Symbol(_) | Term::Fun(_) => 0,
        Term::Add(add) => add.iter().map(root_depth).max().unwrap_or(0),
        Term::Mul(mul) => mul.iter().map(root_depth).max().unwrap_or(0),
        Term::Pow(pow) => {
            let inner = root_depth(&pow.base).max(root_depth(&pow.exponant));
            match &**pow.exponant {
                Term::Value(e) if e.value.denominator_ref() != &1u32 => inner + 1,
                _ => inner,
            }
        }
    }
}

/// An error with `reason`.
fn error(reason: impl Into<String>) -> SolveError {
    SolveError::Optimization(reason.into())
}

/// Compare `p` and `q`, exactly when their difference is zero once expanded, otherwise from its sign (structure,
/// assumptions, then approximation of constants). `None` when it is unknown.
///
/// A constant difference far from zero is compared by a single approximation first, since expanding differences
/// of nested radicals (roots of quartics) may not finish.
fn compare(p: &Expr, q: &Expr) -> Option<Ordering> {
    /// Bits of the quick approximation, accurate to about `{$2^(-BITS)$}`.
    const BITS: u64 = 64;
    let difference = (p.clone() - q.clone()).normalize();
    if difference.is_zero() {
        return Some(Ordering::Equal);
    }
    if difference
        .symbols()
        .iter()
        .all(|symbol| Context::is_builtin_constant(*symbol))
        && let Some(approximation) = approximate_fixed(&difference, BITS)
        && (&approximation).abs() > Rational::from(2).pow(-(BITS / 2).cast_signed())
    {
        return Some(approximation.sign());
    }
    if difference.expand().is_zero() {
        return Some(Ordering::Equal);
    }
    // Limits write `{$tan u$}` as `{$sin u / cos u$}`, and approximations don't decide zero
    let sine_cosine = map_tree(&difference, &|t| match t {
        Term::Fun(f) if f.get_ident() == Context::TAN => {
            f.get_args::<Real>().and_then(|args| match args.as_slice() {
                [u] => Some(fun(Context::SIN, u.clone()) / fun(Context::COS, u.clone())),
                _ => None,
            })
        }
        _ => None,
    });
    if sine_cosine != difference && sine_cosine.normalize().expand().is_zero() {
        return Some(Ordering::Equal);
    }
    constant_sign(&difference)
}

/// Keep in `best` the candidates with the lowest value, adding `candidate` with its `value`.
fn keep_lowest<P>(best: &mut Vec<(P, Expr)>, candidate: P, value: Expr) -> Result<(), SolveError> {
    let Some((_, lowest)) = best.first() else {
        best.push((candidate, value));
        return Ok(());
    };
    match compare(&value, lowest) {
        Some(Ordering::Less) => *best = vec![(candidate, value)],
        Some(Ordering::Equal) => best.push((candidate, value)),
        Some(Ordering::Greater) => {}
        None => {
            return Err(error(format!(
                "can't compare the values `{}` and `{}`",
                crate::solve::plain(&value),
                crate::solve::plain(lowest)
            )));
        }
    }
    Ok(())
}
