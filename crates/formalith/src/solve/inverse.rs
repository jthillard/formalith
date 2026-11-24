//! Equations in one unknown with functions of it, like `{$sin x = 1/2$}`, `{$e^(2x) - 3 e^x + 2 = 0$}` or
//! `{$x e^x = 1$}`, solved by inverting the functions.
//!
//! The non-polynomial parts containing the unknown are the kernels of the equation: functions of it, powers with
//! an exponent depending on it, and powers with a rational exponent. When they are all powers of a single kernel
//! `g` (`{$e^(2x) = (e^x)^2$}`), the equation is a polynomial in `g`, whose roots `c` give equations `{$g = c$}`.
//! These are solved by inverting the function of `g`, then solving for the unknown in its argument, recursively.
//! Periodic functions have one solution per period: `{$sin u = c$}` gives `{$u = arcsin c + 2 k pi$}` and
//! `{$u = pi - arcsin c + 2 k pi$}`, `k` being a new integer parameter (`k`, `k_1`, `k_2`... for nested ones,
//! skipping the names of the equation). Equations `{$(alpha x + beta) e^(gamma x + delta) = c$}` are solved with
//! the Lambert W function, with both branches `{$W_0$}` and `{$W_(-1)$}` when its argument is in `{$(-1/e, 0)$}`.

use std::{cmp::Ordering, collections::BTreeSet};

use malachite::{
    Integer, Rational,
    base::num::arithmetic::traits::{Gcd, Lcm, Reciprocal},
};

use crate::{
    context::{Context, Symbol},
    field::{
        Ring,
        real::{
            R,
            expr::{Expr, constant_sign, depends, fun, map_tree, subs, unary, value, variable},
        },
    },
    term::{Expand, Fun, Normalize, Term},
};

use super::{Equation, Solution, Solve, SolveError, plain};

/// Maximum number of nested inversions.
const MAX_DEPTH: usize = 16;

/// Equations with functions of the unknowns. Implemented for every ring, where they can't be solved by default.
pub(crate) trait Transcendental: Ring {
    /// Solve the expanded equations `expressions = 0` for `unknowns`, after the polynomial solver failed with
    /// `error`, which is returned if they can't be solved.
    fn solve_transcendental(
        expressions: &[Term<Self>],
        unknowns: &[Symbol],
        error: SolveError,
    ) -> Result<Solution<Self>, SolveError>;

    /// Whether the expanded equations `expressions = 0` have functions of the unknowns that are solved by
    /// [`Transcendental::solve_transcendental`], so that the polynomial solver is skipped.
    fn is_transcendental(expressions: &[Term<Self>], unknowns: &[Symbol]) -> bool;
}

impl<T: Ring> Transcendental for T {
    default fn is_transcendental(_: &[Term<Self>], _: &[Symbol]) -> bool {
        false
    }

    default fn solve_transcendental(
        _: &[Term<Self>],
        _: &[Symbol],
        error: SolveError,
    ) -> Result<Solution<Self>, SolveError> {
        Err(error)
    }
}

impl Transcendental for R<Rational> {
    fn is_transcendental(expressions: &[Term<Self>], unknowns: &[Symbol]) -> bool {
        let ([expression], [x]) = (expressions, unknowns) else {
            return false;
        };
        let mut kernels = vec![];
        !collect_kernels(expression, *x, &mut kernels) || !kernels.is_empty()
    }

    /// A single equation in a single unknown is solved by inverting its functions.
    fn solve_transcendental(
        expressions: &[Term<Self>],
        unknowns: &[Symbol],
        error: SolveError,
    ) -> Result<Solution<Self>, SolveError> {
        let ([expression], [x]) = (expressions, unknowns) else {
            return Err(error);
        };
        let inverter = Inverter {
            x: *x,
            used: expression.symbols(),
        };
        let values = inverter.solve(expression, 0)?;
        Ok(Solution::from_branches(
            values.into_iter().map(|value| vec![(*x, value)]).collect(),
        ))
    }
}

/// Whether `symbol` is named like an integer parameter of a periodic solution, `k` or `k_n`.
pub(crate) fn is_integer_parameter(symbol: Symbol) -> bool {
    let name = symbol.name();
    name == "k"
        || name
            .strip_prefix("k_")
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// Solve an equation in the unknown `x`, whose symbols are `used`.
struct Inverter {
    x: Symbol,
    used: BTreeSet<Symbol>,
}

/// A kernel `{$a g^n$}`, `g` being a function, a power with an exponent depending on the unknown, or the base of a
/// power with a rational exponent, and `a` a constant.
struct Kernel {
    /// The term found in the equation.
    term: Expr,
    /// The constant factor `a`, `{$e^(2x - 2) = e^-2 (e^x)^2$}`.
    factor: Expr,
    /// The kernel `g`.
    base: Expr,
    /// The exponent `n`.
    exponent: Rational,
}

impl Inverter {
    /// The integer parameter of the solutions of periodic functions nested `depth` times.
    fn parameter(&self, depth: usize) -> Expr {
        let symbol = std::iter::once("k".to_owned())
            .chain((1..).map(|i| format!("k_{i}")))
            .map(Symbol::new)
            .filter(|symbol| !self.used.contains(symbol))
            .nth(depth)
            .expect("There are infinitely many names");
        variable(symbol)
    }

    /// The values of the unknown such that `expression = 0`.
    fn solve(&self, expression: &Expr, depth: usize) -> Result<Vec<Expr>, SolveError> {
        let unsolvable = || SolveError::Unsolvable(plain(expression));
        if depth > MAX_DEPTH {
            return Err(unsolvable());
        }
        let (numerator, _) = expression.normalize().as_fraction(true);
        let numerator = numerator.expand();
        let mut kernels = vec![];
        if !collect_kernels(&numerator, self.x, &mut kernels) {
            return Err(SolveError::NotPolynomial(plain(&numerator)));
        }
        if kernels.is_empty() {
            return roots(&numerator, self.x).ok_or_else(unsolvable);
        }
        if let Some(factor) = self.exponential_factor(&numerator, &kernels) {
            return self.solve(&(numerator / factor), depth + 1);
        }
        if let Some((kernel, polynomial, s)) = self.as_polynomial(&numerator, &kernels, depth) {
            let values = roots(&polynomial, s).ok_or_else(unsolvable)?;
            let mut res = vec![];
            for c in values {
                for (u, v) in self.invert(&kernel, &c, depth)? {
                    res.extend(self.solve(&(u - v), depth + 1)?);
                }
            }
            return Ok(res);
        }
        if let Some(res) = self.lambert(&numerator, &kernels) {
            return Ok(res);
        }
        Err(SolveError::NotPolynomial(plain(&numerator)))
    }

    /// `expression` as a polynomial in a new symbol `s` standing for a kernel, `{$e^(2x) - e^x$}` being
    /// `{$s^2 - s$}` with `{$s = e^x$}`, if its kernels are powers of a single one. Returns the kernel, the
    /// polynomial and `s`.
    fn as_polynomial(
        &self,
        expression: &Expr,
        kernels: &[Kernel],
        depth: usize,
    ) -> Option<(Expr, Expr, Symbol)> {
        let base = &kernels[0].base;
        if kernels.iter().any(|kernel| kernel.base != *base) {
            return None;
        }
        // The kernel `{$g^m$}`, `m` being the gcd of the exponents
        let m = kernels
            .iter()
            .map(|kernel| kernel.exponent.clone())
            .reduce(|a, b| rational_gcd(&a, &b))?;
        let s = Symbol::new(format!("@s{depth}"));
        let power = |n: &Rational| variable(s).pow(&value(n / &m));
        let mut res = map_tree(expression, &|term| {
            kernels
                .iter()
                .find(|kernel| kernel.term == *term)
                .map(|kernel| &kernel.factor * &power(&kernel.exponent))
        });
        // `{$x + sqrt(x) = 6$}` is `{$s^2 + s = 6$}` with `{$s = sqrt(x)$}`
        if *base == variable(self.x) {
            res = subs(&res, self.x, &power(&Rational::from(1)));
        }
        if depends(&res, self.x) {
            return None;
        }
        Some((kernel_power(base, &m), res.expand(), s))
    }

    /// A factor `{$e^(m u)$}` of every term of `expression`, which never vanishes, when its kernels are powers of
    /// a single exponential `{$e^u$}`: `{$x^2 e^(2x) - e^(2x)$}` is `{$e^(2x) (x^2 - 1)$}`.
    fn exponential_factor(&self, expression: &Expr, kernels: &[Kernel]) -> Option<Expr> {
        let base = &kernels[0].base;
        if kernels.iter().any(|kernel| {
            kernel.base != *base || unary(&kernel.term).is_none_or(|(f, _)| f != Context::EXP)
        }) {
            return None;
        }
        let terms = match expression {
            Term::Add(add) => add.iter().collect(),
            _ => vec![expression],
        };
        // The exponent of the kernel in each term, 0 without it
        let mut m: Option<Rational> = None;
        for term in terms {
            let mut found = vec![];
            collect_kernels(term, self.x, &mut found);
            let exponent = match &found[..] {
                [] => Rational::from(0),
                [kernel] => kernel.exponent.clone(),
                _ => return None,
            };
            m = Some(m.map_or(
                exponent.clone(),
                |m| if exponent < m { exponent } else { m },
            ));
        }
        let m = m.filter(|m| *m != 0)?;
        Some(kernel_power(base, &m))
    }

    /// The equations `u = v` equivalent to `{$g = c$}`, `g` being a function of `u`.
    fn invert(&self, g: &Expr, c: &Expr, depth: usize) -> Result<Vec<(Expr, Expr)>, SolveError> {
        let pi = variable(Context::PI);
        let int = |n: i64| value(Rational::from(n));
        let k = || self.parameter(depth);
        // The sign of `c - a`
        let cmp = |a: i64| constant_sign(&(c - &int(a)));
        let cmp_term = |a: &Expr| constant_sign(&(c - a));
        let unsupported = || SolveError::NotPolynomial(plain(g));
        if let Term::Pow(pow) = g {
            let (b, e) = (&*pow.base, &**pow.exponant);
            if depends(e, self.x) {
                // `{$b^u = c$}`, `{$u = log_b c$}`
                if !matches!(cmp(0), Some(Ordering::Greater)) && cmp(0).is_some() {
                    return Ok(vec![]);
                }
                let log = Term::Fun(Box::new(Fun::new(
                    Context::LOG,
                    vec![c.clone(), b.clone()],
                    R,
                )))
                .normalize();
                return Ok(vec![(e.clone(), log)]);
            }
            // `{$b^(p/q) = c$}`
            let Term::Value(e) = e else {
                return Err(unsupported());
            };
            let (p, q) = (e.value.numerator_ref(), e.value.denominator_ref());
            let inverse = value((&e.value).reciprocal());
            let odd = |n: &malachite::Natural| n % malachite::Natural::from(2u32) == 1u32;
            if !odd(q) && matches!(cmp(0), Some(Ordering::Less)) {
                return Ok(vec![]);
            }
            if odd(p) || !odd(q) {
                return Ok(vec![(b.clone(), c.pow(&inverse))]);
            }
            // An even power of an odd root: `{$b = plus.minus c^(q/p)$}`
            if matches!(cmp(0), Some(Ordering::Less)) {
                return Ok(vec![]);
            }
            let root = c.pow(&inverse);
            return Ok(vec![(b.clone(), -&root), (b.clone(), root)]);
        }
        let (ident, u) = unary(g).ok_or_else(unsupported)?;
        let u = u.clone();
        let f = |ident: Symbol, arg: Expr| fun(ident, arg);
        let single = |v: Expr| Ok(vec![(u.clone(), v)]);
        let both = |v: Expr| Ok(vec![(u.clone(), -&v), (u.clone(), v)]);
        let none = || Ok(vec![]);
        let half_pi = &pi / &int(2);
        match ident {
            Context::SIN | Context::COS => {
                if cmp(1) == Some(Ordering::Greater) || cmp(-1) == Some(Ordering::Less) {
                    return none();
                }
                let period = int(2) * &pi * k();
                let sin = ident == Context::SIN;
                match (cmp(1), cmp(-1)) {
                    (Some(Ordering::Equal), _) => {
                        single(if sin { half_pi } else { int(0) } + period)
                    }
                    (_, Some(Ordering::Equal)) => single(if sin { -half_pi } else { pi } + period),
                    _ if sin => {
                        let asin = f(Context::ASIN, c.clone());
                        Ok(vec![
                            (u.clone(), &asin + &period),
                            (u.clone(), pi - asin + period),
                        ])
                    }
                    _ => {
                        let acos = f(Context::ACOS, c.clone());
                        Ok(vec![
                            (u.clone(), &acos + &period),
                            (u.clone(), period - acos),
                        ])
                    }
                }
            }
            Context::TAN => single(f(Context::ATAN, c.clone()) + pi * k()),
            Context::EXP => match cmp(0) {
                Some(Ordering::Less | Ordering::Equal) => none(),
                _ => single(f(Context::LN, c.clone())),
            },
            Context::LN => single(f(Context::EXP, c.clone())),
            Context::ASIN => {
                if cmp_term(&half_pi) == Some(Ordering::Greater)
                    || cmp_term(&-&half_pi) == Some(Ordering::Less)
                {
                    return none();
                }
                single(f(Context::SIN, c.clone()))
            }
            Context::ACOS => {
                if cmp(0) == Some(Ordering::Less) || cmp_term(&pi) == Some(Ordering::Greater) {
                    return none();
                }
                single(f(Context::COS, c.clone()))
            }
            Context::ATAN => {
                if matches!(
                    cmp_term(&half_pi),
                    Some(Ordering::Greater | Ordering::Equal)
                ) || matches!(cmp_term(&-&half_pi), Some(Ordering::Less | Ordering::Equal))
                {
                    return none();
                }
                single(f(Context::TAN, c.clone()))
            }
            Context::SINH => single(f(Context::ASINH, c.clone())),
            Context::COSH => match cmp(1) {
                Some(Ordering::Less) => none(),
                Some(Ordering::Equal) => single(int(0)),
                _ => both(f(Context::ACOSH, c.clone())),
            },
            Context::TANH => {
                if matches!(cmp(1), Some(Ordering::Greater | Ordering::Equal))
                    || matches!(cmp(-1), Some(Ordering::Less | Ordering::Equal))
                {
                    return none();
                }
                single(f(Context::ATANH, c.clone()))
            }
            Context::ASINH => single(f(Context::SINH, c.clone())),
            Context::ACOSH => match cmp(0) {
                Some(Ordering::Less) => none(),
                _ => single(f(Context::COSH, c.clone())),
            },
            Context::ATANH => single(f(Context::TANH, c.clone())),
            Context::LAMBERTW => match cmp(-1) {
                Some(Ordering::Less) => none(),
                _ => single(c * &f(Context::EXP, c.clone())),
            },
            ident if ident == Context::lambertw_m1() => match cmp(-1) {
                Some(Ordering::Greater) => none(),
                _ => single(c * &f(Context::EXP, c.clone())),
            },
            Context::ABS => match cmp(0) {
                Some(Ordering::Less) => none(),
                Some(Ordering::Equal) => single(int(0)),
                _ => both(c.clone()),
            },
            _ => Err(unsupported()),
        }
    }

    /// The solutions of `{$(alpha x + beta) e^(gamma x + delta) + r = 0$}`,
    /// `{$x = W(a) / gamma - beta / alpha$}` with `{$a = -r gamma e^(gamma beta / alpha - delta) / alpha$}`, if the
    /// expression has this form: none for `{$a < -1/e$}`, `{$W = -1$}` for `{$a = -1/e$}`, both branches
    /// `{$W_0(a)$}` and `{$W_(-1)(a)$}` for `{$-1/e < a < 0$}`, and only `{$W_0(a)$}` otherwise (or when the sign
    /// of `a` is unknown).
    fn lambert(&self, expression: &Expr, kernels: &[Kernel]) -> Option<Vec<Expr>> {
        let [kernel] = kernels else {
            return None;
        };
        let (Context::EXP, q) = unary(&kernel.term)? else {
            return None;
        };
        let s = Symbol::new("@w");
        let replaced = map_tree(expression, &|term| {
            (*term == kernel.term).then(|| variable(s))
        });
        // `{$p s + r$}`, linear in `s`
        let p = replaced.derivative(s);
        let r = subs(&replaced, s, &value(Rational::from(0)));
        if depends(&p, s) || depends(&r, self.x) {
            return None;
        }
        let x = self.x;
        let (alpha, gamma) = (p.derivative(x), q.derivative(x));
        if [&alpha, &gamma]
            .iter()
            .any(|c| c.is_zero() || depends(c, x))
        {
            return None;
        }
        let zero = value(Rational::from(0));
        let (beta, delta) = (subs(&p, x, &zero), subs(q, x, &zero));
        let shift = &beta / &alpha;
        let argument = -(&r * &gamma) * fun(Context::EXP, &gamma * &shift - delta) / &alpha;
        let solution = |w: Expr| &w / &gamma - &shift;
        let branch_point =
            constant_sign(&(&argument + &fun(Context::EXP, value(Rational::from(-1)))));
        Some(match branch_point {
            Some(Ordering::Less) => vec![],
            Some(Ordering::Equal) => vec![solution(value(Rational::from(-1)))],
            _ => {
                let mut res = vec![solution(fun(Context::LAMBERTW, argument.clone()))];
                if branch_point.is_some() && constant_sign(&argument) == Some(Ordering::Less) {
                    res.push(solution(fun(Context::lambertw_m1(), argument)));
                }
                res
            }
        })
    }
}

/// `{$g^m$}` for a kernel `g`, written as a function when `g` is an exponential (`{$e^(m u)$}`) or a power with
/// an exponent depending on the unknown (`{$b^(m u)$}`).
fn kernel_power(g: &Expr, m: &Rational) -> Expr {
    let m_term = value(m.clone());
    match (unary(g), g) {
        (Some((Context::EXP, u)), _) => fun(Context::EXP, &m_term * u),
        (_, Term::Pow(pow)) => pow.base.pow(&(&m_term * &**pow.exponant)),
        _ => g.pow(&m_term),
    }
}

/// The greatest common divisor of two rationals, `{$gcd(a, c) / "lcm"(b, d)$}` for `{$a/b$}` and `{$c/d$}`.
fn rational_gcd(a: &Rational, b: &Rational) -> Rational {
    let numerator = Integer::from(a.numerator_ref().clone().gcd(b.numerator_ref().clone()));
    let denominator = a.denominator_ref().clone().lcm(b.denominator_ref().clone());
    Rational::from(numerator) / Rational::from(denominator)
}

/// Collect the kernels of `term` in `x` (see [`Kernel`]), returning `false` if one can't be inverted.
fn collect_kernels(term: &Expr, x: Symbol, kernels: &mut Vec<Kernel>) -> bool {
    if !depends(term, x) {
        return true;
    }
    let mut push = |term: &Expr, factor: Expr, base: Expr, exponent: Rational| {
        if !kernels.iter().any(|kernel| kernel.term == *term) {
            kernels.push(Kernel {
                term: term.clone(),
                factor,
                base,
                exponent,
            });
        }
        true
    };
    match term {
        Term::Value(_) | Term::Symbol(_) => true,
        Term::Add(add) => add.iter().all(|t| collect_kernels(t, x, kernels)),
        Term::Mul(mul) => mul.iter().all(|t| collect_kernels(t, x, kernels)),
        Term::Pow(pow) => match &**pow.exponant {
            // Polynomials
            Term::Value(e) if e.value.denominator_ref() == &1u32 && e.value > 0 => {
                collect_kernels(&pow.base, x, kernels)
            }
            Term::Value(e) => push(term, one(), (*pow.base).clone(), e.value.clone()),
            exponent if !depends(&pow.base, x) => {
                // `{$b^(n u + c) = b^c (b^u)^n$}`
                let (c, exponent) = split_constant(exponent, x);
                let (n, u) = split_coefficient(&exponent);
                push(term, pow.base.pow(&c), pow.base.pow(&u), n)
            }
            _ => false,
        },
        Term::Fun(_) => match unary(term) {
            Some((Context::EXP, u)) => {
                // `{$e^(n u + c) = e^c (e^u)^n$}`
                let (c, u) = split_constant(u, x);
                let (n, u) = split_coefficient(&u);
                push(term, fun(Context::EXP, c), fun(Context::EXP, u), n)
            }
            Some(_) => push(term, one(), term.clone(), Rational::from(1)),
            None => false,
        },
    }
}

/// `u` as `{$c + v$}` with `c` its terms free of `x`.
fn split_constant(u: &Expr, x: Symbol) -> (Expr, Expr) {
    match u {
        Term::Add(add) => {
            let (constant, rest): (Vec<_>, Vec<_>) = add.iter().partition(|t| !depends(t, x));
            let sum = |terms: Vec<&Expr>| {
                terms
                    .into_iter()
                    .fold(value(Rational::from(0)), |a, t| a + t)
            };
            (sum(constant), sum(rest))
        }
        _ => (value(Rational::from(0)), u.clone()),
    }
}

/// The constant 1.
fn one() -> Expr {
    value(Rational::from(1))
}

/// `u` as `{$n v$}` with `n` its rational coefficient.
fn split_coefficient(u: &Expr) -> (Rational, Expr) {
    match u {
        Term::Mul(mul) if mul.coefficient != 0 => {
            (mul.coefficient.clone(), u / &value(mul.coefficient.clone()))
        }
        _ => (Rational::from(1), u.clone()),
    }
}

/// The roots of the polynomial `p` in `x`, `None` if they can't be found or every value is a root.
fn roots(p: &Expr, x: Symbol) -> Option<Vec<Expr>> {
    let solution = R
        .solve_for(&[Equation::new(p.clone(), value(Rational::from(0)))], &[x])
        .ok()?;
    match solution {
        Solution::NoSolution => Some(vec![]),
        Solution::Assignments(assignments) if assignments.is_empty() => None,
        Solution::Assignments(assignments) => {
            Some(assignments.into_iter().map(|(_, value)| value).collect())
        }
        Solution::Alternatives(branches) => Some(
            branches
                .into_iter()
                .filter_map(|assignments| assignments.into_iter().next().map(|(_, value)| value))
                .collect(),
        ),
    }
}
