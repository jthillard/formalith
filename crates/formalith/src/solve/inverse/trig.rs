//! Equations in `{$sin$}`, `{$cos$}` and `{$tan$}` of multiples of a common angle, like `{$sin x = cos x$}` or
//! `{$cos 2x = sin x$}`.
//!
//! The functions of `{$n_i u + c_i$}` are written as polynomials in `{$S = sin v$}` and `{$C = cos v$}`, `v` being
//! the largest common divisor `{$m u$}` of the angles, giving an equation `{$P(S, C) = 0$}` solved with
//! `{$S^2 + C^2 = 1$}`: as a polynomial in `S` (or `C`) when `P` only has even powers of the other one, as a
//! polynomial in `{$tan v$}` when it is homogeneous (`{$S^2 + C^2$}` raising the degree of the lower terms), as
//! `{$R sin(v + phi) = c$}` when it is linear, and otherwise with `{$t = tan(v / 2)$}`.

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    field::real::{
        R,
        expr::{
            Expr, arg, constant_sign, depends, fun, int, map_tree, sqrt, subs, unary, value,
            variable,
        },
    },
    term::{Expand, Fun, Normalize, Term},
};

use super::{
    Inverter, Kernel, SolveError, plain, rational_gcd, roots, split_coefficient, split_constant,
};

/// Largest multiple of the common angle written as a polynomial.
const MAX_MULTIPLE: u32 = 12;

/// A monomial `{$a S^i C^j$}` of a polynomial in `S` and `C`.
struct Monomial {
    coefficient: Expr,
    s: u32,
    c: u32,
}

/// An equation `{$f(w) = "value"$}` equivalent to some of the solutions, with the points `{$(S, C)$}` of the
/// common angle where it holds, at which the denominator of the equation must not vanish.
struct Branch {
    ident: Symbol,
    /// The angle `w` is `{$"scale" v + "shift"$}`.
    scale: Rational,
    shift: Expr,
    value: Expr,
    points: Vec<(Expr, Expr)>,
}

impl Inverter {
    /// The values of the unknown such that `expression = 0`, if its kernels are `sin`, `cos` and `tan` of
    /// rational multiples of a common angle, plus constants. `None` if it doesn't have this form or can't be
    /// solved this way.
    pub(super) fn trigonometric(
        &self,
        expression: &Expr,
        kernels: &[Kernel],
        depth: usize,
    ) -> Option<Result<Vec<Expr>, SolveError>> {
        let x = self.x;
        // Each kernel as `{$n u + c$}`, with the same `u`
        let mut angle: Option<Expr> = None;
        let mut multiples = vec![];
        for kernel in kernels {
            let (Context::SIN | Context::COS | Context::TAN, argument) = unary(&kernel.term)?
            else {
                return None;
            };
            let (_, rest) = split_constant(argument, x);
            let (n, u) = split_coefficient(&rest);
            if angle.as_ref().is_some_and(|angle| *angle != u) {
                return None;
            }
            angle = Some(u);
            multiples.push(n);
        }
        let u = angle?;
        let m = multiples.into_iter().reduce(|a, b| rational_gcd(&a, &b))?;
        let (s, c) = (Symbol::new("@S"), Symbol::new("@C"));
        let (sv, cv) = (variable(s), variable(c));
        // `{$sin(N v)$}` and `{$cos(N v)$}` for `{$0 <= N <= "MAX_MULTIPLE"$}`
        let mut multiple = vec![(int(0), int(1))];
        for _ in 0..MAX_MULTIPLE {
            let (sn, cn) = multiple.last().expect("There is a first multiple");
            let next = (
                (sn * &cv + cn * &sv).expand(),
                (cn * &cv - sn * &sv).expand(),
            );
            multiple.push(next);
        }
        let failed = std::cell::Cell::new(false);
        // The cosines dividing `tan`, collected before normalization can cancel them (`{$tan x cos x$}`)
        let denominators = std::cell::RefCell::new(vec![]);
        let replaced = map_tree(expression, &|term| {
            let (ident @ (Context::SIN | Context::COS | Context::TAN), argument) = unary(term)?
            else {
                return None;
            };
            if !depends(argument, x) {
                return None;
            }
            let (shift, rest) = split_constant(argument, x);
            let (n, _) = split_coefficient(&rest);
            let n = n / &m;
            let Some((sin, cos)) = i64::try_from(&n).ok().and_then(|n| {
                let (sin, cos) = multiple.get(usize::try_from(n.unsigned_abs()).ok()?)?;
                Some((if n < 0 { -sin } else { sin.clone() }, cos.clone()))
            }) else {
                failed.set(true);
                return Some(term.clone());
            };
            // The addition formulas with the constant shift
            let (sin_c, cos_c) = (fun(Context::SIN, shift.clone()), fun(Context::COS, shift));
            let sin_shifted = &sin * &cos_c + &cos * &sin_c;
            let cos_shifted = cos * cos_c - sin * sin_c;
            Some(match ident {
                Context::SIN => sin_shifted,
                Context::COS => cos_shifted,
                _ => {
                    denominators.borrow_mut().push(cos_shifted.clone());
                    sin_shifted / cos_shifted
                }
            })
        });
        if failed.get() {
            return None;
        }
        let (numerator, _) = replaced.normalize().as_fraction(true);
        let numerator = numerator.expand();
        let denominator = denominators
            .into_inner()
            .into_iter()
            .fold(int(1), |res, d| res * d);
        if depends(&numerator, x) {
            return None;
        }
        let monomials = monomials(&numerator, s, c)?;
        let Some(branches) = branches(&monomials, s) else {
            return Some(Err(SolveError::Unsolvable(plain(expression))));
        };
        let v = value(m) * u;
        let mut res = vec![];
        for branch in branches {
            if !depends(&denominator, s) && !depends(&denominator, c) {
                // No point to exclude
            } else {
                let vanishes: Vec<bool> = branch
                    .points
                    .iter()
                    .map(|(sp, cp)| {
                        let at = subs(&subs(&denominator, s, sp), c, cp);
                        at.expand().is_zero()
                            || constant_sign(&at) == Some(std::cmp::Ordering::Equal)
                    })
                    .collect();
                if vanishes.iter().all(|v| *v) {
                    continue;
                }
                if vanishes.iter().any(|v| *v) {
                    return None;
                }
            }
            let angle = value(branch.scale) * &v + branch.shift;
            let kernel = raw_fun(branch.ident, angle);
            let pairs = match self.invert(&kernel, &branch.value, depth) {
                Ok(pairs) => pairs,
                Err(error) => return Some(Err(error)),
            };
            for (lhs, rhs) in pairs {
                match self.solve(&(lhs - rhs), depth + 1) {
                    Ok(values) => res.extend(values),
                    Err(error) => return Some(Err(error)),
                }
            }
        }
        Some(Ok(res))
    }
}

/// The function `ident(arg)`, not normalized, so that `{$sin(v + pi/4)$}` stays a sine for the inversion.
fn raw_fun(ident: Symbol, arg: Expr) -> Expr {
    Term::Fun(Box::new(Fun::new(ident, vec![arg], R)))
}

/// The monomials of the expanded polynomial `p` in `s` and `c`, `None` if it isn't one.
fn monomials(p: &Expr, s: Symbol, c: Symbol) -> Option<Vec<Monomial>> {
    let terms: Vec<&Expr> = match p {
        Term::Add(add) => add.iter().collect(),
        _ if p.is_zero() => vec![],
        _ => vec![p],
    };
    let degree = |factor: &Expr| -> Option<(u32, u32, bool)> {
        let (base, exponent) = match factor {
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(e) => (&*pow.base, u32::try_from(&e.value).ok()),
                _ => (&*pow.base, None),
            },
            _ => (factor, Some(1)),
        };
        match base {
            Term::Symbol(symbol) if symbol.symbol() == s => Some((exponent?, 0, true)),
            Term::Symbol(symbol) if symbol.symbol() == c => Some((0, exponent?, true)),
            _ if depends(factor, s) || depends(factor, c) => None,
            _ => Some((0, 0, false)),
        }
    };
    terms
        .into_iter()
        .map(|term| {
            let factors: Vec<&Expr> = match term {
                Term::Mul(mul) => mul.iter().collect(),
                _ => vec![term],
            };
            let mut coefficient = match term {
                Term::Mul(mul) => value(mul.coefficient.clone()),
                _ => int(1),
            };
            let (mut i, mut j) = (0, 0);
            for factor in factors {
                let (di, dj, power) = degree(factor)?;
                if power {
                    i += di;
                    j += dj;
                } else {
                    coefficient *= factor;
                }
            }
            Some(Monomial {
                coefficient,
                s: i,
                c: j,
            })
        })
        .collect()
}

/// `{$sum a S^i C^j$}` with `S` and `C` replaced by `sin` and `cos`, for the monomials `{$a S^i C^j$}`.
fn evaluate(monomials: &[Monomial], sin: &Expr, cos: &Expr) -> Expr {
    monomials.iter().fold(int(0), |res, monomial| {
        res + monomial.coefficient.clone()
            * sin.pow(&value(Rational::from(monomial.s)))
            * cos.pow(&value(Rational::from(monomial.c)))
    })
}

/// The equations in `sin`, `cos` or `tan` of the common angle equivalent to `{$P(S, C) = 0$}`, `P` being given by
/// its monomials, `t` being a free symbol for the polynomials in one function. `None` when the roots of a
/// polynomial can't be found.
fn branches(monomials: &[Monomial], t: Symbol) -> Option<Vec<Branch>> {
    let zero = int(0);
    let one = int(1);
    let tv = variable(t);
    let pow = |base: &Expr, n: u32| base.pow(&value(Rational::from(n)));
    // The points of the angles where `{$sin v = s$}` or `{$cos v = c$}`
    let sin_branch = |s: Expr| {
        let other = sqrt(&(&one - &(&s * &s)));
        Branch {
            ident: Context::SIN,
            scale: Rational::from(1),
            shift: zero.clone(),
            points: vec![(s.clone(), other.clone()), (s.clone(), -other)],
            value: s,
        }
    };
    let cos_branch = |c: Expr| {
        let other = sqrt(&(&one - &(&c * &c)));
        Branch {
            ident: Context::COS,
            scale: Rational::from(1),
            shift: zero.clone(),
            points: vec![(other.clone(), c.clone()), (-other, c.clone())],
            value: c,
        }
    };
    if monomials.is_empty() {
        return None;
    }
    // Parity: `{$P = A(S) + C B(S)$}`, with `{$C^2 = 1 - S^2$}`
    for swap in [false, true] {
        let (mut even, mut odd) = (zero.clone(), zero.clone());
        for monomial in monomials {
            let (i, j) = if swap {
                (monomial.c, monomial.s)
            } else {
                (monomial.s, monomial.c)
            };
            let term =
                monomial.coefficient.clone() * pow(&tv, i) * pow(&(&one - &(&tv * &tv)), j / 2);
            if j % 2 == 0 {
                even += term;
            } else {
                odd += term;
            }
        }
        let (even, odd) = (even.expand(), odd.expand());
        let branch = |r: Expr| if swap { cos_branch(r) } else { sin_branch(r) };
        if odd.is_zero() {
            if even.is_zero() {
                return None;
            }
            return Some(roots(&even, t)?.into_iter().map(branch).collect());
        }
        if even.is_zero() {
            // The other function vanishes, or `{$B = 0$}`
            let mut res: Vec<Branch> = roots(&odd, t)?.into_iter().map(branch).collect();
            res.push(if swap {
                sin_branch(zero.clone())
            } else {
                cos_branch(zero.clone())
            });
            return Some(res);
        }
    }
    let degree = monomials.iter().map(|m| m.s + m.c).max()?;
    // Homogeneous: `{$P(S, C) = C^d Q(tan v)$}`
    if monomials.iter().all(|m| (m.s + m.c) % 2 == degree % 2) {
        let q = monomials
            .iter()
            .fold(zero.clone(), |res, m| {
                res + m.coefficient.clone()
                    * pow(&tv, m.s)
                    * pow(&(&tv * &tv + &one), (degree - m.s - m.c) / 2)
            })
            .expand();
        if q.is_zero() {
            return None;
        }
        let mut res: Vec<Branch> = roots(&q, t)?
            .into_iter()
            .map(|r| Branch {
                ident: Context::TAN,
                scale: Rational::from(1),
                shift: zero.clone(),
                points: vec![(r.clone(), one.clone())],
                value: r,
            })
            .collect();
        // `{$C = 0$}` when the coefficient of `{$S^d$}` vanishes
        let leading = monomials
            .iter()
            .filter(|m| m.c == 0)
            .fold(zero.clone(), |res, m| res + &m.coefficient)
            .expand();
        if leading.is_zero() {
            res.push(cos_branch(zero.clone()));
        }
        return Some(res);
    }
    // Linear: `{$a S + b C + c = R sin(v + phi) + c$}`
    if degree == 1 {
        let coefficient = |i: u32, j: u32| {
            monomials
                .iter()
                .filter(|m| m.s == i && m.c == j)
                .fold(zero.clone(), |res, m| res + &m.coefficient)
        };
        let (a, b, c) = (coefficient(1, 0), coefficient(0, 1), coefficient(0, 0));
        if let Some(phi) = arg(&a, &b) {
            let r = sqrt(&(&a * &a + &b * &b));
            let s = -c / &r;
            let other = sqrt(&(&one - &(&s * &s)));
            // `{$v = w - phi$}` with `{$sin w = s$}`
            let point = |cw: &Expr| ((&s * &a - cw * &b) / &r, (cw * &a + &s * &b) / &r);
            return Some(vec![Branch {
                ident: Context::SIN,
                scale: Rational::from(1),
                shift: phi,
                points: vec![point(&other), point(&-&other)],
                value: s,
            }]);
        }
    }
    // `{$t = tan(v/2)$}`, `{$S = 2t/(1 + t^2)$}`, `{$C = (1 - t^2)/(1 + t^2)$}`
    let square = &tv * &tv;
    let q = monomials
        .iter()
        .fold(zero.clone(), |res, m| {
            res + m.coefficient.clone()
                * pow(&(int(2) * &tv), m.s)
                * pow(&(&one - &square), m.c)
                * pow(&(&one + &square), degree - m.s - m.c)
        })
        .expand();
    if q.is_zero() {
        return None;
    }
    let mut res: Vec<Branch> = roots(&q, t)?
        .into_iter()
        .map(|r| {
            let d = &one + &(&r * &r);
            Branch {
                ident: Context::TAN,
                scale: Rational::from_signeds(1, 2),
                shift: zero.clone(),
                points: vec![(int(2) * &r / &d, (&one - &(&r * &r)) / &d)],
                value: r,
            }
        })
        .collect();
    // `{$v = pi$}`, where `t` is infinite
    if evaluate(monomials, &zero, &-&one).expand().is_zero() {
        res.push(Branch {
            ident: Context::COS,
            scale: Rational::from(1),
            shift: zero.clone(),
            points: vec![(zero.clone(), -&one)],
            value: -&one,
        });
    }
    Some(res)
}
