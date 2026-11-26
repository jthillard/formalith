//! The differential equation of an expression in `w`, by closure properties of D-finite functions.
//!
//! Rational functions, algebraic functions (nested radicals, in the tower of [`algebraic`]), `{$exp(u)$}`,
//! `{$sin(u)$}`, `{$cos(u)$}`, `{$sinh(u)$}`, `{$cosh(u)$}` of rational `u`, constant powers of functions of order 1
//! (like `{$(1 + w)^a$}`), integrals of D-finite functions (`atan`, `asin`, `ln`, `erf`...), sums and products.
//! Every rule gives an exact operator, and the functions it accepts are meromorphic at `{$w = 0$}`: non-integer
//! powers need a base which is analytic and non-zero there.

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    field::real::expr::{Expr, depends, unary},
    limit::{Direction, series_terms},
    polynom::{dense::Coefficient, fraction::Elem},
    sum::field::Params,
    term::Term,
};

use super::{
    algebraic,
    ore::{Kind, MAX_ORDER, Operator},
    ratfun::RatFun,
};

/// Maximum depth of the recursion on the expression.
const MAX_DEPTH: usize = 16;

/// The functions defined as integrals of D-finite functions, whose derivative doesn't contain themselves.
const INTEGRALS: [Symbol; 10] = [
    Context::ATAN,
    Context::ASIN,
    Context::ACOS,
    Context::ASINH,
    Context::ACOSH,
    Context::ATANH,
    Context::LN,
    Context::ERF,
    Context::ERFI,
    Context::SI,
];

/// A differential operator annihilating `f`, a function of `w`, its coefficients rational functions of `w`.
pub fn annihilator(f: &Expr, w: Symbol, params: &mut Params) -> Option<Operator> {
    annihilator_at(f, w, params, 0).filter(|op| op.order() <= MAX_ORDER)
}

/// The rational function `f` of `w`, if it is one.
pub fn rational(f: &Expr, w: Symbol, params: &mut Params) -> Option<RatFun> {
    let (num, den) = params.rational(f, w)?;
    Some(RatFun { num, den })
}

fn annihilator_at(f: &Expr, w: Symbol, params: &mut Params, depth: usize) -> Option<Operator> {
    if depth > MAX_DEPTH {
        return None;
    }
    if !depends(f, w) {
        return Some(Operator::first_order(Kind::Differential, &RatFun::zero()));
    }
    if let Some(r) = rational(f, w, params) {
        // `{$r partial - r'$}`
        return Some(if r.is_zero() {
            Operator::first_order(Kind::Differential, &RatFun::zero())
        } else {
            Operator::first_order(Kind::Differential, &r.derivative().divide(&r))
        });
    }
    if let Some(op) = algebraic::annihilator(f, w, params) {
        return Some(op);
    }
    let recurse = |t: &Expr, params: &mut Params| annihilator_at(t, w, params, depth + 1);
    match f {
        Term::Add(add) => {
            let mut res: Option<Operator> = None;
            for t in add {
                let op = recurse(t, params)?;
                res = Some(match res {
                    None => op,
                    Some(res) => res.lclm(&op)?,
                });
            }
            res
        }
        Term::Mul(mul) => {
            let mut res: Option<Operator> = None;
            for t in mul.iter().filter(|t| depends(t, w)) {
                let op = recurse(t, params)?;
                res = Some(match res {
                    None => op,
                    Some(res) => res.symmetric_product(&op)?,
                });
            }
            res
        }
        Term::Pow(pow) => {
            let (base, exponent) = (&*pow.base, &**pow.exponant);
            if depends(exponent, w) {
                return None;
            }
            if let Term::Value(e) = exponent
                && e.value.denominator_ref() == &1u32
                && e.value > 0
            {
                // `{$g^n$}` as a product
                let n = usize::try_from(&e.value).ok().filter(|&n| n <= 4)?;
                let op = recurse(base, params)?;
                if op.order() == 1 {
                    return Some(power_of_first_order(&op, &Elem::rational(e.value.clone())));
                }
                let mut res = op.clone();
                for _ in 1..n {
                    res = res.symmetric_product(&op)?;
                }
                return Some(res);
            }
            let op = recurse(base, params)?;
            if op.order() != 1 {
                return None;
            }
            let is_integer =
                matches!(exponent, Term::Value(e) if e.value.denominator_ref() == &1u32);
            if !is_integer && !analytic_non_zero(base, w) {
                return None;
            }
            let c = params.elem(exponent)?;
            Some(power_of_first_order(&op, &c))
        }
        Term::Fun(_) => {
            let (ident, u) = unary(f)?;
            let u = rational(u, w, params)?;
            let du = u.derivative();
            match ident {
                // `{$partial - u'$}`
                Context::EXP => Some(Operator::first_order(Kind::Differential, &du)),
                // `{$u' f'' - u'' f' plus.minus u'^3 f = 0$}`
                Context::SIN | Context::COS | Context::SINH | Context::COSH => {
                    let cube = du.times(&du).times(&du);
                    let cube = if matches!(ident, Context::SIN | Context::COS) {
                        cube
                    } else {
                        cube.negate()
                    };
                    Operator::new(Kind::Differential, vec![cube, du.derivative().negate(), du])
                }
                ident if INTEGRALS.contains(&ident) => {
                    // `{$f' = g$}`, so `{$L_g partial f = 0$}`
                    let g = f.derivative(w);
                    Some(recurse(&g, params)?.times_generator())
                }
                _ => None,
            }
        }
        Term::Value(_) | Term::Symbol(_) => None,
    }
}

/// `{$partial - c rho$}`, the operator of `{$g^c$}` when `{$g' = rho g$}`.
fn power_of_first_order(op: &Operator, c: &Elem) -> Operator {
    // `{$a_1 g' + a_0 g = 0$}`, so `{$rho = -a_0 / a_1$}`
    let rho = op.coefficients[0].negate().divide(&op.coefficients[1]);
    Operator::first_order(Kind::Differential, &rho.times(&RatFun::constant(c.clone())))
}

/// Whether `g` is analytic and non-zero at `{$w = 0^+$}`: its series starts with a non-zero constant.
pub(super) fn analytic_non_zero(g: &Expr, w: Symbol) -> bool {
    let zero = Term::zero(crate::field::real::R);
    matches!(
        series_terms(g, w, &zero, &Rational::from(1), Direction::Right),
        Ok(series) if series.terms.first().is_some_and(|(e, _)| *e == 0)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        field::real::{
            R,
            approx::approximate_fixed,
            expr::{subs, value},
        },
        parse, symbol,
    };
    use malachite::base::num::arithmetic::traits::Abs;

    /// `{$L f$}`, with the coefficients of `L` as expressions.
    fn apply(op: &Operator, f: &Expr, w: Symbol, params: &Params) -> Expr {
        let mut derivative = f.clone();
        let mut res = Term::zero(crate::field::real::R);
        for c in &op.coefficients {
            let wt = crate::field::real::expr::variable(w);
            let c = params.poly_to_term(&c.num, &wt) / params.poly_to_term(&c.den, &wt);
            res += c * &derivative;
            derivative = derivative.derivative(w);
        }
        res
    }

    #[test]
    fn annihilators_annihilate() {
        let w = symbol!("w");
        for f in [
            "w^3 + 1/(1 - w)",
            "exp(2*w)",
            "sin(w^2)",
            "cosh(w)",
            "atan(w)",
            "asin(w)",
            "erf(w)",
            "ln(1 + w)",
            "(1 + w)^a",
            "sqrt(1 - w^2)",
            "exp(w)*sin(w)",
            "sin(w) + exp(w)",
            "cos(w)^2",
            "Si(w)",
            "sqrt(1 + sqrt(1 + w))",
            "1/sqrt(1 + sqrt(1 + w))",
            "(1 + w)^(1/3) + sqrt(1 - w)",
            "sqrt(1 + w)*(1 + w^2)^(1/3)",
            "exp(w)*sqrt(1 + sqrt(1 + w))",
        ] {
            let f = parse!(f, R);
            let mut params = Params::default();
            let op = annihilator(&f, w, &mut params).unwrap_or_else(|| panic!("{f}"));
            let res = apply(&op, &f, w, &params);
            // At sample points, `a` being 2
            let res = subs(&res, symbol!("a"), &value(Rational::from(2)));
            for (p, q) in [(1, 3), (2, 7)] {
                let at = subs(&res, w, &value(Rational::from_signeds(p, q)));
                let v = approximate_fixed(&at, 128).unwrap_or_else(|| panic!("{f}: {at}"));
                assert!(
                    v.abs() < Rational::from_signeds(1, 1i64 << 60),
                    "{f}: {res}"
                );
            }
        }
    }

    #[test]
    fn non_holonomic_functions() {
        let w = symbol!("w");
        for f in ["tan(w)", "exp(sin(w))", "sqrt(w)", "1/cos(w)", "gamma(w)"] {
            let mut params = Params::default();
            assert!(annihilator(&parse!(f, R), w, &mut params).is_none(), "{f}");
        }
    }
}
