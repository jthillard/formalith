//! Equations `{$a sin u + b sin v = 0$}` with `{$a = plus.minus b$}` and unrelated angles `u` and `v`, like
//! `{$sin x = cos x^2$}`, solved by the sum-to-product formulas (`{$cos v = sin(v + pi/2)$}`):
//! `{$sin u + sin v = 2 sin((u + v)/2) cos((u - v)/2)$}` and `{$sin u - sin v = 2 cos((u + v)/2) sin((u - v)/2)$}`.

use malachite::Rational;

use crate::{
    context::Context,
    field::real::expr::{Expr, depends, fun, unary, value, variable},
    term::{Normalize, Term},
};

use super::{Inverter, SolveError};

impl Inverter {
    /// The values of the unknown such that `expression = 0`, if it is `{$a f(u) + b g(v)$}` with `f` and `g` being
    /// `sin` or `cos` and `{$a = plus.minus b$}` constants. `None` if it doesn't have this form.
    pub(super) fn unrelated_angles(
        &self,
        expression: &Expr,
        depth: usize,
    ) -> Option<Result<Vec<Expr>, SolveError>> {
        let Term::Add(add) = expression else {
            return None;
        };
        let [t1, t2] = add.iter().collect::<Vec<_>>()[..] else {
            return None;
        };
        let (a, u) = self.sine(t1)?;
        let (b, v) = self.sine(t2)?;
        let half = |w: Expr| w / value(Rational::from(2));
        let (sum, difference) = (half(&u + &v), half(u - v));
        let factors = match (a / b).normalize() {
            Term::Value(ratio) if ratio.value == 1 => {
                [fun(Context::SIN, sum), fun(Context::COS, difference)]
            }
            Term::Value(ratio) if ratio.value == -1 => {
                [fun(Context::COS, sum), fun(Context::SIN, difference)]
            }
            _ => return None,
        };
        let mut res = vec![];
        for factor in factors {
            match self.solve(&factor, depth + 1) {
                Ok(values) => res.extend(values),
                Err(error) => return Some(Err(error)),
            }
        }
        Some(Ok(res))
    }

    /// The term `t` as `{$a sin w$}` with a constant `a`, `{$a cos w$}` being `{$a sin(w + pi/2)$}`.
    fn sine(&self, t: &Expr) -> Option<(Expr, Expr)> {
        let factors: Vec<&Expr> = match t {
            Term::Mul(mul) => mul.iter().collect(),
            _ => vec![t],
        };
        let [kernel] = factors
            .into_iter()
            .filter(|factor| depends(factor, self.x))
            .collect::<Vec<_>>()[..]
        else {
            return None;
        };
        let angle = match unary(kernel)? {
            (Context::SIN, w) => w.clone(),
            (Context::COS, w) => w + &(variable(Context::PI) / value(Rational::from(2))),
            _ => return None,
        };
        Some(((t / kernel).normalize(), angle))
    }
}
