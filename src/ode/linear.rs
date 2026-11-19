//! Linear equations with constant coefficients `{$sum_k a_k y^((k)) = g(x)$}`.
//!
//! A root `r` of multiplicity `m` of the characteristic polynomial `{$sum_k a_k r^k$}` gives the solutions
//! `{$x^j e^(r x)$}` for `{$j < m$}`, written `{$x^j e^(u x) cos(v x)$}` and `{$x^j e^(u x) sin(v x)$}` for a pair of
//! complex roots `{$u plus.minus i v$}`. A particular solution `{$sum_i u_i y_i$}` is found by variation of
//! parameters: `{$sum_i u_i' y_i^((k)) = 0$}` for `{$k < n - 1$}` and `{$sum_i u_i' y_i^((n - 1)) = g / a_n$}`.

use std::cmp::Ordering;

use malachite::{Rational, base::num::basic::traits::Zero};

use crate::{
    context::{Context, Symbol},
    field::{
        complex::C,
        real::{
            R,
            expr::{Expr, Real, constant_sign, depends, fun, subs, value, variable, zero},
        },
    },
    integrate::{poly::Poly, rational},
    solve::{Equation, Solution, Solve, polynomial::PolynomialRoots},
    term::{Expand, Term},
};

use super::{OdeBranch, OdeError, OdeResult, integrate, placeholder, simplify_trigonometric, tidy};

/// Solve the linear equation of order `n` with constant coefficients `{$e = 0$}`, written with the placeholders
/// `@y0, ..., @y<n>`, with the integration `constants`.
pub(super) fn solve(
    e: &Expr,
    n: usize,
    x: Symbol,
    constants: &[Symbol],
) -> OdeResult<Vec<OdeBranch<Real>>> {
    let unsupported = || {
        OdeError::Unsupported(
            "only linear equations with constant coefficients can be solved above the first order"
                .to_owned(),
        )
    };
    let ys: Vec<_> = (0..=n).map(placeholder).collect();
    let e = e.expand();
    let coefficients = ys
        .iter()
        .map(|&y| match e.derivative(y).expand() {
            Term::Value(a) => Some(a.value),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(unsupported)?;
    // `{$e = sum_k a_k y^((k)) - g$}`
    let rest = ys.iter().fold(e.clone(), |t, y| subs(&t, *y, &zero()));
    let linear_part = ys
        .iter()
        .zip(&coefficients)
        .fold(zero(), |s, (y, a)| s + value(a.clone()) * variable(*y));
    if ys.iter().any(|y| depends(&rest, *y)) || !(e - linear_part - rest.clone()).expand().is_zero()
    {
        return Err(unsupported());
    }
    let lead = coefficients[n].clone();
    if lead == Rational::ZERO {
        return Err(unsupported());
    }
    let basis = basis(&Poly::new(coefficients), x)?;
    let mut res = basis
        .iter()
        .zip(constants)
        .fold(zero(), |s, (y, c)| s + variable(*c) * y);
    if !rest.is_zero() {
        res += particular(&basis, &(-rest / value(lead)), x)?;
    }
    Ok(vec![OdeBranch::Explicit(tidy(&res))])
}

/// A basis of the solutions of the homogeneous equation with the characteristic polynomial `p`.
fn basis(p: &Poly, x: Symbol) -> OdeResult<Vec<Expr>> {
    let unsolvable = || {
        OdeError::Unsupported(format!(
            "can't find the roots of the characteristic polynomial `{}`",
            crate::solve::plain(&p.to_term(Symbol::new("r")))
        ))
    };
    let r = Symbol::new("@r");
    let complex = |c: &Rational| Term::constant([c.clone(), Rational::ZERO], C);
    let x_term = variable(x);
    let mut basis = vec![];
    for (i, part) in p.square_free().iter().enumerate() {
        if part.degree() == 0 {
            continue;
        }
        for q in rational::factor(part, r) {
            let coefficients: Vec<_> = q.coefficients().iter().map(complex).collect();
            let roots = <C<R<Rational>> as PolynomialRoots>::roots(&coefficients)
                .filter(|roots| roots.len() == q.degree())
                .ok_or_else(unsolvable)?;
            for root in &roots {
                let (u, v) = rational::split(root).ok_or_else(unsolvable)?;
                let sign = constant_sign(&v).ok_or_else(unsolvable)?;
                for j in 0..=i {
                    let power = x_term.pow(&value(Rational::from(j)));
                    let exp = power * fun(Context::EXP, u.clone() * &x_term);
                    match sign {
                        Ordering::Less => {}
                        Ordering::Equal => basis.push(exp),
                        Ordering::Greater => {
                            basis.push(&exp * &fun(Context::COS, v.clone() * &x_term));
                            basis.push(exp * fun(Context::SIN, v.clone() * &x_term));
                        }
                    }
                }
            }
        }
    }
    if basis.len() != p.degree() {
        return Err(unsolvable());
    }
    Ok(basis)
}

/// A particular solution of `{$sum_k a_k y^((k)) = a_n g$}` by variation of parameters, `basis` being a basis of
/// the solutions of the homogeneous equation.
fn particular(basis: &[Expr], g: &Expr, x: Symbol) -> OdeResult<Expr> {
    let n = basis.len();
    let us: Vec<_> = (0..n).map(|i| Symbol::new(format!("@u{i}"))).collect();
    let mut derivatives = basis.to_vec();
    let mut equations = vec![];
    for k in 0..n {
        let lhs = us
            .iter()
            .zip(&derivatives)
            .fold(zero(), |s, (u, y)| s + variable(*u) * y);
        let rhs = if k == n - 1 { g.clone() } else { zero() };
        equations.push(Equation::new(lhs, rhs));
        derivatives = derivatives.iter().map(|y| y.derivative(x)).collect();
    }
    let failed =
        || OdeError::Unsupported("can't find a particular solution of the equation".to_owned());
    let Ok(Solution::Assignments(assignments)) = R.solve_for(&equations, &us) else {
        return Err(failed());
    };
    let mut res = zero();
    for (u, y) in us.iter().zip(basis) {
        let (_, derivative) = assignments
            .iter()
            .find(|(symbol, _)| symbol == u)
            .ok_or_else(failed)?;
        // Quotients by the Wronskian, which often needs `{$sin^2 + cos^2 = 1$}`
        let derivative = fun(Context::SIMPLIFY, derivative.clone());
        res += integrate(&derivative, x)? * y;
    }
    // Terms which are solutions of the homogeneous equation are absorbed by the constants
    let res = simplify_trigonometric(&res).unwrap_or(res).expand();
    let terms = match &res {
        Term::Add(add) => add.iter().cloned().collect(),
        _ => vec![res.clone()],
    };
    Ok(terms
        .into_iter()
        .filter(|term| {
            !basis
                .iter()
                .any(|y| matches!((term / y).expand(), Term::Value(_)))
        })
        .fold(zero(), |s, term| s + term))
}
