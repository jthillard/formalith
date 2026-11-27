//! Linear equations with constant coefficients `{$sum_k a_k y^((k)) = g(x)$}`.
//!
//! A root `r` of multiplicity `m` of the characteristic polynomial `{$sum_k a_k r^k$}` gives the solutions
//! `{$x^j e^(r x)$}` for `{$j < m$}`, written `{$x^j e^(u x) cos(v x)$}` and `{$x^j e^(u x) sin(v x)$}` for a pair of
//! complex roots `{$u plus.minus i v$}`. A particular solution is found by undetermined coefficients when the
//! right side is a sum of terms `{$q(x) e^(a x) cos(b x)$}` and `{$q(x) e^(a x) sin(b x)$}`, otherwise as
//! `{$sum_i u_i y_i$}` by variation of parameters: `{$sum_i u_i' y_i^((k)) = 0$}` for `{$k < n - 1$}` and `{$sum_i u_i' y_i^((n - 1)) = g / a_n$}`.

use std::cmp::Ordering;

use malachite::{
    Rational,
    base::num::basic::traits::{One, Zero},
};

use crate::{
    context::{Context, Symbol},
    field::{
        complex::C,
        real::{
            R,
            expr::{Expr, Real, constant_sign, depends, fun, subs, unary, value, variable, zero},
        },
    },
    integrate::{
        factors,
        poly::{Coefficient, Poly},
        rational,
    },
    solve::{Equation, Solution, Solve, polynomial::PolynomialRoots},
    term::{Expand, Term},
};

use super::{OdeBranch, OdeError, OdeResult, integrate, placeholder, simplify_trigonometric, tidy};

/// The coefficients `{$a_0, ..., a_n$}` and the rest `{$-g$}` of the linear equation of order `n`
/// `{$e = sum_k a_k y^((k)) - g = 0$}`, written with the placeholders `@y0, ..., @y<n>`, the coefficients and the
/// rest being free of them.
pub(super) fn linear_form(e: &Expr, n: usize) -> OdeResult<(Vec<Expr>, Expr)> {
    let unsupported = || {
        OdeError::Unsupported(
            "only linear equations can be solved above the first order".to_owned(),
        )
    };
    let ys: Vec<_> = (0..=n).map(placeholder).collect();
    let e = e.expand();
    let coefficients: Vec<_> = ys.iter().map(|&y| e.derivative(y).expand()).collect();
    let rest = ys.iter().fold(e.clone(), |t, y| subs(&t, *y, &zero()));
    let linear_part = ys
        .iter()
        .zip(&coefficients)
        .fold(zero(), |s, (y, a)| s + a * &variable(*y));
    if ys
        .iter()
        .any(|y| depends(&rest, *y) || coefficients.iter().any(|a| depends(a, *y)))
        || !(e - linear_part - rest.clone()).expand().is_zero()
        || coefficients[n].is_zero()
    {
        return Err(unsupported());
    }
    Ok((coefficients, rest))
}

/// Solve the linear equation with constant `coefficients` `{$sum_k a_k y^((k)) + "rest" = 0$}` of order
/// `{$n >= 1$}`, with the integration `constants`.
pub(super) fn solve(
    coefficients: &[Rational],
    rest: &Expr,
    x: Symbol,
    constants: &[Symbol],
) -> OdeResult<Vec<OdeBranch<Real>>> {
    let n = coefficients.len() - 1;
    let lead = coefficients[n].clone();
    let basis = basis(&Poly::new(coefficients.to_vec()), x)?;
    let mut res = basis
        .iter()
        .zip(constants)
        .fold(zero(), |s, (y, c)| s + variable(*c) * y);
    if !rest.is_zero() {
        let g = -rest.clone() / value(lead);
        res += match undetermined(coefficients, &g, x) {
            Some(y) => y,
            None => particular(&basis, &g, x)?,
        };
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

/// A Gaussian rational `{$a + b i$}`.
type Gaussian = [Rational; 2];

/// A particular solution of `{$sum_k a_k y^((k)) = a_n g$}` by undetermined coefficients, when every term of `g` is
/// `{$q(x) e^(a x) cos(b x)$}` or `{$q(x) e^(a x) sin(b x)$}` with a polynomial `q` and rationals `a`, `b` (or
/// without the cosine and the sine), the real or imaginary part of `{$h(x) e^(s x)$}` with `{$s = a + b i$}`:
/// `{$P(D) (h e^(s x)) = e^(s x) P(D + s) h$}`, so `h` is a polynomial solution of `{$P(D + s) h = a_n q$}`.
/// Unlike variation of parameters it needs neither the roots of `P` nor integrals, which are very slow with the
/// nested radicals of Cardano's formula.
fn undetermined(coefficients: &[Rational], g: &Expr, x: Symbol) -> Option<Expr> {
    let lead = &coefficients[coefficients.len() - 1];
    let p = Poly::new(
        coefficients
            .iter()
            .map(|c| [c / lead, Rational::ZERO])
            .collect::<Vec<Gaussian>>(),
    );
    let terms = match g.expand() {
        Term::Add(add) => add.iter().cloned().collect(),
        term => vec![term],
    };
    let x_term = variable(x);
    let mut res = zero();
    for term in terms {
        let (q, a, b, sine) = forcing_term(&term, x)?;
        let h = shifted_solution(&p, &q, &[a.clone(), b.clone()]);
        let part = |i: usize| {
            Poly::new(h.coefficients().iter().map(|c| c[i].clone()).collect()).to_term(x)
        };
        // `{$q cos(b x) = "Re"(q e^(i b x))$}` and `{$q sin(b x) = "Im"(q e^(i b x))$}`
        let (cos_part, sin_part) = if sine {
            (part(1), part(0))
        } else {
            (part(0), -part(1))
        };
        let angle = value(b) * &x_term;
        res += fun(Context::EXP, value(a) * &x_term)
            * (cos_part * fun(Context::COS, angle.clone()) + sin_part * fun(Context::SIN, angle));
    }
    Some(res)
}

/// The polynomial `q`, the rationals `a`, `b` and whether the term is a sine, for a term
/// `{$q(x) e^(a x) cos(b x)$}` or `{$q(x) e^(a x) sin(b x)$}` (`{$b = 0$}` without them).
fn forcing_term(term: &Expr, x: Symbol) -> Option<(Poly, Rational, Rational, bool)> {
    let rate = |u: &Expr| match u.derivative(x) {
        Term::Value(v)
            if (u - &(value(v.value.clone()) * variable(x)))
                .expand()
                .is_zero() =>
        {
            Some(v.value)
        }
        _ => None,
    };
    let mut a = Rational::ZERO;
    let mut trigonometric = None;
    let mut rest = value(Rational::ONE);
    for factor in factors(term) {
        match unary(&factor) {
            Some((Context::EXP, u)) => a += rate(u)?,
            Some((ident @ (Context::COS | Context::SIN), u)) if trigonometric.is_none() => {
                trigonometric = Some((rate(u)?, ident == Context::SIN));
            }
            _ => rest *= &factor,
        }
    }
    let q = Poly::from_term(&rest, x)?;
    let (b, sine) = trigonometric.unwrap_or((Rational::ZERO, false));
    Some((q, a, b, sine))
}

/// The polynomial `h` solving `{$P(D + s) h = q$}`, of the lowest degree, whose coefficients below the order
/// `m` of `{$P(r + s)$}` at `{$r = 0$}` (the multiplicity of the root `s` of `P`) are zero: `{$f = h^((m))$}` is
/// found from its leading coefficient down, then integrated `m` times.
fn shifted_solution(p: &Poly<Gaussian>, q: &Poly, s: &Gaussian) -> Poly<Gaussian> {
    let c = p.shift(s);
    let m = c.order_at_zero();
    let d = q.coefficients().len().saturating_sub(1);
    let mut f = vec![Gaussian::zero(); d + 1];
    for j in (0..=d).rev() {
        let mut r: Gaussian = [q.coefficient(j), Rational::ZERO];
        // `{$D^t x^(j + t) = (j + t)! / j! x^j$}`
        let mut weight = Rational::ONE;
        for t in 1..=d - j {
            weight *= Rational::from(j + t);
            let term = c.coefficient(m + t).times(&f[j + t]);
            r = r.minus(&[&term[0] * &weight, &term[1] * &weight]);
        }
        f[j] = r.divide(&c.coefficient(m));
    }
    let mut h = vec![Gaussian::zero(); m];
    for (j, fj) in f.into_iter().enumerate() {
        // `{$x^j$}` integrated `m` times is `{$j! / (j + m)! x^(j + m)$}`
        let scale = (1..=m).fold(Rational::ONE, |s, i| s / Rational::from(j + i));
        h.push([&fj[0] * &scale, &fj[1] * &scale]);
    }
    Poly::new(h)
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
