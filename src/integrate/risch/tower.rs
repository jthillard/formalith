//! The differential field `{$K_n = QQ(x, t_2, ..., t_n)$}` an integrand lives in, each `{$t_k$}` being an
//! exponential or a logarithm of an element of `{$K_(k - 1)$}`, transcendental over it.
//!
//! The tower is built from the expression: a new exponential `{$e^a$}` or logarithm `{$ln u$}` is only added when
//! it is not algebraic over the tower, which the Risch structure theorems reduce to linear algebra over `{$QQ$}`:
//! `{$e^a$}` is algebraic iff `{$a' = sum_i r_i u_i' / u_i + sum_j r_j a_j'$}` for rational `r`, the `{$ln u_i$}`
//! and `{$e^(a_j)$}` being the monomials of the tower, and `{$ln u$}` iff `{$u' / u$}` is such a combination.
//! Dependent ones are written with the existing monomials, when the exponents are integers.

use malachite::{
    Rational,
    base::num::{
        arithmetic::traits::Lcm,
        basic::traits::{One, Zero},
    },
};

use crate::{
    context::{Context, Symbol},
    field::real::R,
    integrate::{
        Expr,
        poly::Coefficient,
    },
    limit::{fun, value, variable},
    term::Term,
};

use super::{
    RischError, RischResult,
    field::{EPoly, Elem},
};

/// Maximum number of monomials of a tower.
const MAX_HEIGHT: usize = 6;

/// The kind of a monomial `t`.
#[derive(Clone, Debug)]
pub(super) enum Kind {
    /// `{$t = x$}`.
    X,
    /// `{$t = e^a$}`, with `a` of a lower level.
    Exp(Elem),
    /// `{$t = ln u$}`, with `u` of a lower level.
    Ln(Elem),
}

/// A monomial `{$t_k$}` of the tower.
#[derive(Clone, Debug)]
struct Monomial {
    kind: Kind,
    /// `{$D t_k$}`, as a polynomial in `{$t_k$}`.
    derivative: EPoly,
    /// The monomial as an expression.
    term: Expr,
}

/// A tower of monomials over `{$QQ$}`.
#[derive(Clone, Debug)]
pub(super) struct Tower {
    x: Symbol,
    monomials: Vec<Monomial>,
    /// Arguments `b` of exponentials to add before an exponential `{$e^a$}` with `{$a = n b$}`, `n` an integer.
    hints: Vec<Expr>,
    /// An argument to add to the hints, when an exponential is a non-integer power of a monomial.
    rebase: Option<Expr>,
}

impl Tower {
    pub(super) fn new(x: Symbol) -> Self {
        Self {
            x,
            monomials: vec![Monomial {
                kind: Kind::X,
                derivative: EPoly::one(),
                term: variable(x),
            }],
            hints: vec![],
            rebase: None,
        }
    }

    /// The tower of an expression and the expression as an element of it.
    ///
    /// # Errors
    /// See [`Self::elem`].
    pub(super) fn build(x: Symbol, term: &Expr) -> RischResult<(Self, Elem)> {
        let mut hints = vec![];
        for _ in 0..MAX_HEIGHT {
            let mut tower = Self::new(x);
            tower.hints.clone_from(&hints);
            match tower.elem(term) {
                Ok(e) => return Ok((tower, e)),
                Err(err) => match tower.rebase.take() {
                    Some(hint) => hints.push(hint),
                    None => return Err(err),
                },
            }
        }
        Err(RischError::Unsupported)
    }

    pub(super) const fn x(&self) -> Symbol {
        self.x
    }

    pub(super) fn kind(&self, level: usize) -> &Kind {
        &self.monomials[level - 1].kind
    }

    /// The number of monomials.
    pub(super) const fn height(&self) -> usize {
        self.monomials.len()
    }

    /// `{$D t$}` as a polynomial in `t`, for the monomial `t` of level `level`.
    pub(super) fn monomial_derivative(&self, level: usize) -> &EPoly {
        &self.monomials[level - 1].derivative
    }

    /// `{$eta = D a$}` for `{$t = e^a$}`, `{$D u / u$}` for `{$t = ln u$}`, 1 for `{$t = x$}`: an element of lower
    /// level with `{$D t = eta t$}` or `{$D t = eta$}`.
    pub(super) fn eta(&self, level: usize) -> Elem {
        let derivative = self.monomial_derivative(level);
        match self.kind(level) {
            Kind::Exp(_) => derivative.coefficient(1),
            Kind::X | Kind::Ln(_) => derivative.coefficient(0),
        }
    }

    /// The derivative of an element.
    pub(super) fn derivative(&self, f: &Elem) -> Elem {
        let level = f.level();
        if level == 0 {
            return Elem::zero();
        }
        let (num, den) = f.fraction(level);
        let dnum = self.derivative_poly(&num, level);
        if den.degree() == 0 {
            return Elem::from_poly(level, dnum);
        }
        let dden = self.derivative_poly(&den, level);
        Elem::from_fraction(level, &dnum.mul(&den).sub(&num.mul(&dden)), &den.mul(&den))
    }

    /// The derivative of a polynomial in the monomial of level `level`.
    pub(super) fn derivative_poly(&self, p: &EPoly, level: usize) -> EPoly {
        let coefficients = p.map(|c| self.derivative(c));
        coefficients.add(&p.derivative().mul(self.monomial_derivative(level)))
    }

    /// `{$(p, s)$}` with `{$p = p_n p_s$}`, `{$p_s$}` the special part (a power of `t` for `{$t = e^a$}`, 1
    /// otherwise), and `{$p_n$}` the normal part.
    pub(super) fn split_factor(&self, p: &EPoly, level: usize) -> (EPoly, EPoly) {
        match self.kind(level) {
            Kind::Exp(_) => {
                let n = p.order_at_zero();
                (p.shift_down(n), EPoly::monomial(Elem::one(), n))
            }
            Kind::X | Kind::Ln(_) => (p.clone(), EPoly::one()),
        }
    }

    /// The element as an expression.
    pub(super) fn to_term(&self, f: &Elem) -> Expr {
        match f {
            Elem::Rational(r) => value(r.clone()),
            Elem::Fraction(_) => {
                let level = f.level();
                let (num, den) = f.fraction(level);
                let num = self.poly_to_term(&num, level);
                if den.is_one_poly() {
                    num
                } else {
                    num / self.poly_to_term(&den, level)
                }
            }
        }
    }

    /// The polynomial in the monomial of level `level` as an expression.
    pub(super) fn poly_to_term(&self, p: &EPoly, level: usize) -> Expr {
        let t = &self.monomials[level - 1].term;
        p.coefficients()
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .fold(Term::zero(R), |res, (i, c)| {
                let c = self.to_term(c);
                res + match i {
                    0 => c,
                    1 => c * t,
                    _ => c * t.pow(&value(Rational::from(i))),
                }
            })
    }

    /// The expression as an element of the tower, adding the monomials it needs.
    ///
    /// # Errors
    /// [`RischError::Unsupported`] when the expression isn't in a tower of exponentials and logarithms over
    /// `{$QQ(x)$}`.
    pub(super) fn elem(&mut self, term: &Expr) -> RischResult<Elem> {
        match term {
            Term::Value(v) => Ok(Elem::rational(v.value.clone())),
            Term::Symbol(s) if s.symbol == self.x => Ok(Elem::generator(1)),
            Term::Symbol(_) => Err(RischError::Unsupported),
            Term::Add(add) => add
                .iter()
                .try_fold(Elem::zero(), |res, t| Ok(res.plus(&self.elem(t)?))),
            Term::Mul(mul) => mul.iter().try_fold(
                Elem::rational(mul.coefficient.clone()),
                |res, t| Ok(res.times(&self.elem(t)?)),
            ),
            Term::Pow(pow) => {
                let base = self.elem(&pow.base)?;
                if let Some(n) = pow.exponant.to_i64() {
                    if base.is_zero() && n < 0 {
                        return Err(RischError::Unsupported);
                    }
                    return Ok(base.pow(n));
                }
                // `{$b^g = e^(g ln b)$}`
                let exponant = self.elem(&pow.exponant)?;
                if exponant.level() == 0 {
                    // Algebraic
                    return Err(RischError::Unsupported);
                }
                let ln_term = fun(Context::LN, (*pow.base).clone());
                let ln = self.ln(&base, ln_term.clone())?;
                self.exp(&exponant.times(&ln), term.clone())
            }
            Term::Fun(f) => match f.get_args::<R<Rational>>().map(Vec::as_slice) {
                Some([arg]) => match f.get_ident() {
                    Context::EXP => {
                        let a = self.elem(arg)?;
                        self.exp(&a, term.clone())
                    }
                    Context::LN => {
                        let u = self.elem(arg)?;
                        self.ln(&u, term.clone())
                    }
                    _ => Err(RischError::Unsupported),
                },
                _ => Err(RischError::Unsupported),
            },
        }
    }

    /// `{$e^a$}`, `term` being it as an expression.
    fn exp(&mut self, a: &Elem, term: Expr) -> RischResult<Elem> {
        if a.level() == 0 {
            return if a.is_zero() { Ok(Elem::one()) } else { Err(RischError::Unsupported) };
        }
        let da = self.derivative(a);
        if let Some(r) = self.dependence(&da)? {
            // `{$a = sum r_i ln u_i + sum r_j a_j + c$}`, so `{$e^a = e^c product u_i^(r_i) product t_j^(r_j)$}`
            let mut rest = a.clone();
            let mut res = Elem::one();
            for (k, r) in r.iter().enumerate().filter(|(_, r)| **r != 0) {
                let level = k + 2;
                let Some(n) = integer(r) else {
                    // `{$e^a = t^(p / q)$}` for `{$t = e^b$}`: build again with `{$e^(b / q)$}` first
                    if let Kind::Exp(b) = self.kind(level) {
                        let q = Rational::from(r.denominator_ref().clone());
                        self.rebase = Some(self.to_term(b) / value(q));
                    }
                    return Err(RischError::Unsupported);
                };
                let r = Elem::rational(r.clone());
                match self.kind(level).clone() {
                    Kind::Ln(u) => {
                        rest = rest.minus(&r.times(&Elem::generator(level)));
                        res = res.times(&u.pow(n));
                    }
                    Kind::Exp(b) => {
                        rest = rest.minus(&r.times(&b));
                        res = res.times(&Elem::generator(level).pow(n));
                    }
                    Kind::X => unreachable!("x is not a candidate"),
                }
            }
            // `{$e^c$}` is a transcendental constant for a rational `{$c != 0$}`
            return if rest.is_zero() { Ok(res) } else { Err(RischError::Unsupported) };
        }
        for i in 0..self.hints.len() {
            let hint = self.hints[i].clone();
            let Ok(b) = self.elem(&hint) else {
                continue;
            };
            let db = self.derivative(&b);
            if !db.is_zero() && da.divide(&db).as_rational().and_then(integer).is_some() {
                self.hints.remove(i);
                self.exp(&b, fun(Context::EXP, hint))?;
                return self.exp(a, term);
            }
        }
        self.push(Monomial {
            kind: Kind::Exp(a.clone()),
            derivative: EPoly::new(vec![Elem::zero(), da]),
            term,
        })
    }

    /// `{$ln u$}`, `term` being it as an expression.
    fn ln(&mut self, u: &Elem, term: Expr) -> RischResult<Elem> {
        if u.level() == 0 {
            return if u.is_one() { Ok(Elem::zero()) } else { Err(RischError::Unsupported) };
        }
        let eta = self.derivative(u).divide(u);
        if let Some(r) = self.dependence(&eta)? {
            // `{$ln u = sum r_i ln u_i + sum r_j a_j + ln c$}`, with `{$u^N = c^N product u_i^(N r_i) product
            // t_j^(N r_j)$}`
            let n = r
                .iter()
                .fold(malachite::Natural::ONE, |n, r| n.lcm(r.denominator_ref()));
            let n = Rational::from(n);
            let mut res = Elem::zero();
            let mut product = Elem::one();
            for (k, r) in r.iter().enumerate().filter(|(_, r)| **r != 0) {
                let level = k + 2;
                let power = integer(&(r * &n)).ok_or(RischError::Unsupported)?;
                let r = Elem::rational(r.clone());
                match self.kind(level).clone() {
                    Kind::Ln(v) => {
                        res = res.plus(&r.times(&Elem::generator(level)));
                        product = product.times(&v.pow(power));
                    }
                    Kind::Exp(b) => {
                        res = res.plus(&r.times(&b));
                        product = product.times(&Elem::generator(level).pow(power));
                    }
                    Kind::X => unreachable!("x is not a candidate"),
                }
            }
            let n = integer(&n).ok_or(RischError::Unsupported)?;
            return if u.pow(n) == product { Ok(res) } else { Err(RischError::Unsupported) };
        }
        self.push(Monomial {
            kind: Kind::Ln(u.clone()),
            derivative: EPoly::constant(eta),
            term,
        })
    }

    fn push(&mut self, monomial: Monomial) -> RischResult<Elem> {
        if self.monomials.len() >= MAX_HEIGHT {
            return Err(RischError::Unsupported);
        }
        self.monomials.push(monomial);
        Ok(Elem::generator(self.monomials.len()))
    }

    /// Rational `{$r_k$}` with `{$f = sum_k r_k eta_k$}` over the monomials `{$t_k$}` other than `x`, if any. The
    /// candidates are found by evaluating at points, then checked exactly.
    fn dependence(&self, f: &Elem) -> RischResult<Option<Vec<Rational>>> {
        let etas: Vec<_> = (2..=self.height()).map(|level| self.eta(level)).collect();
        let mut rows = vec![];
        for point in sample_points(self.height()).take(4 * (etas.len() + 3)) {
            let row: Option<Vec<_>> = etas
                .iter()
                .chain(std::iter::once(f))
                .map(|e| e.eval(&point))
                .collect();
            if let Some(row) = row {
                rows.push(row);
                if rows.len() == etas.len() + 3 {
                    break;
                }
            }
        }
        if rows.len() < etas.len() + 3 {
            return Err(RischError::Unsupported);
        }
        let Some(r) = solve_linear(rows, etas.len()) else {
            return Ok(None);
        };
        let combination = etas
            .iter()
            .zip(&r)
            .fold(Elem::zero(), |res, (eta, r)| res.plus(&eta.times(&Elem::rational(r.clone()))));
        if combination == *f {
            Ok(Some(r))
        } else {
            Err(RischError::Unsupported)
        }
    }
}

/// The integer `r`, if it is one.
fn integer(r: &Rational) -> Option<i64> {
    i64::try_from(r).ok()
}

/// Points of `{$QQ^n$}` to evaluate elements at, distinct from simple values like 0, 1 or -1.
pub(super) fn sample_points(n: usize) -> impl Iterator<Item = Vec<Rational>> {
    const PRIMES: [i64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    (0..).map(move |i: usize| {
        (0..n)
            .map(|j| {
                let p = PRIMES[(i + 3 * j) % PRIMES.len()];
                let q = PRIMES[(2 * i + j + 5) % PRIMES.len()];
                Rational::from_signeds(p * i64::try_from(i + j + 1).unwrap_or(1) + 1, q)
            })
            .collect()
    })
}

/// A solution `r` of the linear system whose rows are `{$(a_1, ..., a_n, b)$}` with `{$sum a_i r_i = b$}`, the
/// free unknowns being 0, or `None` if it is inconsistent.
pub(super) fn solve_linear(mut rows: Vec<Vec<Rational>>, n: usize) -> Option<Vec<Rational>> {
    let mut pivots = vec![];
    let mut row = 0;
    for column in 0..n {
        let Some(pivot) = (row..rows.len()).find(|&i| rows[i][column] != 0) else {
            continue;
        };
        rows.swap(row, pivot);
        let inverse = Rational::ONE / &rows[row][column];
        for value in &mut rows[row] {
            *value *= &inverse;
        }
        for i in 0..rows.len() {
            if i != row && rows[i][column] != 0 {
                let factor = rows[i][column].clone();
                for j in 0..=n {
                    let delta = &factor * &rows[row][j];
                    rows[i][j] -= delta;
                }
            }
        }
        pivots.push(column);
        row += 1;
    }
    if rows[row..].iter().any(|r| r[n] != 0) {
        return None;
    }
    let mut res = vec![Rational::ZERO; n];
    for (i, column) in pivots.into_iter().enumerate() {
        res[column] = rows[i][n].clone();
    }
    Some(res)
}

impl EPoly {
    /// Whether the polynomial is 1.
    pub(super) fn is_one_poly(&self) -> bool {
        self.coefficients().len() == 1 && self.coefficients()[0].is_one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, symbol};

    fn build(f: &str) -> (Tower, Elem) {
        Tower::build(symbol!("x"), &parse!(f, R)).unwrap()
    }

    #[test]
    fn dependent_monomials() {
        // `{$e^(2x) = (e^x)^2$}`, `{$e^(3x / 2) = (e^(x / 2))^3$}`
        let (tower, e) = build("exp(x) + exp(2*x)");
        assert_eq!(tower.height(), 2);
        let t = Elem::generator(2);
        assert_eq!(e, t.plus(&t.times(&t)));
        let (tower, e) = build("exp(x) + exp(3*x/2)");
        assert_eq!(tower.height(), 2);
        assert_eq!(e, t.pow(2).plus(&t.pow(3)));
        // `{$ln(x^2) = 2 ln x$}`
        let (tower, e) = build("ln(x) + ln(x^2)");
        assert_eq!(tower.height(), 2);
        assert_eq!(tower.derivative(&e), Elem::integer(3).divide(&Elem::generator(1)));
        // `{$t = e^(x + ln x)$}` comes first, then `{$e^x = t / x$}`
        let (tower, e) = build("ln(x) + exp(x) + exp(x + ln(x))");
        assert_eq!(tower.height(), 3);
        let (x, l, t) = (Elem::generator(1), Elem::generator(2), Elem::generator(3));
        assert_eq!(e, l.plus(&t).plus(&t.divide(&x)));
        // `{$ln(x^2 e^(2x)) = 2 ln x + 2 x$}`
        let (tower, e) = build("ln(x) + exp(x) + ln(x^2*exp(2*x))");
        assert_eq!(tower.height(), 3);
        let expected = Elem::integer(3).divide(&x).plus(&Elem::generator(2)).plus(&Elem::integer(2));
        assert_eq!(tower.derivative(&e), expected);
    }

    #[test]
    fn unsupported() {
        let mut tower = Tower::new(symbol!("x"));
        for f in ["sqrt(x)", "sin(x)", "exp(x)+exp(x+1)", "ln(2)*x", "a*x", "exp(ln(x)/2)"] {
            assert!(tower.clone().elem(&parse!(f, R)).is_err(), "{f}");
        }
        tower.elem(&parse!("x", R)).unwrap();
    }
}
