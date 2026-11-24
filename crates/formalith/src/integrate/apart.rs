//! Partial fraction decomposition of rational functions with rational (or Gaussian rational) coefficients, the
//! builtin `apart(f, x)`.

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    field::{Set, complex::C, real::Real},
    term::{Term, Value},
};

use super::{
    poly::{TermCoefficient, rational_function_over},
    rational::factor,
};

impl Term<Real> {
    /// The partial fraction decomposition of the expression in `x`, `{$p + sum_(q, j) a_(q, j) / q^j$}` with `p` a
    /// polynomial, `q` the monic irreducible factors over `{$QQ$}` of the denominator and `{$deg a_(q, j) < deg q$}`,
    /// or `None` if it isn't a rational function of `x` with rational coefficients.
    ///
    /// ```
    /// use formalith::{field::real::R, parse, symbol};
    ///
    /// let x = symbol!("x");
    /// assert_eq!(parse!("1/(x^2-1)", R).apart(x), Some(parse!("1/(2*(x-1)) - 1/(2*(x+1))", R)));
    /// ```
    #[must_use]
    pub fn apart(&self, x: Symbol) -> Option<Self> {
        apart::<Rational>(self, x)
    }
}

impl Term<C<Real>> {
    /// The partial fraction decomposition of the expression in `x` over `{$QQ(i)$}`, like [`Term::<Real>::apart`]
    /// with the irreducible factors over `{$QQ(i)$}` of the denominator, or `None` if it isn't a rational function
    /// of `x` with Gaussian rational coefficients.
    ///
    /// ```
    /// use formalith::{field::complex::C, parse, symbol};
    ///
    /// let x = symbol!("x");
    /// assert_eq!(parse!("1/(x^2+1)", C).apart(x), Some(parse!("-i/(2*(x-i)) + i/(2*(x+i))", C)));
    /// ```
    #[must_use]
    pub fn apart(&self, x: Symbol) -> Option<Self> {
        apart::<[Rational; 2]>(self, x)
    }
}

/// The function and variable of `apart(f, x)`, or of `apart(f)` when `f` has a single symbol.
pub fn apart_arguments<T: Set>(args: &[Term<T>]) -> Option<(&Term<T>, Symbol)> {
    match args {
        [f, Term::Symbol(x)] => Some((f, x.symbol)),
        [f] => {
            let symbols: Vec<_> = f
                .symbols()
                .into_iter()
                .filter(|s| !Context::is_builtin_constant(*s))
                .collect();
            match symbols.as_slice() {
                [x] => Some((f, *x)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The partial fraction decomposition of `f` in `x` over the field of coefficients `F`.
fn apart<F: TermCoefficient>(f: &Term<F::Set>, x: Symbol) -> Option<Term<F::Set>> {
    let (num, den) = rational_function_over::<F>(f, x)?;
    let (quo, rem) = num.div_rem(&den);
    let mut res = quo.to_term(x);
    if rem.is_zero() {
        return Some(res);
    }
    for (i, square_free) in den.square_free().iter().enumerate() {
        if square_free.degree() == 0 {
            continue;
        }
        let multiplicity = i + 1;
        for q in factor(square_free, x) {
            // `{$A / D = A_q / q^e + ...$}` with `{$A_q = A (D / q^e)^(-1) mod q^e$}`
            let power = q.pow(multiplicity);
            let cofactor = den.exact_div(&power);
            let mut a = rem.mul(&cofactor.inverse_mod(&power)).rem(&power);
            // The `q`-adic digits of `{$A_q = sum_j a_j q^j$}` give `{$a_j / q^(e - j)$}`
            let q_term = q.to_term(x);
            for j in 0..multiplicity {
                let (quotient, digit) = a.div_rem(&q);
                if !digit.is_zero() {
                    let exponent = F::from_rational(Rational::from(multiplicity - j));
                    res +=
                        digit.to_term(x) / q_term.pow(&Term::Value(Value::new(exponent, F::set())));
                }
                a = quotient;
            }
        }
    }
    Some(res)
}
