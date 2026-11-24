//! Coefficients of sums: polynomials in the index `k` with coefficients in `{$QQ(t_1, ..., t_n)$}`, each `{$t_i$}`
//! being a subterm free of `k` (a parameter, `{$sqrt(2)$}`, `{$pi$}`...), considered transcendental.

use malachite::Rational;

use crate::{
    context::Symbol,
    field::real::expr::{Expr, depends, value, variable, zero},
    polynom::{
        dense::Coefficient,
        fraction::{EPoly, Elem},
    },
    term::{Expand, Term},
};

/// The subterms free of the index used as generators `{$t_1, ..., t_n$}`.
#[derive(Default)]
pub struct Params {
    atoms: Vec<Expr>,
}

impl Params {
    /// The generator of the field standing for `atom`.
    fn generator(&mut self, atom: &Expr) -> Elem {
        let level = if let Some(i) = self.atoms.iter().position(|a| a == atom) {
            i + 1
        } else {
            self.atoms.push(atom.clone());
            self.atoms.len()
        };
        Elem::generator(level)
    }

    /// A term free of `k` as an element of the field, `None` if it divides by 0.
    pub(crate) fn elem(&mut self, term: &Expr) -> Option<Elem> {
        Some(match term {
            Term::Value(v) => Elem::rational(v.value.clone()),
            Term::Add(add) => add
                .iter()
                .try_fold(Elem::zero(), |res, t| Some(res.plus(&self.elem(t)?)))?,
            Term::Mul(mul) => mul
                .iter()
                .try_fold(Elem::rational(mul.coefficient.clone()), |res, t| {
                    Some(res.times(&self.elem(t)?))
                })?,
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(n) => match i64::try_from(&n.value) {
                    Ok(n) => {
                        let base = self.elem(&pow.base)?;
                        if n < 0 && base.is_zero() {
                            return None;
                        }
                        base.pow(n)
                    }
                    Err(_) => self.generator(term),
                },
                _ => self.generator(term),
            },
            Term::Symbol(_) | Term::Fun(_) => self.generator(term),
        })
    }

    /// The polynomial in `k` given by an expression, `None` if it isn't one.
    pub(crate) fn poly(&mut self, term: &Expr, k: Symbol) -> Option<EPoly> {
        self.expanded_poly(&term.expand(), k)
    }

    fn expanded_poly(&mut self, term: &Expr, k: Symbol) -> Option<EPoly> {
        if !depends(term, k) {
            return Some(EPoly::constant(self.elem(term)?));
        }
        match term {
            Term::Symbol(_) => Some(EPoly::x()),
            Term::Add(add) => add.iter().try_fold(EPoly::zero(), |res, t| {
                Some(res.add(&self.expanded_poly(t, k)?))
            }),
            Term::Mul(mul) => mul.iter().try_fold(
                EPoly::constant(Elem::rational(mul.coefficient.clone())),
                |res, t| Some(res.mul(&self.expanded_poly(t, k)?)),
            ),
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(n) => {
                    let n = usize::try_from(&n.value).ok()?;
                    Some(self.expanded_poly(&pow.base, k)?.pow(n))
                }
                _ => None,
            },
            Term::Value(_) | Term::Fun(_) => None,
        }
    }

    /// The rational function `{$p / q$}` in `k` given by an expression, reduced with `q` monic, `None` if it isn't
    /// one.
    pub(crate) fn rational(&mut self, term: &Expr, k: Symbol) -> Option<(EPoly, EPoly)> {
        let (num, den) = term.as_fraction(true);
        let num = self.poly(&num, k)?;
        let den = self.poly(&den, k)?;
        if den.is_zero() {
            return None;
        }
        Some(reduce(&num, &den))
    }

    /// The element as an expression.
    pub(crate) fn to_term(&self, e: &Elem) -> Expr {
        match e {
            Elem::Rational(r) => value(r.clone()),
            Elem::Fraction(_) => {
                let level = e.level();
                let (num, den) = e.fraction(level);
                let t = &self.atoms[level - 1];
                let num = self.poly_to_term(&num, t);
                if den.is_one() {
                    num
                } else {
                    num / self.poly_to_term(&den, t)
                }
            }
        }
    }

    /// The polynomial in `x` as an expression.
    pub(crate) fn poly_to_term(&self, p: &EPoly, x: &Expr) -> Expr {
        p.coefficients()
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .fold(zero(), |res, (i, c)| {
                let c = self.to_term(c);
                res + match i {
                    0 => c,
                    1 => c * x,
                    _ => c * x.pow(&value(Rational::from(i))),
                }
            })
    }

    /// The polynomial in `k` as an expression.
    pub(crate) fn k_poly_to_term(&self, p: &EPoly, k: Symbol) -> Expr {
        self.poly_to_term(p, &variable(k))
    }
}

/// The fraction `{$p / q$}` reduced, with `q` monic.
pub fn reduce(num: &EPoly, den: &EPoly) -> (EPoly, EPoly) {
    let g = num.gcd(den);
    let (num, den) = if g.degree() == 0 {
        (num.clone(), den.clone())
    } else {
        (num.exact_div(&g), den.exact_div(&g))
    };
    let lead = den.leading().inverse();
    (num.scale(&lead), den.scale(&lead))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{field::real::R, parse, symbol};

    #[test]
    fn round_trip() {
        let k = symbol!("k");
        let mut params = Params::default();
        let (num, den) = params
            .rational(&parse!("(a*k + 1)/(k^2 - a^2)", R), k)
            .unwrap();
        assert_eq!(den.degree(), 2);
        let term = params.k_poly_to_term(&num, k) / params.k_poly_to_term(&den, k);
        assert_eq!(term, parse!("(a*k + 1)/(k^2 - a^2)", R));
    }
}
