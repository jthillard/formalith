//! Seeded random expressions, printed fully parenthesized, with variants per engine.
use super::rng::Rng;

/// Functions of random expressions.
pub const FUNCTIONS: [&str; 6] = ["exp", "ln", "sin", "cos", "sqrt", "atan"];

/// A small integer or rational constant.
pub fn constant(rng: &mut Rng) -> String {
    if rng.chance(0.7) {
        rng.nonzero(5).to_string()
    } else {
        format!("{}/{}", rng.nonzero(5), rng.range(2, 5))
    }
}

/// A random expression of depth at most `depth` in `vars`, with `+ - * /`, small powers and [`FUNCTIONS`].
pub fn expr(rng: &mut Rng, vars: &[&str], depth: usize) -> String {
    if depth == 0 || rng.chance(0.25) {
        return if rng.chance(0.65) {
            (*rng.pick(vars)).to_owned()
        } else {
            constant(rng)
        };
    }
    match rng.below(8) {
        0 | 1 => format!(
            "({} + {})",
            expr(rng, vars, depth - 1),
            expr(rng, vars, depth - 1)
        ),
        2 => format!(
            "({} - {})",
            expr(rng, vars, depth - 1),
            expr(rng, vars, depth - 1)
        ),
        3 | 4 => format!(
            "({} * {})",
            expr(rng, vars, depth - 1),
            expr(rng, vars, depth - 1)
        ),
        5 => format!(
            "({} / {})",
            expr(rng, vars, depth - 1),
            expr(rng, vars, depth - 1)
        ),
        6 => format!("({})^{}", expr(rng, vars, depth - 1), rng.pick(&[2, 3, -1])),
        _ => format!("{}({})", rng.pick(&FUNCTIONS), expr(rng, vars, depth - 1)),
    }
}

/// A polynomial in `vars` of total degree at most `degree`, with `terms` monomials and integer coefficients.
pub fn polynomial(rng: &mut Rng, vars: &[&str], degree: usize, terms: usize) -> String {
    let mut monomials = Vec::new();
    for _ in 0..terms.max(1) {
        let mut parts = vec![rng.nonzero(6).to_string()];
        let mut left = rng.range(0, degree as i64) as usize;
        for &v in vars {
            if left == 0 {
                break;
            }
            let e = rng.range(0, left as i64) as usize;
            left -= e;
            match e {
                0 => {}
                1 => parts.push(v.to_owned()),
                _ => parts.push(format!("{v}^{e}")),
            }
        }
        monomials.push(parts.join("*"));
    }
    format!("({})", monomials.join(" + "))
}

/// A univariate polynomial in `x` of degree exactly `degree`.
pub fn univariate(rng: &mut Rng, x: &str, degree: usize, coefficient: i64) -> String {
    let mut terms = vec![format!("{}*{x}^{degree}", rng.nonzero(coefficient))];
    for d in (0..degree).rev() {
        if rng.chance(0.6) {
            terms.push(format!("{}*{x}^{d}", rng.nonzero(coefficient)));
        }
    }
    format!("({})", terms.join(" + "))
}

/// A rational function `p/q` in `vars`.
pub fn rational_function(rng: &mut Rng, vars: &[&str]) -> String {
    let p = polynomial(rng, vars, 3, 3);
    let q = polynomial(rng, vars, 2, 2);
    format!("{p}/{q}")
}

/// A product of small linear factors in `x`, maybe with repeated ones.
pub fn linear_factors(rng: &mut Rng, x: &str, count: usize) -> String {
    let factors: Vec<_> = (0..count)
        .map(|_| {
            let a = rng.range(1, 3);
            let b = rng.range(-4, 4);
            format!("({a}*{x} + {b})")
        })
        .collect();
    factors.join("*")
}

/// A linear form `a x + b` with small coefficients, `a != 0`.
pub fn linear(rng: &mut Rng, x: &str) -> String {
    format!("({}*{x} + {})", rng.nonzero(3), rng.range(-3, 3))
}

/// An elementary building block of integrands in `x`.
pub fn integrand_atom(rng: &mut Rng) -> String {
    let l = linear(rng, "x");
    match rng.below(10) {
        0 => format!("x^{}", rng.range(0, 4)),
        1 => format!("exp({l})"),
        2 => format!("sin({l})"),
        3 => format!("cos({l})"),
        4 => format!("1/{l}"),
        5 => format!("1/(x^2 + {})", rng.range(1, 4)),
        6 => format!("ln({}*x)", rng.range(1, 3)),
        7 => format!("sqrt({}*x + {})", rng.range(1, 3), rng.range(0, 3)),
        8 => {
            let p = polynomial(rng, &["x"], 3, 2);
            let count = rng.below(2) + 2;
            format!("{p}/{}", linear_factors(rng, "x", count))
        }
        _ => format!("atan({l})"),
    }
}

/// An integrand in `x`: a sum or product of two [`integrand_atom`]s with a constant factor.
pub fn integrand(rng: &mut Rng) -> String {
    let a = integrand_atom(rng);
    let b = integrand_atom(rng);
    let c = constant(rng);
    match rng.below(3) {
        0 => format!("{c}*{a}"),
        1 => format!("{c}*{a} + {b}"),
        _ => format!("{c}*{a}*{b}"),
    }
}

/// A trigonometric polynomial in `x`.
pub fn trig_poly(rng: &mut Rng) -> String {
    let terms: Vec<_> = (0..rng.range(1, 3))
        .map(|_| {
            let f = rng.pick(&["sin", "cos"]);
            let k = rng.range(1, 3);
            let e = rng.range(1, 3);
            format!("{}*{f}({k}*x)^{e}", constant(rng))
        })
        .collect();
    terms.join(" + ")
}

/// A sum of products of exponentials and polynomials in `x`.
pub fn exp_poly(rng: &mut Rng) -> String {
    let terms: Vec<_> = (0..rng.range(1, 3))
        .map(|_| {
            format!(
                "{}*exp({})",
                polynomial(rng, &["x"], 2, 2),
                linear(rng, "x")
            )
        })
        .collect();
    terms.join(" + ")
}

/// A square integer matrix literal of size `n`, entries in `-bound..=bound`.
pub fn int_matrix(rng: &mut Rng, n: usize, m: usize, bound: i64) -> String {
    let rows: Vec<_> = (0..n)
        .map(|_| {
            let row: Vec<_> = (0..m)
                .map(|_| rng.range(-bound, bound).to_string())
                .collect();
            format!("[{}]", row.join(", "))
        })
        .collect();
    format!("[{}]", rows.join(", "))
}

/// Multiply integer matrices.
pub fn mat_mul(a: &[Vec<i64>], b: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let (n, k, m) = (a.len(), b.len(), b[0].len());
    (0..n)
        .map(|i| {
            (0..m)
                .map(|j| (0..k).map(|l| a[i][l] * b[l][j]).sum())
                .collect()
        })
        .collect()
}

/// A matrix literal from rows.
pub fn literal(rows: &[Vec<i64>]) -> String {
    let rows: Vec<_> = rows
        .iter()
        .map(|r| {
            format!(
                "[{}]",
                r.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
        .collect();
    format!("[{}]", rows.join(", "))
}

/// A unimodular `n x n` integer matrix (product of a lower and an upper unitriangular matrix), with its inverse.
pub fn unimodular(rng: &mut Rng, n: usize) -> (Vec<Vec<i64>>, Vec<Vec<i64>>) {
    let mut lower = vec![vec![0; n]; n];
    let mut upper = vec![vec![0; n]; n];
    for i in 0..n {
        lower[i][i] = 1;
        upper[i][i] = 1;
        for j in 0..i {
            lower[i][j] = rng.range(-1, 1);
            upper[j][i] = rng.range(-1, 1);
        }
    }
    let p = mat_mul(&lower, &upper);
    // Inverses of unitriangular matrices by forward substitution
    let inv_lower = unitriangular_inverse(&lower, true);
    let inv_upper = unitriangular_inverse(&upper, false);
    (p, mat_mul(&inv_upper, &inv_lower))
}

fn unitriangular_inverse(t: &[Vec<i64>], lower: bool) -> Vec<Vec<i64>> {
    let n = t.len();
    let mut inv = vec![vec![0; n]; n];
    for col in 0..n {
        let order: Vec<usize> = if lower {
            (0..n).collect()
        } else {
            (0..n).rev().collect()
        };
        for &i in &order {
            let e = i64::from(i == col);
            let s: i64 = (0..n)
                .filter(|&j| if lower { j < i } else { j > i })
                .map(|j| t[i][j] * inv[j][col])
                .sum();
            inv[i][col] = e - s;
        }
    }
    inv
}

/// A diagonalizable `n x n` integer matrix `P D P^-1` with small integer eigenvalues (maybe repeated), and the
/// eigenvalues.
pub fn diagonalizable(rng: &mut Rng, n: usize) -> (String, Vec<i64>) {
    let (p, inv) = unimodular(rng, n);
    let eig: Vec<i64> = (0..n).map(|_| rng.range(-3, 3)).collect();
    let mut d = vec![vec![0; n]; n];
    for i in 0..n {
        d[i][i] = eig[i];
    }
    (literal(&mat_mul(&mat_mul(&p, &d), &inv)), eig)
}
