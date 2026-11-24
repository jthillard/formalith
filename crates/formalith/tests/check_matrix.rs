//! Matrix builtins checked against their definitions: `A v = λ v` for eigenvectors, `A K = 0` with `n - rank`
//! columns for `kernel`, `det` and `trace` against the eigenvalues, `charpoly(A)` vanishing at `A`
//! (Cayley-Hamilton), `A A^-1 = I`, and the shape properties of `hermite` and `smith` over `Z`.

use crate::common::{
    harness::{Verdict, check_all, fuzz},
    numeric::{env_with, eval, eval_in, number, split_top},
    random,
    rng::Rng,
};
use formalith::{dynamic::SetChoice, parser::environment::Environment};

/// Rows of a printed matrix `[[a, b], [c, d]]`.
fn rows(matrix: &str) -> Option<Vec<Vec<String>>> {
    let inner = matrix.trim().strip_prefix('[')?.strip_suffix(']')?;
    split_top(inner, ',')
        .iter()
        .map(|row| Some(split_top(row.strip_prefix('[')?.strip_suffix(']')?, ',')))
        .collect()
}

/// The columns of a printed matrix, each as a column matrix literal.
fn columns(matrix: &str) -> Option<Vec<String>> {
    let rows = rows(matrix)?;
    Some(
        (0..rows[0].len())
            .map(|j| {
                format!(
                    "[{}]",
                    rows.iter()
                        .map(|r| format!("[{}]", r[j]))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect(),
    )
}

/// Evaluate in `M` (symbolic real entries).
fn m(input: &str) -> Result<String, String> {
    eval_in(SetChoice::M, &mut Environment::new(), input)
}

/// Whether every entry of the printed matrix is numerically 0.
fn numerically_zero(matrix: &str) -> bool {
    let env = env_with(&[]);
    rows(matrix).is_some_and(|rows| {
        rows.iter()
            .flatten()
            .all(|e| number(&env, e).is_some_and(|v| v.abs() < 1e-9))
    })
}

/// Check `eigenvalues`, `eigenvectors`, `det`, `trace`, `kernel`, `rank`, `charpoly` and the inverse of `A`.
fn linear_algebra(a: &str) -> Verdict {
    let n = rows(a).unwrap().len();
    let env = env_with(&[]);
    let mut renv = Environment::new();
    let scalar = |f: &str| eval(&mut renv.clone(), &format!("{f}({a})"));
    let (Ok(det), Ok(trace), Ok(rank)) = (scalar("det"), scalar("trace"), scalar("rank")) else {
        return Verdict::Skip("det, trace or rank".to_owned());
    };
    let (Some(det_v), Some(trace_v)) = (number(&env, &det), number(&env, &trace)) else {
        return Verdict::Skip("det, trace aren't numbers".to_owned());
    };
    let rank: usize = rank.parse().unwrap();
    // Kernel: `A K = 0`, `n - rank` columns
    let Ok(kernel) = m(&format!("kernel({a})")) else {
        return Verdict::Skip("kernel".to_owned());
    };
    let Ok(product) = m(&format!("{a} * {kernel}")) else {
        return Verdict::Skip("A K".to_owned());
    };
    if !numerically_zero(&product) {
        return Verdict::Wrong(format!("A kernel(A) = {product} with kernel {kernel}"));
    }
    let dim = if rank == n {
        0
    } else {
        columns(&kernel).map_or(0, |c| c.len())
    };
    if dim != n - rank {
        return Verdict::Wrong(format!(
            "kernel {kernel} has {dim} columns but rank is {rank}"
        ));
    }
    // Cayley-Hamilton: `p(A) = 0` with the coefficients of `charpoly(A, x)`
    let Ok(p) = eval(&mut renv, &format!("charpoly({a}, x)")) else {
        return Verdict::Skip("charpoly".to_owned());
    };
    let mut terms = Vec::new();
    for k in 0..=n {
        let Ok(c) = eval(&mut renv, &format!("diff({p}, x, {k})/factorial({k})")) else {
            return Verdict::Skip("coefficients".to_owned());
        };
        let c = c.replace('x', "0");
        match m(&format!("({c})*{a}^{k}")) {
            Ok(term) => terms.push(term),
            Err(e) => return Verdict::Skip(e),
        }
    }
    match m(&terms.join(" + ")) {
        Ok(res) if numerically_zero(&res) => {}
        Ok(res) => return Verdict::Wrong(format!("charpoly(A) = {p} but p(A) = {res}")),
        Err(e) => return Verdict::Skip(e),
    }
    // Inverse
    if det_v.abs() > 1e-9 {
        let identity = format!("{a}^0");
        match m(&format!("{a} * {a}^-1 - {identity}")) {
            Ok(res) if numerically_zero(&res) => {}
            Ok(res) => return Verdict::Wrong(format!("A A^-1 - I = {res}")),
            Err(e) => return Verdict::Skip(e),
        }
    }
    // Eigenvalues and eigenvectors
    let (Ok(values), Ok(vectors)) = (
        m(&format!("eigenvalues({a})")),
        m(&format!("eigenvectors({a})")),
    ) else {
        return Verdict::Skip("eigen".to_owned());
    };
    if values.contains("eigen") || vectors.contains("eigen") {
        return Verdict::Pass;
    }
    let values: Vec<String> = rows(&values)
        .unwrap()
        .into_iter()
        .map(|r| r[0].clone())
        .collect();
    if values.len() != n {
        return Verdict::Wrong(format!(
            "{} eigenvalues {values:?} for size {n}",
            values.len()
        ));
    }
    let numeric: Vec<f64> = values.iter().filter_map(|v| number(&env, v)).collect();
    if numeric.len() == n {
        let (prod, sum): (f64, f64) = (numeric.iter().product(), numeric.iter().sum());
        if (prod - det_v).abs() > 1e-8 * det_v.abs().max(1.0)
            || (sum - trace_v).abs() > 1e-8 * trace_v.abs().max(1.0)
        {
            return Verdict::Wrong(format!(
                "eigenvalues {values:?}: product {prod}, sum {sum}, det {det_v}, trace {trace_v}"
            ));
        }
    }
    let mut distinct = values.clone();
    distinct.dedup();
    for v in columns(&vectors).unwrap() {
        let ok = distinct.iter().any(|lambda| {
            m(&format!("{a} * {v} - ({lambda}) * {v}")).is_ok_and(|res| numerically_zero(&res))
        });
        let nonzero = !numerically_zero(&v);
        if !ok || !nonzero {
            return Verdict::Wrong(format!("eigenvector {v} of eigenvalues {values:?}"));
        }
    }
    Verdict::Pass
}

/// Integer matrix from rows of `i64`.
fn integers(matrix: &str) -> Option<Vec<Vec<i64>>> {
    rows(matrix)?
        .iter()
        .map(|r| r.iter().map(|e| e.parse().ok()).collect())
        .collect()
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

/// Check `hermite(A)` and `smith(A)` in `M(Z)`.
fn normal_forms(a: &str) -> Verdict {
    let mz = |input: String| eval_in(SetChoice::MZ, &mut Environment::new(), &input);
    let (Ok(h), Ok(d)) = (mz(format!("hermite({a})")), mz(format!("smith({a})"))) else {
        return Verdict::Skip("unevaluated".to_owned());
    };
    let (Some(hm), Some(dm), Some(am)) = (integers(&h), integers(&d), integers(a)) else {
        return Verdict::Wrong(format!("non-integer forms H = {h}, D = {d}"));
    };
    let env = env_with(&[]);
    let square = am.len() == am[0].len();
    let det = if square {
        number(
            &env,
            &eval(&mut Environment::new(), &format!("det({a})")).unwrap(),
        )
        .unwrap()
    } else {
        0.0
    };
    let rank: usize = eval(&mut Environment::new(), &format!("rank({a})"))
        .unwrap()
        .parse()
        .unwrap();
    // Hermite: row echelon, positive pivots, entries above pivots reduced, rank nonzero rows
    let mut last_pivot: Option<usize> = None;
    let mut nonzero_rows = 0;
    for (i, row) in hm.iter().enumerate() {
        let Some(p) = row.iter().position(|&e| e != 0) else {
            if hm[i..].iter().flatten().any(|&e| e != 0) {
                return Verdict::Wrong(format!("H = {h}: zero row before a nonzero one"));
            }
            break;
        };
        nonzero_rows += 1;
        if last_pivot.is_some_and(|l| p <= l) || row[p] <= 0 {
            return Verdict::Wrong(format!(
                "H = {h} isn't in echelon form with positive pivots"
            ));
        }
        if hm[..i].iter().any(|r| r[p] < 0 || r[p] >= row[p]) {
            return Verdict::Wrong(format!(
                "H = {h}: entries above the pivot of row {i} aren't reduced"
            ));
        }
        last_pivot = Some(p);
    }
    if nonzero_rows != rank {
        return Verdict::Wrong(format!(
            "H = {h} has {nonzero_rows} nonzero rows, rank {rank}"
        ));
    }
    // `H = U A` with `U` unimodular when `A` is invertible
    if square && det.abs() > 0.5 {
        let u = m(&format!("{h} * {a}^-1")).unwrap();
        let unimodular = integers(&u).is_some()
            && eval(&mut Environment::new(), &format!("abs(det({u}))")).as_deref() == Ok("1");
        if !unimodular {
            return Verdict::Wrong(format!("H = {h} isn't U A with U unimodular: H A^-1 = {u}"));
        }
    }
    // Smith: diagonal, non-negative, divisibility chain, product |det|, first entry gcd of entries
    let k = dm.len().min(dm[0].len());
    for (i, row) in dm.iter().enumerate() {
        for (j, &e) in row.iter().enumerate() {
            if i != j && e != 0 {
                return Verdict::Wrong(format!("D = {d} isn't diagonal"));
            }
        }
    }
    let diagonal: Vec<i64> = (0..k).map(|i| dm[i][i]).collect();
    if diagonal.iter().any(|&e| e < 0)
        || diagonal.windows(2).any(|w| {
            if w[0] == 0 {
                w[1] != 0
            } else {
                w[1] % w[0] != 0
            }
        })
    {
        return Verdict::Wrong(format!(
            "D = {d}: diagonal {diagonal:?} isn't a divisibility chain"
        ));
    }
    if diagonal.iter().filter(|&&e| e != 0).count() != rank {
        return Verdict::Wrong(format!("D = {d} doesn't have rank {rank}"));
    }
    let content = am.iter().flatten().fold(0, |g, &e| gcd(g, e));
    if diagonal[0] != content {
        return Verdict::Wrong(format!("D = {d} but the gcd of the entries is {content}"));
    }
    if square && (diagonal.iter().product::<i64>() as f64 - det.abs()).abs() > 0.5 {
        return Verdict::Wrong(format!("D = {d} but |det A| = {}", det.abs()));
    }
    Verdict::Pass
}

#[test]
fn matrices() {
    check_all(
        "linear algebra",
        &[
            "[[2, 1], [1, 2]]",
            "[[2, 1], [0, 2]]",
            "[[1, 2], [3, 4]]",
            "[[0, -1], [1, 0]]",
            "[[1, 2], [2, 4]]",
            "[[2, 0, 0], [0, 3, 4], [0, 4, 9]]",
            "[[1, 1, 1], [1, 1, 1], [1, 1, 1]]",
            "[[4, 1, 2], [0, 3, 1], [0, 0, 3]]",
            "[[1, 2, 3], [4, 5, 6], [7, 8, 9]]",
            "[[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 3, 1], [0, 0, 0, 3]]",
        ],
        linear_algebra,
    );
}

#[test]
fn integer_normal_forms() {
    check_all(
        "normal forms",
        &[
            "[[2, 4], [6, 8]]",
            "[[2, 4, 4], [-6, 6, 12], [10, -4, -16]]",
            "[[1, 2, 3], [4, 5, 6], [7, 8, 9]]",
            "[[6, 4], [4, 6], [2, 2]]",
            "[[0, 0], [0, 3]]",
            "[[3, 5, 7]]",
        ],
        normal_forms,
    );
}

/// A random small matrix: diagonalizable with integer eigenvalues, or with random entries.
fn matrix(rng: &mut Rng) -> String {
    let n = rng.range(2, 3) as usize;
    if rng.chance(0.5) {
        random::diagonalizable(rng, n).0
    } else {
        random::int_matrix(rng, n, n, 3)
    }
}

#[test]
#[ignore = "fuzz: random matrices, run with --ignored"]
fn fuzz_linear_algebra() {
    fuzz("fuzz linear algebra", 60, matrix, linear_algebra);
}

#[test]
#[ignore = "fuzz: random integer matrices, run with --ignored"]
fn fuzz_normal_forms() {
    fuzz(
        "fuzz normal forms",
        100,
        |rng| {
            let (h, w) = (rng.range(1, 4) as usize, rng.range(1, 4) as usize);
            random::int_matrix(rng, h, w, 6)
        },
        normal_forms,
    );
}

#[test]
fn bug_matrix_sum_of_scalar_multiple_and_power() {
    let a = "[[2, 1], [1, 2]]";
    // `A^2 - A` is right
    assert_eq!(m(&format!("{a}^2 + 2*{a}")), m("[[9, 6], [6, 9]]"));
    assert_eq!(m(&format!("{a}^2 - 4*{a}")), m("[[-3, 0], [0, -3]]"));
}

fn regression(input: &str, check: fn(&str) -> Verdict) {
    crate::common::harness::assert_pass(input, std::time::Duration::from_secs(60), check);
}

#[test]
fn bug_smith_of_unimodular_hangs() {
    regression("[[2, 1], [1, 1]]", normal_forms);
}

#[test]
fn bug_eigenvalues_of_cubic_with_complex_roots_hang() {
    // Characteristic polynomial `x^3 - 4 x^2 - 3 x + 37`, with one real root
    regression("[[3, 2, 3], [-2, 2, -1], [3, 1, -1]]", linear_algebra);
}
