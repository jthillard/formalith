//! Solving systems of equations.
mod common;

/// Evaluate each statement in `set`, returning the result of the last one.
fn eval_in(set: &str, statements: &[&str], typst: bool) -> Result<String, String> {
    common::eval_statements(set.parse().unwrap(), statements, typst)
}

/// Solve `system` in `set`, printed as Typst so that the output doesn't depend on colors.
fn solve_in(set: &str, system: &str) -> Result<String, String> {
    eval_in(set, &[system], true)
}

fn solve(system: &str) -> Result<String, String> {
    solve_in("R", system)
}

fn ok(solution: &str) -> Result<String, String> {
    Ok(solution.to_owned())
}

#[test]
fn unique_solution() {
    assert_eq!(solve("x + y = 3, x - y = 1"), ok("x = 2, y = 1"));
    assert_eq!(solve("x + 2*y = 5, 3*x - y = 1"), ok("x = 1, y = 2"));
    assert_eq!(solve("2*x = 3"), ok("x = frac(3, 2)"));
    // Unknowns appear on both sides
    assert_eq!(solve("2*x + 1 = x - 3"), ok("x = -4"));
    // Unknowns are sorted by name
    assert_eq!(solve("b = 1, a = b + 1"), ok("a = 2, b = 1"));
}

#[test]
fn parametric_solution() {
    // `y` is free
    assert_eq!(
        solve("x + y = 1, 2*x + 2*y = 2"),
        solve_in("R", "x = 1 - y")
    );
    assert_eq!(solve("x = x"), ok("\"true\""));
    assert_eq!(solve("0 = 0"), ok("\"true\""));
}

#[test]
fn no_solution() {
    assert_eq!(solve("x + y = 1, x + y = 2"), ok("\"no solution\""));
    assert_eq!(solve("1 = 2"), ok("\"no solution\""));
}

#[test]
fn other_sets() {
    assert_eq!(solve_in("C", "x + i*y = 1, x - y = i"), ok("x = 0, y = -i"));
    assert_eq!(solve_in("Z/7", "3*x = 1"), ok("x = 5"));
    assert_eq!(solve_in("Z/7", "x + y = 2, x - y = 3"), ok("x = 6, y = 3"));
    // Pivots are one
    assert_eq!(solve_in("Z", "x + y = 3, x + 2*y = 5"), ok("x = 1, y = 2"));
    assert_eq!(solve_in("Z", "x + y = 1, x + y = 3"), ok("\"no solution\""));
}

#[test]
fn errors() {
    assert!(solve("abs(x) = 1").unwrap_err().contains("not polynomial"));
    assert!(solve("2^x = 1").unwrap_err().contains("not polynomial"));
    // Irreducible quartic over the rationals, and not a polynomial in `x^k`
    assert!(
        solve("x^4 + x + 1 = 0")
            .unwrap_err()
            .contains("can't solve")
    );
    assert!(
        solve_in("N", "x = 1")
            .unwrap_err()
            .contains("can't be solved")
    );
    assert!(
        solve_in("M", "x = 1")
            .unwrap_err()
            .contains("can't be solved")
    );
    assert_eq!(
        solve("x = 1, 2"),
        Err("expected `=` in each equation of a system".to_owned())
    );
    assert_eq!(
        solve("x = "),
        Err("Expression expected at position 4".to_owned())
    );
    assert!(solve("x = 1 = 2").is_err());
}

#[test]
fn expressions() {
    // Without `=`, a statement is still an expression
    assert_eq!(solve("1 + 2"), ok("3"));
    assert_eq!(solve(""), Err("Input was empty".to_owned()));
}

#[test]
fn definitions() {
    assert_eq!(eval_in("R", &["a := 2", "x + a = 3"], true), ok("x = 1"));
    assert_eq!(
        eval_in("R", &["f(t) := 2*t", "f(x) = 4"], true),
        ok("x = 2")
    );
}

#[test]
fn solve_function() {
    // Other symbols are parameters. Parameters are only used in this test, since the order of factors depends on
    // the order symbols are created in, and tests run in parallel.
    assert_eq!(solve("solve(k*x = h, x)"), ok("x = frac(h, k)"));
    assert_eq!(
        solve("solve(m*x + y = 1, x - y = w, x, y)"),
        ok("x = frac((w+1), (m+1)), y = frac((-m w+1), (m+1))")
    );
    assert_eq!(
        solve("solve(p*x + q*y = r, s*x + v*y = u, x, y)"),
        ok("x = frac((-q u+r v), (p v-q s)), y = frac((p u-r s), (p v-q s))")
    );
    assert_eq!(solve("solve(y = x + g, y)"), ok("y = x+g"));
    assert_eq!(solve("solve(x + y = 1, y)"), ok("y = -x+1"));
    // Without unknowns, every symbol is an unknown
    assert_eq!(solve("solve(x + y = 3, x - y = 1)"), ok("x = 2, y = 1"));
    // Unknowns are in the order given
    assert_eq!(
        solve("solve(x + y = 3, x - y = 1, y, x)"),
        ok("y = 1, x = 2")
    );
    assert_eq!(
        solve("solve(x + k*y = 1, x + k*y = 2, x, y)"),
        ok("\"no solution\"")
    );
    // Coefficients can be any expression without unknowns
    assert_eq!(solve("sqrt(2)*x = 1"), solve("x = sqrt(1/2)"));
    assert_eq!(
        eval_in("R", &["c := 3", "solve(c*x = 2, x)"], true),
        ok("x = frac(2, 3)")
    );
    // Non-linear in the unknowns, `a` being free
    assert_eq!(solve("solve(a*x = 1, x, a)"), ok("x = frac(1, a)"));
    assert_eq!(
        solve("solve(x^2 = c, x)"),
        ok("x = sqrt(c) \\ x = -sqrt(c)")
    );
}

#[test]
fn solve_function_errors() {
    assert_eq!(
        solve("solve(x = 1, 2)"),
        Err("`2` is not an unknown, expected an equation or a symbol".to_owned())
    );
    assert_eq!(
        solve("solve(x = 1, x, x)"),
        Err("Unknown `x` is repeated".to_owned())
    );
    assert_eq!(
        solve("solve(x)"),
        Err("solve expects at least one equation".to_owned())
    );
    assert!(solve("solve(x = 1, x) + 1").is_err());
    assert!(solve("solve(x = 1, x").is_err());
    assert_eq!(
        solve("solve := 2"),
        Err("`solve` is a builtin function".to_owned())
    );
    // `i` is a constant of C, not an unknown
    assert!(solve_in("C", "solve(x = i, i)").is_err());
}

#[test]
fn univariate_polynomials() {
    assert_eq!(solve("x^2 = 1"), ok("x = -1 \\ x = 1"));
    assert_eq!(solve("x^2 - 3*x + 2 = 0"), ok("x = 1 \\ x = 2"));
    assert_eq!(
        solve("x^3 - 6*x^2 + 11*x - 6 = 0"),
        ok("x = 1 \\ x = 2 \\ x = 3")
    );
    // Multiple roots are given once
    assert_eq!(solve("x^2 = 0"), ok("x = 0"));
    assert_eq!(solve("x^2 + 1 = 0"), ok("\"no solution\""));
}

#[test]
fn radicals() {
    assert_eq!(solve("x^2 = 2"), ok("x = sqrt(2) \\ x = -sqrt(2)"));
    assert_eq!(
        solve("x^2 - x - 1 = 0"),
        ok("x = -frac(1, 2) sqrt(5)+frac(1, 2) \\ x = frac(1, 2) sqrt(5)+frac(1, 2)")
    );
    // Polynomials in `x^k`
    assert_eq!(solve("x^4 = 16"), ok("x = -2 \\ x = 2"));
    assert_eq!(solve("x^3 = -8"), ok("x = -2"));
    assert_eq!(solve("x^3 = 2"), ok("x = root(3, 2)"));
    // The sign of a radical is approximated, `2 sqrt(2) - 3 < 0`
    assert_eq!(solve("x^2 = 2*sqrt(2) - 3"), ok("\"no solution\""));
}

#[test]
fn polynomial_systems() {
    // Products are split
    assert_eq!(
        solve("x*y = 0, x + y = 1"),
        ok("x = 0, y = 1 \\ x = 1, y = 0")
    );
    // Substitution
    assert_eq!(
        solve("x^2 + y^2 = 1, x = y"),
        ok(
            "x = -frac(1, 2) sqrt(2), y = -frac(1, 2) sqrt(2) \\ x = frac(1, 2) sqrt(2), y = frac(1, 2) sqrt(2)"
        )
    );
    assert_eq!(
        solve("x^2 + y^2 = 5, x*y = 2"),
        ok("x = -2, y = -1 \\ x = -1, y = -2 \\ x = 1, y = 2 \\ x = 2, y = 1")
    );
    assert_eq!(
        solve("x^2 + y^2 = 3, x^2 - y^2 = 1"),
        ok(
            "x = sqrt(2), y = -1 \\ x = sqrt(2), y = 1 \\ x = -sqrt(2), y = -1 \\ x = -sqrt(2), y = 1"
        )
    );
    // Resultants, no equation being linear in an unknown
    assert_eq!(
        solve("x^2 + y^2 = 2, x^2 = y^3"),
        ok("x = -1, y = 1 \\ x = 1, y = 1")
    );
    assert_eq!(solve("x^2 + y^2 = 1, x^2 + y^2 = 2"), ok("\"no solution\""));
    // Parametric solutions
    assert_eq!(solve("x*y = 1"), ok("x = frac(1, y)"));
    assert_eq!(
        solve("x^2 + y^2 = 1, 2*x^2 + 2*y^2 = 2"),
        ok("x = sqrt(-y^2+1) \\ x = -sqrt(-y^2+1)")
    );
}

#[test]
fn polynomials_in_other_sets() {
    assert_eq!(solve_in("C", "x^2 + 1 = 0"), ok("x = -i \\ x = i"));
    assert_eq!(
        solve_in("C", "x^2 + y^2 = 0, x - y = 2"),
        ok("x = 1+i, y = -1+i \\ x = 1-i, y = -1-i")
    );
    // Radicals
    assert_eq!(solve_in("C", "x^2 = 2"), ok("x = sqrt(2) \\ x = -sqrt(2)"));
    assert_eq!(
        solve_in("C", "x^2 = -2"),
        ok("x = -i sqrt(2) \\ x = i sqrt(2)")
    );
    assert_eq!(
        solve_in("C", "x^2 + x + 1 = 0"),
        ok("x = -frac(1, 2) i sqrt(3)-frac(1, 2) \\ x = frac(1, 2) i sqrt(3)-frac(1, 2)")
    );
    // Square roots of non-real values, `{$sqrt(3 + 4 i) = 2 + i$}`
    assert_eq!(
        solve_in("C", "x^2 - 2*x = 2 + 4*i"),
        ok("x = -1-i \\ x = 3+i")
    );
    assert_eq!(
        solve_in("C", "x^3 = 2").map(|s| s.matches(" \\ ").count()),
        Ok(2)
    );
    assert!(
        solve_in("C", "x^5 = 2")
            .unwrap_err()
            .contains("can't solve")
    );
    assert_eq!(solve_in("Z/7", "x^2 = 2"), ok("x = 3 \\ x = 4"));
    assert_eq!(solve_in("Z/7", "x^2 = 3"), ok("\"no solution\""));
    assert_eq!(solve_in("Z/6", "x^2 = 1"), ok("x = 1 \\ x = 5"));
    assert_eq!(solve_in("Z", "x^2 = 4"), ok("x = -2 \\ x = 2"));
    assert_eq!(solve_in("Z", "x^2 = 2"), ok("\"no solution\""));
    assert_eq!(
        solve_in("Z", "x*y = 0, x + y = 2"),
        ok("x = 0, y = 2 \\ x = 2, y = 0")
    );
}

#[test]
fn printing() {
    // One solution per line
    assert_eq!(eval_in("R", &["x^2 = 1"], false), ok("x = -1\nx = 1 "));
}

#[test]
fn degenerate_systems() {
    assert_eq!(solve("x = x + 1"), ok("\"no solution\""));
    assert_eq!(solve("x^2 + 1 = 0, x = 1"), ok("\"no solution\""));
    // x = y and z = 5 - 2x give x + y + z = 5
    assert_eq!(
        solve("x + y + z = 6, x - y = 0, 2*x + z = 5"),
        ok("\"no solution\"")
    );
    assert_eq!(solve("x + y = 1, 2*x + 2*y = 3"), ok("\"no solution\""));
    assert_eq!(solve("2*x = 3"), ok("x = frac(3, 2)"));
    assert_eq!(solve("solve(a*x = b, x)"), ok("x = frac(b, a)"));
}

#[test]
fn polynomials_with_repeated_and_many_roots() {
    assert_eq!(solve("x^2 - 2*x + 1 = 0"), ok("x = 1"));
    assert_eq!(solve("(x-1)^3 = 0"), ok("x = 1"));
    assert_eq!(solve("x^2 = x"), ok("x = 0 \\ x = 1"));
    assert_eq!(solve("x^4 = 1"), ok("x = -1 \\ x = 1"));
    assert_eq!(solve("x^8 - 1 = 0"), ok("x = -1 \\ x = 1"));
    assert_eq!(solve("x^6 = 64"), ok("x = -2 \\ x = 2"));
    assert_eq!(solve("x^4 + 1 = 0"), ok("\"no solution\""));
    assert_eq!(solve("x^2 = -1"), ok("\"no solution\""));
    assert_eq!(
        solve("x^4 - 5*x^2 + 4 = 0"),
        ok("x = -2 \\ x = -1 \\ x = 1 \\ x = 2")
    );
}

#[test]
fn quadratic_with_symbolic_coefficients() {
    assert_eq!(
        solve("solve(x^2 + p*x + q = 0, x)"),
        ok(
            "x = -frac(1, 2) p+frac(1, 2) sqrt(p^2-4 q) \\ x = -frac(1, 2) p-frac(1, 2) sqrt(p^2-4 q)"
        )
    );
}

#[test]
fn nonlinear_systems() {
    assert_eq!(
        solve("x^2 + y^2 = 1, x = y"),
        ok(
            "x = -frac(1, 2) sqrt(2), y = -frac(1, 2) sqrt(2) \\ x = frac(1, 2) sqrt(2), y = frac(1, 2) sqrt(2)"
        )
    );
    assert_eq!(
        solve("x*y = 6, x + y = 5"),
        ok("x = 2, y = 3 \\ x = 3, y = 2")
    );
    assert_eq!(
        solve("x^2 + y^2 = 25, x*y = 12"),
        ok("x = -4, y = -3 \\ x = -3, y = -4 \\ x = 3, y = 4 \\ x = 4, y = 3")
    );
}

#[test]
fn complex_roots() {
    assert_eq!(solve_in("C", "x^2 = -1"), ok("x = -i \\ x = i"));
    assert_eq!(
        solve_in("C", "x^2 + 2*x + 5 = 0"),
        ok("x = -1+2 i \\ x = -1-2 i")
    );
    assert_eq!(solve_in("C", "(1+i)*x = 2"), ok("x = 1-i"));
    assert_eq!(
        solve_in("C", "x^3 = 1"),
        ok("x = -frac(1, 2) i sqrt(3)-frac(1, 2) \\ x = frac(1, 2) i sqrt(3)-frac(1, 2) \\ x = 1")
    );
    assert_eq!(
        solve_in("C", "x^2 = i"),
        ok("x = (-frac(1, 2)-frac(1, 2) i) sqrt(2) \\ x = (frac(1, 2)+frac(1, 2) i) sqrt(2)")
    );
    // The 6th roots of unity
    assert_eq!(
        solve_in("C", "x^6 = 1").map(|s| s.matches(" \\ ").count() + 1),
        Ok(6)
    );
    assert_eq!(
        solve_in("C", "x^4 = -1").map(|s| s.matches(" \\ ").count() + 1),
        Ok(4)
    );
}

#[test]
fn integer_and_modular_roots() {
    assert_eq!(solve_in("Z", "x^2 = 4"), ok("x = -2 \\ x = 2"));
    assert_eq!(solve_in("Z", "x^2 = 2"), ok("\"no solution\""));
    assert_eq!(solve_in("Z", "x^3 - x = 0"), ok("x = -1 \\ x = 0 \\ x = 1"));
    assert_eq!(solve_in("Z/7", "x^2 = 2"), ok("x = 3 \\ x = 4"));
    assert_eq!(solve_in("Z/7", "x^2 = 3"), ok("\"no solution\""));
    assert_eq!(solve_in("Z/7", "x^3 = 1"), ok("x = 1 \\ x = 2 \\ x = 4"));
    assert_eq!(solve_in("Z/7", "x + y = 1, x - y = 3"), ok("x = 2, y = 6"));
    // Z/6 has zero divisors, x^2 = x has 4 roots
    assert_eq!(
        solve_in("Z/6", "x^2 = x"),
        ok("x = 0 \\ x = 1 \\ x = 3 \\ x = 4")
    );
    assert_eq!(solve_in("Z/6", "2*x = 1"), ok("\"no solution\""));
}

#[test]
fn linear_systems_with_non_invertible_pivots() {
    assert_eq!(solve_in("Z", "2*x = 4"), ok("x = 2"));
    assert_eq!(solve_in("Z", "x + y = 3, x - y = 1"), ok("x = 2, y = 1"));
    assert_eq!(solve_in("Z/6", "2*x = 4"), ok("x = 2 \\ x = 5"));
    assert_eq!(solve_in("Z", "2*x = 3"), ok("\"no solution\""));
    assert_eq!(solve_in("Z", "3*x = 6, 2*x = 4"), ok("x = 2"));
    // Unknowns without pivot stay free when the pivots divide their rows
    assert_eq!(solve_in("Z", "2*x + 4*y = 6"), ok("x = -2 y+3"));
    assert_eq!(
        solve_in("Z", "6*x + 4*y + 2*z = 2, x - z = 1"),
        ok("x = z+1, y = -2 z-1")
    );
    assert_eq!(solve_in("Z", "2*x + 4*y = 3"), ok("\"no solution\""));
}

#[test]
fn linear_systems_with_new_parameters() {
    assert_eq!(
        solve_in("Z", "2*x + 3*y = 1"),
        ok("x = 3 t_1-1, y = -2 t_1+1")
    );
    // `t_1` is taken
    assert_eq!(
        solve_in("Z", "2*x + 3*t_1 = 1"),
        ok("t_1 = -2 t_2+1, x = 3 t_2-1")
    );
    assert_eq!(
        solve_in("Z/6", "2*x + 2*y = 2"),
        ok("x = t_1, y = -t_1+1 \\ x = t_1, y = -t_1+4")
    );
    assert_eq!(
        solve_in("Z/12", "4*x + 6*y = 2, x + y = 1"),
        ok("x = 2, y = 11 \\ x = 8, y = 5")
    );
    assert_eq!(
        solve_in("Z/8", "4*x = 0"),
        ok("x = 0 \\ x = 2 \\ x = 4 \\ x = 6")
    );
}

#[test]
fn cubics_and_quintics() {
    assert!(solve("x^3 + x + 1 = 0").is_ok());
    assert!(solve("x^3 - 3*x + 1 = 0").is_ok());
}

#[test]
fn quartics() {
    // Ferrari's method, the resolvent cubic having the rational root 1
    assert_eq!(
        solve("x^4 - 4*x - 1 = 0"),
        ok(
            "x = -frac(1, 2) sqrt(4 sqrt(2)-2)+frac(1, 2) sqrt(2) \\ x = frac(1, 2) sqrt(4 sqrt(2)-2)+frac(1, 2) sqrt(2)"
        )
    );
    assert_eq!(
        solve_in("C", "x^4 - 4*x - 1 = 0").map(|s| s.matches(" \\ ").count() + 1),
        Ok(4)
    );
    // Shifted, with an irrational resolvent root
    assert!(solve("x^4 + 4*x^3 - 2 = 0").is_ok());
    assert_eq!(
        solve("(x - 1)^4 = 2").map(|s| s.matches(" \\ ").count() + 1),
        Ok(2)
    );
}

#[test]
fn cyclotomic_polynomials() {
    assert_eq!(
        solve_in("C", "x^4 - x^3 + x^2 - x + 1 = 0"),
        ok(
            "x = -frac(1, 4) i sqrt(-2 sqrt(5)+10)+frac(1, 4) sqrt(5)+frac(1, 4) \\ x = -frac(1, 4) i sqrt(2 sqrt(5)+10)-frac(1, 4) sqrt(5)+frac(1, 4) \\ x = frac(1, 4) i sqrt(-2 sqrt(5)+10)+frac(1, 4) sqrt(5)+frac(1, 4) \\ x = frac(1, 4) i sqrt(2 sqrt(5)+10)-frac(1, 4) sqrt(5)+frac(1, 4)"
        )
    );
    assert_eq!(solve("x^4 - x^3 + x^2 - x + 1 = 0"), ok("\"no solution\""));
    // `{$Phi_15$}`, with `{$(2 pi) / 15 = (3 pi) / 10 - pi / 6$}`
    assert_eq!(
        solve_in("C", "x^8 - x^7 + x^5 - x^4 + x^3 - x + 1 = 0")
            .map(|s| s.matches(" \\ ").count() + 1),
        Ok(8)
    );
    // `{$Phi_7$}` has no real radical values
    assert!(solve_in("C", "x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 = 0").is_err());
}

#[test]
fn non_polynomial_equations_are_rejected() {
    for system in ["sin(x) = 0", "exp(x) = 2", "sqrt(x) = 2"] {
        assert!(
            solve(system).unwrap_err().contains("not polynomial"),
            "{system}"
        );
    }
    // Quintic without radical roots
    assert!(
        solve("x^5 - x - 1 = 0")
            .unwrap_err()
            .contains("can't solve")
    );
}

#[test]
fn rational_equations() {
    assert_eq!(solve("1/x = 2"), ok("x = frac(1, 2)"));
    assert_eq!(solve("x/(x-1) = 2"), ok("x = 2"));
    // `x = 1` cancels the denominator
    assert_eq!(solve("x/(x-1) = 1/(x-1)"), ok("\"no solution\""));
}
