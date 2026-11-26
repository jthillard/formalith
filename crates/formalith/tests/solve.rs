//! Solving systems of equations.

/// Evaluate each statement in `set`, returning the result of the last one.
fn eval_in(set: &str, statements: &[&str], typst: bool) -> Result<String, String> {
    crate::common::eval_statements(set.parse().unwrap(), statements, typst)
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
    assert!(solve("abs(x) = y").unwrap_err().contains("not polynomial"));
    assert!(solve("2^x = y").unwrap_err().contains("not polynomial"));
    // Irrational coefficients, without radical roots
    assert!(
        solve("x^5 + sqrt(2)*x + 1 = 0")
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
        ok("x = 1-i, y = -1-i \\ x = 1+i, y = -1+i")
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
            "x = -frac(1, 2) p-frac(1, 2) sqrt(p^2-4 q) \\ x = -frac(1, 2) p+frac(1, 2) sqrt(p^2-4 q)"
        )
    );
}

#[test]
fn vanishing_divisors() {
    // `{$y = (4 - x^2)/x$}` assumes `{$x != 0$}`, the case `{$x = 0$}` being another branch, but the numerator of
    // `{$y^3 + x^2$}` after the substitution had a factor `{$x$}`, giving `{$x = 0, y = 4/0$}`
    let solutions = solve("x*y + x^2 - 4 = 0, y^3 + x^2 = 0").unwrap();
    assert_eq!(solutions.split(" \\ ").count(), 2, "{solutions}");
    assert!(solutions.contains("rootof"), "{solutions}");
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
        ok("x = -1-2 i \\ x = -1+2 i")
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
        ok("x = -t_1+1, y = t_1 \\ x = -t_1+4, y = t_1")
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
    // In `{$CC$}`, the conjugate roots next to Cardano's real root
    let count = |s: Result<String, String>| s.map(|s| s.matches(" \\ ").count() + 1);
    assert_eq!(count(solve_in("C", "x^3 + x + 1 = 0")), Ok(3));
    assert_eq!(count(solve_in("C", "x^3 - 3*x + 1 = 0")), Ok(3));
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
            "x = -frac(1, 4) i sqrt(-2 sqrt(5)+10)+frac(1, 4) sqrt(5)+frac(1, 4) \\ x = frac(1, 4) i sqrt(-2 sqrt(5)+10)+frac(1, 4) sqrt(5)+frac(1, 4) \\ x = -frac(1, 4) i sqrt(2 sqrt(5)+10)-frac(1, 4) sqrt(5)+frac(1, 4) \\ x = frac(1, 4) i sqrt(2 sqrt(5)+10)-frac(1, 4) sqrt(5)+frac(1, 4)"
        )
    );
    assert_eq!(solve("x^4 - x^3 + x^2 - x + 1 = 0"), ok("\"no solution\""));
    // `{$Phi_15$}`, with `{$(2 pi) / 15 = (3 pi) / 10 - pi / 6$}`
    assert_eq!(
        solve_in("C", "x^8 - x^7 + x^5 - x^4 + x^3 - x + 1 = 0")
            .map(|s| s.matches(" \\ ").count() + 1),
        Ok(8)
    );
    // `{$Phi_7$}` has no real radical values, its roots are written with `sin` and `cos`
    assert_eq!(
        solve_in("C", "x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 = 0"),
        ok(
            "x = -i sin(frac(2, 7) pi)+cos(frac(2, 7) pi) \\ x = i sin(frac(2, 7) pi)+cos(frac(2, 7) pi) \\ x = -i sin(frac(4, 7) pi)+cos(frac(4, 7) pi) \\ x = i sin(frac(4, 7) pi)+cos(frac(4, 7) pi) \\ x = -i sin(frac(6, 7) pi)+cos(frac(6, 7) pi) \\ x = i sin(frac(6, 7) pi)+cos(frac(6, 7) pi)"
        )
    );
    assert_eq!(
        solve_in("C", "x^7 = 1").map(|s| s.matches(" \\ ").count() + 1),
        Ok(7)
    );
    assert_eq!(solve("x^7 = 1"), ok("x = 1"));
}

#[test]
fn non_polynomial_equations_are_rejected() {
    for system in [
        "sin(x) = x",
        "x + sin(x) = 1",
        "exp(x) = x^2",
        "x + y = 1, sin(x) = y",
    ] {
        assert!(
            solve(system).unwrap_err().contains("not polynomial"),
            "{system}"
        );
    }
}

#[test]
fn polynomials_without_radical_roots() {
    assert_eq!(
        solve("x^5 - x - 1 = 0"),
        ok("x = op(\"rootof\")(-x+x^5-1, 1)")
    );
    assert_eq!(
        solve("x^5 - 5*x + 1 = 0"),
        ok(
            "x = op(\"rootof\")(-5 x+x^5+1, 1) \\ x = op(\"rootof\")(-5 x+x^5+1, 2) \\ \
            x = op(\"rootof\")(-5 x+x^5+1, 3)"
        )
    );
    assert_eq!(
        solve("(x^2 - 2)*(x^5 - x - 1) = 0"),
        ok("x = sqrt(2) \\ x = -sqrt(2) \\ x = op(\"rootof\")(-x+x^5-1, 1)")
    );
    assert_eq!(
        solve("x^6 = x + 1, x > 0"),
        ok("x = op(\"rootof\")(-x+x^6-1, 2)")
    );
    // Irreducible quartic over the rationals without real root, whose radicals aren't found
    assert_eq!(solve("x^4 + x + 1 = 0"), ok("\"no solution\""));
    // In `{$CC$}`, Ferrari's method with the resolvent root in trigonometric form
    assert_eq!(
        solve_in("C", "x^4 + x + 1 = 0").map(|s| s.matches(" \\ ").count() + 1),
        Ok(4)
    );
}

#[test]
fn rational_equations() {
    assert_eq!(solve("1/x = 2"), ok("x = frac(1, 2)"));
    assert_eq!(solve("x/(x-1) = 2"), ok("x = 2"));
    // `x = 1` cancels the denominator
    assert_eq!(solve("x/(x-1) = 1/(x-1)"), ok("\"no solution\""));
}

#[test]
fn inequalities() {
    assert_eq!(
        solve("x^2 - 3*x + 2 > 0"),
        ok("x in (-oo, 1) union (2, oo)")
    );
    assert_eq!(solve("x^2 <= 4"), ok("x in [-2, 2]"));
    // Roots of the denominator are excluded
    assert_eq!(
        solve("(x-1)/(x+2) >= 0"),
        ok("x in (-oo, -2) union [1, oo)")
    );
    assert_eq!(solve("x^2 + 1 < 0"), ok("\"no solution\""));
    assert_eq!(solve("x^2 >= 0"), ok("x in RR"));
    assert_eq!(solve("x^2 <= 0"), ok("x = 0"));
    assert_eq!(solve("x^2*(x-1) >= 0"), ok("x in {0} union [1, oo)"));
    assert_eq!(solve("x != 1"), ok("x in (-oo, 1) union (1, oo)"));
    assert_eq!(solve("x^2 < 2"), ok("x in (-sqrt(2), sqrt(2))"));
    assert_eq!(solve("1 < 2"), ok("\"true\""));
}

#[test]
fn systems_of_inequalities() {
    assert_eq!(solve("x > 0, x^2 < 4"), ok("x in (0, 2)"));
    assert_eq!(solve("x^2 - 2 > 0, x < 0"), ok("x in (-oo, -sqrt(2))"));
    // Equations restrict the solutions to points
    assert_eq!(solve("x^2 = 4, x > 0"), ok("x = 2"));
    assert_eq!(
        solve("solve(x^3 < x, x)"),
        ok("x in (-oo, -1) union (0, 1)")
    );
}

#[test]
fn inequalities_in_several_unknowns() {
    assert_eq!(solve("x > 0, y > 0"), ok("x in (0, oo), y in (0, oo)"));
    assert_eq!(
        solve("x^2 + y^2 < 1"),
        ok("x in (-1, 1), y in (-sqrt(-x^2+1), sqrt(-x^2+1))")
    );
    // Points where the bounds meet are merged
    assert_eq!(
        solve("x^2 + y^2 <= 1"),
        ok("x in [-1, 1], y in [-sqrt(-x^2+1), sqrt(-x^2+1)]")
    );
    assert_eq!(solve("y > x^2, y < 1"), ok("x in (-1, 1), y in (x^2, 1)"));
    assert_eq!(
        solve("x*y > 0"),
        ok("x in (-oo, 0), y in (-oo, 0) \\ x in (0, oo), y in (0, oo)")
    );
    assert_eq!(
        solve("y^2 > x"),
        ok("x in (-oo, 0), y in RR \\ x in [0, oo), y in (-oo, -sqrt(x)) union (sqrt(x), oo)")
    );
    assert_eq!(
        solve("a*x > 1"),
        ok("a in (-oo, 0), x in (-oo, frac(1, a)) \\ a in (0, oo), x in (frac(1, a), oo)")
    );
    assert_eq!(
        solve("x + y = 1, x != y"),
        ok("x in (-oo, frac(1, 2)), y = -x+1 \\ x in (frac(1, 2), oo), y = -x+1")
    );
    // The lines cross at `{$x = -4/3$}`, sampling must not land on it
    assert_eq!(
        solve("y < -2*x - 3, y < x + 1"),
        ok(
            "x in (-oo, -frac(4, 3)], y in (-oo, x+1) \\ x in (-frac(4, 3), oo), y in (-oo, -2 x-3)"
        )
    );
    // The unknowns in the given order
    assert_eq!(solve("solve(x > 0, x, y)"), ok("x in (0, oo), y in RR"));
    assert_eq!(
        solve("solve(x^2 + y^2 < 1, y, x)"),
        ok("y in (-1, 1), x in (-sqrt(-y^2+1), sqrt(-y^2+1))")
    );
    assert_eq!(
        solve("x^2 + y^2 + z^2 < 1"),
        ok(
            "x in (-1, 1), y in (-sqrt(-x^2+1), sqrt(-x^2+1)), z in (-sqrt(-x^2-y^2+1), sqrt(-x^2-y^2+1))"
        )
    );
}

#[test]
fn unsupported_inequalities() {
    assert!(solve("sin(x) > 0").unwrap_err().contains("not polynomial"));
    assert!(
        solve("solve(x > a, x)")
            .unwrap_err()
            .contains("without parameters")
    );
    assert!(solve_in("Z", "x > 1").is_err());
}

#[test]
fn trigonometric_equations() {
    assert_eq!(
        solve("sin(x) = 1/2"),
        ok("x = frac(1, 6) pi+2 pi k \\ x = frac(5, 6) pi+2 pi k \\ k in ZZ")
    );
    assert_eq!(solve("cos(x) = 0"), ok("x = frac(1, 2) pi+pi k \\ k in ZZ"));
    assert_eq!(solve("cos(x) = 1"), ok("x = 2 pi k \\ k in ZZ"));
    assert_eq!(
        solve("tan(2*x) = 1"),
        ok("x = frac(1, 8) pi+frac(1, 2) pi k \\ k in ZZ")
    );
    // A polynomial in `sin(x)`
    assert_eq!(
        solve("2*sin(x)^2 = 1").map(|s| s.matches(" \\ ").count()),
        Ok(4)
    );
    assert_eq!(solve("sin(x) = 2"), ok("\"no solution\""));
    // `k` is taken, the parameter is `k_1`
    assert_eq!(
        solve("solve(sin(x) = k, x)"),
        ok("x = arcsin(k)+2 pi k_1 \\ x = pi-arcsin(k)+2 pi k_1 \\ k_1 in ZZ")
    );
}

#[test]
fn exponential_and_logarithmic_equations() {
    assert_eq!(solve("exp(x) = 3"), ok("x = ln(3)"));
    assert_eq!(solve("exp(x) = -1"), ok("\"no solution\""));
    assert_eq!(solve("ln(x) = 2"), ok("x = exp(2)"));
    assert_eq!(solve("2^x = 8"), ok("x = 3"));
    // A polynomial in `{$e^x$}`
    assert_eq!(
        solve("exp(2*x) - 3*exp(x) + 2 = 0"),
        ok("x = ln(2) \\ x = 0")
    );
    assert_eq!(solve("x + sqrt(x) = 6"), ok("x = 4"));
    assert_eq!(solve("sqrt(x) = -2"), ok("\"no solution\""));
    assert_eq!(solve("abs(x - 1) = 3"), ok("x = -2 \\ x = 4"));
    assert_eq!(solve("atan(x) = 2"), ok("\"no solution\""));
    assert_eq!(solve("abs(x) = 1"), ok("x = -1 \\ x = 1"));
    assert_eq!(solve("2^x = 1"), ok("x = 0"));
    // A polynomial times an exponential, which never vanishes
    assert_eq!(solve("x^2*exp(2*x) - exp(2*x) = 0"), ok("x = -1 \\ x = 1"));
    assert_eq!(solve("x^2*exp(-x) = 4*exp(-x)"), ok("x = -2 \\ x = 2"));
}

#[test]
fn lambert_equations() {
    assert_eq!(solve("x*exp(x) = 1"), ok("x = W(1)"));
    assert_eq!(
        solve("2*x*exp(3*x) = 5"),
        ok("x = frac(1, 3) W(frac(15, 2))")
    );
    assert_eq!(solve("lambertw(x) = 2"), ok("x = 2 exp(2)"));
    // Both branches for arguments in `{$(-1/e, 0)$}`
    assert_eq!(
        solve("x*exp(x) = -1/(2*e)"),
        ok("x = W(-frac(1, 2) exp(-1)) \\ x = W_(-1)(-frac(1, 2) exp(-1))")
    );
    assert_eq!(solve("x*exp(x) = -exp(-1)"), ok("x = -1"));
    assert_eq!(solve("x*exp(x) = -1"), ok("\"no solution\""));
    assert_eq!(solve("lambertw(x, -1) = -2"), ok("x = -2 exp(-2)"));
    assert_eq!(solve("lambertw(x, -1) = 2"), ok("\"no solution\""));
}

#[test]
fn trigonometric_equations_with_half_angle_forms() {
    // `{$tan x = (1 - sin 1)/cos 1 = tan(pi/4 - 1/2)$}`
    assert_eq!(
        solve("sin(x+1) = cos(x)"),
        ok("x = frac(1, 4) pi+pi k-frac(1, 2) \\ k in ZZ")
    );
    assert_eq!(
        solve("cos(x) + sin(x - 1) = 0"),
        ok("x = -frac(1, 4) pi+pi k+frac(1, 2) \\ k in ZZ")
    );
    // The amplitude `{$sqrt((1 + cos 1)^2 + sin(1)^2) = 2 cos(1/2)$}`, by `{$sin^2 + cos^2 = 1$}` and the half angle
    assert_eq!(
        solve("sin(x) + sin(x + 1) = 1"),
        ok(
            "x = arcsin(frac(frac(1, 2), cos(frac(1, 2))))+2 pi k-frac(1, 2) \\ x = pi-arcsin(frac(frac(1, 2), cos(frac(1, 2))))+2 pi k-frac(1, 2) \\ k in ZZ"
        )
    );
}

#[test]
fn trigonometric_equations_of_a_common_angle() {
    // Homogeneous in `{$sin x$}` and `{$cos x$}`: a polynomial in `{$tan x$}`
    assert_eq!(
        solve("sin(x) = cos(x)"),
        ok("x = frac(1, 4) pi+pi k \\ k in ZZ")
    );
    assert_eq!(
        solve("solve(sin(x) = a*cos(x), x)"),
        ok("x = arctan(a)+pi k \\ k in ZZ")
    );
    // `{$1 = sin^2 x + cos^2 x$}` makes it homogeneous, `{$cos x = 0$}` is a solution too
    assert_eq!(
        solve("sin(x)^2 + sin(x)*cos(x) = 1"),
        ok("x = frac(1, 4) pi+pi k \\ x = frac(1, 2) pi+pi k \\ k in ZZ")
    );
    // Linear: `{$R sin(x + phi) = c$}`
    assert_eq!(
        solve("sin(x) + cos(x) = 1"),
        ok("x = 2 pi k \\ x = frac(1, 2) pi+2 pi k \\ k in ZZ")
    );
    assert_eq!(
        solve("2*sin(x) - 3*cos(x) = 1"),
        ok(
            "x = arcsin(frac(1, 13) sqrt(13))+arctan(frac(3, 2))+2 pi k \\ x = pi-arcsin(frac(1, 13) sqrt(13))+arctan(frac(3, 2))+2 pi k \\ k in ZZ"
        )
    );
    assert_eq!(solve("sin(x) + cos(x) = 2"), ok("\"no solution\""));
    // Multiple angles, with only even powers of `{$cos x$}`: a polynomial in `{$sin x$}`
    assert_eq!(
        solve("cos(2*x) = sin(x)"),
        ok(
            "x = -frac(1, 2) pi+2 pi k \\ x = frac(1, 6) pi+2 pi k \\ x = frac(5, 6) pi+2 pi k \\ k in ZZ"
        )
    );
    assert_eq!(
        solve("sin(x/2) = cos(x)"),
        ok("x = -pi+4 pi k \\ x = frac(1, 3) pi+4 pi k \\ x = frac(5, 3) pi+4 pi k \\ k in ZZ")
    );
    assert_eq!(
        solve("tan(2*x) = 1"),
        ok("x = frac(1, 8) pi+frac(1, 2) pi k \\ k in ZZ")
    );
    // Zeros of the cosines dividing `tan` are excluded
    assert_eq!(
        solve("tan(x) = 2*sin(x)"),
        ok("x = pi k \\ x = -frac(1, 3) pi+2 pi k \\ x = frac(1, 3) pi+2 pi k \\ k in ZZ")
    );
    assert_eq!(solve("tan(x)*cos(x) = 1"), ok("\"no solution\""));
}

#[test]
fn exponentials_of_several_bases_and_logarithms() {
    // Perfect powers share their base
    assert_eq!(solve("4^x - 3*2^x + 2 = 0"), ok("x = 0 \\ x = 1"));
    assert_eq!(solve("8^x = 4"), ok("x = frac(2, 3)"));
    // Taking logarithms
    assert_eq!(solve("2^x = 3^(x+1)"), ok("x = frac(ln(3), (ln(2)-ln(3)))"));
    assert_eq!(solve("e^x = 2^x"), ok("x = 0"));
    assert_eq!(solve("2^x = -3^x"), ok("\"no solution\""));
    assert_eq!(solve("x^x = 2"), ok("x = frac(ln(2), W(ln(2)))"));
    // Hyperbolic functions as exponentials
    assert_eq!(solve("sinh(x) = 2*cosh(x) - 2"), ok("x = ln(3) \\ x = 0"));
    // Lambert W
    assert_eq!(
        solve("2^x = 3*x"),
        ok("x = -frac(W(-frac(1, 3) ln(2)), ln(2)) \\ x = -frac(W_(-1)(-frac(1, 3) ln(2)), ln(2))")
    );
    assert_eq!(solve("exp(x) + x = 0"), ok("x = -W(1)"));
    assert_eq!(solve("ln(x) = 2 - x"), ok("x = W(exp(2))"));
    assert_eq!(solve("x*ln(x) = 0"), ok("x = 1"));
}

#[test]
fn sums_of_exponentials_of_several_bases() {
    // At most one root by Descartes' rule of signs, found exactly
    assert_eq!(solve("2^x + 3^x = 5"), ok("x = 1"));
    assert_eq!(solve("2^x + 3^x + 6^x = 3"), ok("x = 0"));
    assert_eq!(solve("exp(x) + 2^x = 2"), ok("x = 0"));
    assert_eq!(solve("2^x + 3^(x+1) = 11"), ok("x = 1"));
    // No sign change
    assert_eq!(solve("2^x + 3^x = -1"), ok("\"no solution\""));
    // The root isn't rational, there is no exact form
    assert!(solve("2^x + 3^x = 7").unwrap_err().contains("can't solve"));
}

#[test]
fn unrelated_angles() {
    // `{$sin x - sin(x^2 + pi/2) = 2 cos((x^2 + x + pi/2)/2) sin((x - x^2 - pi/2)/2)$}`
    assert_eq!(
        solve("sin(x) = cos(x^2)"),
        ok(
            "x = -frac(1, 4) sqrt(8 pi+32 pi n+4)-frac(1, 2) \\ x = frac(1, 4) sqrt(8 pi+32 pi n+4)-frac(1, 2) \\ \
            x = -frac(1, 4) sqrt(24 pi+32 pi n+4)+frac(1, 2) \\ x = frac(1, 4) sqrt(24 pi+32 pi n+4)+frac(1, 2) \\ \
            n in NN"
        )
    );
    assert_eq!(
        solve("cos(x) + cos(x^2) = 0").map(|s| s.matches(" \\ ").count()),
        Ok(4)
    );
    // Unrelated `tan` and coefficients of different sizes are unsupported
    assert!(solve("sin(x) = 2*cos(x^2)").is_err());
    assert!(solve("tan(x) = tan(x^2)").is_err());
}

#[test]
fn ranges_of_integer_parameters() {
    // `{$x^2 = pi/6 + 2 k pi$}` needs `{$k >= 0$}`
    assert_eq!(
        solve("sin(x^2) = 1/2"),
        ok(
            "x = sqrt(frac(1, 6) pi+2 pi n) \\ x = sqrt(frac(5, 6) pi+2 pi n) \\ \
            x = -sqrt(frac(1, 6) pi+2 pi n) \\ x = -sqrt(frac(5, 6) pi+2 pi n) \\ n in NN"
        )
    );
    // `{$sqrt(x) = pi/6 + 2 k pi$}` too, though its square is always real
    assert_eq!(
        solve("sin(sqrt(x)) = 1/2"),
        ok("x = frac(1, 36) pi^2+frac(2, 3) pi^2 n+4 pi^2 n^2 \\ \
            x = frac(25, 36) pi^2+frac(10, 3) pi^2 n+4 pi^2 n^2 \\ n in NN")
    );
    // An upper bound
    assert_eq!(
        solve("sin(-x^2) = 1/2"),
        ok(
            "x = sqrt(frac(7, 6) pi+2 pi n) \\ x = sqrt(frac(11, 6) pi+2 pi n) \\ \
            x = -sqrt(frac(7, 6) pi+2 pi n) \\ x = -sqrt(frac(11, 6) pi+2 pi n) \\ n in NN"
        )
    );
    // Odd roots need no condition
    assert!(solve("cos(x^(1/3)) = 0").unwrap().ends_with("k in ZZ"));
}

#[test]
fn trigonometric_polynomials_without_radical_roots() {
    // A sextic in `{$tan(x/2)$}`
    assert_eq!(
        solve("sin(3*x) + cos(x) = 1/3"),
        ok(
            "x = 2 arctan(op(\"rootof\")(-9 x+30 x^3+3 x^4-9 x^5+2 x^6-1, 1))+2 pi k \\ \
            x = 2 arctan(op(\"rootof\")(-9 x+30 x^3+3 x^4-9 x^5+2 x^6-1, 2))+2 pi k \\ \
            x = 2 arctan(op(\"rootof\")(-9 x+30 x^3+3 x^4-9 x^5+2 x^6-1, 3))+2 pi k \\ \
            x = 2 arctan(op(\"rootof\")(-9 x+30 x^3+3 x^4-9 x^5+2 x^6-1, 4))+2 pi k \\ k in ZZ"
        )
    );
}

#[test]
fn fractional_powers_terminate() {
    // The polynomial solver used to loop on `{$x + sqrt(x)$}` while factoring it
    for (set, system) in [("R", "x + sqrt(x) = 0, y = 1"), ("C", "x + sqrt(x) = 0")] {
        assert!(
            solve_in(set, system)
                .unwrap_err()
                .contains("not polynomial"),
            "{system}"
        );
    }
    assert_eq!(solve("x + sqrt(x) = 0"), ok("x = 0"));
}

#[test]
fn integer_equations_are_factored() {
    assert_eq!(solve_in("Z", "2*x^2 - 5*x - 3 = 0"), ok("x = 3"));
    assert_eq!(solve_in("Z", "(2*x - 1)*(x + y) = 0"), ok("x = -y"));
}
