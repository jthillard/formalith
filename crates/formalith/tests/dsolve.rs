//! Ordinary differential equations with `dsolve`.

/// Evaluate `statement` in `set`, printed as Typst so that the output doesn't depend on colors.
fn dsolve_in(set: &str, statement: &str) -> Result<String, String> {
    crate::common::eval_statements(set.parse().unwrap(), &[statement], true)
}

fn dsolve(statement: &str) -> Result<String, String> {
    dsolve_in("R", statement)
}

/// The solutions `y(x) = f \\ y(x) = g`, each side being evaluated, so that terms are ordered like in the result
/// (the order of symbols depends on when they were created).
fn ok(solution: &str) -> Result<String, String> {
    let branches: Vec<_> = solution
        .split(" \\ ")
        .map(|branch| {
            let sides: Vec<_> = branch
                .split(" = ")
                .map(|side| dsolve(side).unwrap())
                .collect();
            sides.join(" = ")
        })
        .collect();
    Ok(branches.join(" \\ "))
}

#[test]
fn first_order_linear() {
    assert_eq!(dsolve("dsolve(y' = y)"), ok("y(x) = c_1*exp(x)"));
    assert_eq!(
        dsolve("dsolve(y' + 2*x*y = x)"),
        ok("y(x) = c_1*exp(-x^2) + 1/2")
    );
    assert_eq!(dsolve("dsolve(y' = cos(x))"), ok("y(x) = c_1 + sin(x)"));
    // Integrating factor `x`, from `{$e^(ln|x|)$}`
    assert_eq!(
        dsolve("dsolve(x*y' + y = x^2)"),
        ok("y(x) = (x^3/3 + c_1)/x")
    );
    // Implicit products
    assert_eq!(
        dsolve("dsolve(y' + 2 x y = x)"),
        dsolve("dsolve(y' + 2*x*y = x)")
    );
    assert_eq!(
        dsolve("dsolve(x y' + y = x^2)"),
        dsolve("dsolve(x*y' + y = x^2)")
    );
}

#[test]
fn separable() {
    assert_eq!(
        dsolve("dsolve(y' = y^2)"),
        ok("y(x) = -1/(x + c_1) \\ y(x) = 0")
    );
    assert_eq!(
        dsolve("dsolve(y' = x*y^2)"),
        ok("y(x) = -2/(x^2 + 2*c_1) \\ y(x) = 0")
    );
    // `{$y = 1$}` is the solution with `{$c_1 = 0$}`, so only `{$y = -1$}` is added
    assert_eq!(
        dsolve("dsolve(y' = y^2 - 1)"),
        ok("y(x) = (c_1*exp(2x) + 1)/(1 - c_1*exp(2x)) \\ y(x) = -1")
    );
    assert_eq!(
        dsolve("dsolve(y' = exp(x - y))"),
        ok("y(x) = ln(c_1 + exp(x))")
    );
    assert_eq!(
        dsolve("dsolve(y' = x / y)"),
        ok("y(x) = sqrt(x^2 + 2*c_1) \\ y(x) = -sqrt(x^2 + 2*c_1)")
    );
    // Logarithms are combined, `{$ln|y| - ln|y - 1| = x + c$}`
    assert_eq!(
        dsolve("dsolve(y' = y*(1 - y))"),
        ok("y(x) = -c_1*exp(x)/(1 - c_1*exp(x)) \\ y(x) = 1")
    );
    // Kept implicit
    assert_eq!(
        dsolve("dsolve(y' = 1/(y + exp(y)))"),
        ok("exp(y(x)) + y(x)^2/2 = x + c_1")
    );
}

#[test]
fn constant_coefficients() {
    assert_eq!(
        dsolve("dsolve(y'' + y = 0)"),
        ok("y(x) = c_1*cos(x) + c_2*sin(x)")
    );
    // Double root
    assert_eq!(
        dsolve("dsolve(y'' - 2y' + y = 0)"),
        ok("y(x) = c_1*exp(x) + x*c_2*exp(x)")
    );
    assert_eq!(
        dsolve("dsolve(y'' + 2y' + 5y = 0)"),
        ok("y(x) = c_1*exp(-x)*cos(2x) + c_2*exp(-x)*sin(2x)")
    );
    assert_eq!(
        dsolve("dsolve(y'' - 2y = 0)"),
        ok("y(x) = c_1*exp(-x*sqrt(2)) + c_2*exp(x*sqrt(2))")
    );
    // Complex roots with radicals
    assert_eq!(
        dsolve("dsolve(y''' - y = 0)"),
        ok("y(x) = c_1*exp(x) + c_2*exp(-x/2)*cos(x*sqrt(3)/2) + c_3*exp(-x/2)*sin(x*sqrt(3)/2)")
    );
}

#[test]
fn particular_solutions() {
    assert_eq!(
        dsolve("dsolve(y'' - 3y' + 2y = exp(3x))"),
        ok("y(x) = exp(3x)/2 + c_1*exp(2x) + c_2*exp(x)")
    );
    assert_eq!(
        dsolve("dsolve(y'' + y = x)"),
        ok("y(x) = x + c_1*cos(x) + c_2*sin(x)")
    );
    // Resonance
    assert_eq!(
        dsolve("dsolve(y'' + y = sin(x))"),
        ok("y(x) = -x*cos(x)/2 + c_1*cos(x) + c_2*sin(x)")
    );
    // Constants of the particular solution are absorbed by `c_1`
    assert_eq!(
        dsolve("dsolve(y''' - y' = x)"),
        ok("y(x) = -x^2/2 + c_1 + c_2*exp(x) + c_3*exp(-x)")
    );
    assert_eq!(
        dsolve("dsolve(y'' + y = tan(x))"),
        ok(
            "y(x) = c_1*cos(x) + c_2*sin(x) + ln(abs(sin(x) - 1))*cos(x)/2 - ln(abs(sin(x) + 1))*cos(x)/2"
        )
    );
}

#[test]
fn initial_conditions() {
    assert_eq!(dsolve("dsolve(y' = y, y(0) = 2)"), ok("y(x) = 2*exp(x)"));
    assert_eq!(
        dsolve("dsolve(y'' + y = 0, y(0) = 1, y'(0) = 0)"),
        ok("y(x) = cos(x)")
    );
    assert_eq!(
        dsolve("dsolve(y'' + 4y = cos(x), y(0) = 0, y'(0) = 0)"),
        ok("y(x) = cos(x)/3 - cos(2x)/3")
    );
    assert_eq!(
        dsolve("dsolve(y' = y^2, y(0) = 1)"),
        ok("y(x) = -1/(x - 1)")
    );
    // Only the constant solution satisfies the condition
    assert_eq!(dsolve("dsolve(y' = y^2, y(0) = 0)"), ok("y(x) = 0"));
    // A single condition for an equation of order 2
    assert_eq!(
        dsolve("dsolve(y'' + y = 0, y(0) = 3)"),
        ok("y(x) = 3*cos(x) + c_2*sin(x)")
    );
    // Implicit solutions
    assert_eq!(
        dsolve("dsolve(y' = 1/(y + exp(y)), y(0) = 0)"),
        ok("exp(y(x)) + y(x)^2/2 = x + 1")
    );
}

#[test]
fn slope_conditions() {
    // `{$y'(a) = b$}` gives `{$y(a)$}` through the equation
    assert_eq!(dsolve("dsolve(y' = y, y'(0) = 3)"), ok("y(x) = 3*exp(x)"));
    assert_eq!(
        dsolve("dsolve(y' = x/y, y'(1) = 2)"),
        ok("y(x) = sqrt(x^2 - 3/4)")
    );
    // `{$y(0) = plus.minus 1$}`
    assert_eq!(
        dsolve("dsolve(y' = y^2, y'(0) = 1)"),
        ok("y(x) = -1/(x + 1) \\ y(x) = -1/(x - 1)")
    );
    assert_eq!(
        dsolve("dsolve(y' = y^2, y'(0) = -1)"),
        Err("no solution satisfies the initial conditions".to_owned())
    );
    // Implicit solutions, `{$y(0) = 0$}`
    assert_eq!(
        dsolve("dsolve(y' = 1/(y + exp(y)), y'(0) = 1)"),
        ok("exp(y(x)) + y(x)^2/2 = x + 1")
    );
}

#[test]
fn power_series() {
    // Airy's equation
    assert_eq!(
        dsolve("dsolve(y'' + x*y = 0)").unwrap(),
        "y(x) = c_1 sum_(k = 0)^(+oo) frac(x^(3 k) Gamma(frac(2, 3)) (-1)^k 9^(-k), k! Gamma(k+frac(2, 3)))+c_2 \
         sum_(k = 0)^(+oo) frac(x^(3 k+1) Gamma(frac(4, 3)) (-1)^k 9^(-k), k! Gamma(k+frac(4, 3)))"
    );
    assert_eq!(
        dsolve("dsolve(y'' + x*y = 0, y(0) = 1, y'(0) = 0)").unwrap(),
        "y(x) = sum_(k = 0)^(+oo) frac(x^(3 k) Gamma(frac(2, 3)) (-1)^k 9^(-k), k! Gamma(k+frac(2, 3)))"
    );
    assert_eq!(
        dsolve("dsolve(y'' - x*y' - y = 0)").unwrap(),
        "y(x) = c_1 sum_(k = 0)^(+oo) frac(x^(2 k) 2^(-k), k!)+c_2 sum_(k = 0)^(+oo) frac(x^(2 k+1) (k+1)! \
         2^(k+1), (2 k+2)!)"
    );
    // Hermite's equation, with a polynomial solution
    assert_eq!(
        dsolve("dsolve(y'' - 2*x*y' + 2*y = 0)").unwrap(),
        "y(x) = x c_2+c_1 sum_(k = 0)^(+oo) -frac(x^(2 k), (2 k-1) k!)"
    );
    // Legendre's equation, converging for `{$|x| < 1$}`
    assert_eq!(
        dsolve("dsolve((1 - x^2)*y'' - 2*x*y' + 6*y = 0)").unwrap(),
        "y(x) = c_1 (-3 x^2+1)+c_2 sum_(k = 0)^(+oo) -4 frac((k+1) x^(2 k+1), (16 k^2-4))"
    );
    assert_eq!(
        dsolve("dsolve(x*y'' + y = 0)"),
        Err("`0` is a singular point of the equation".to_owned())
    );
    assert_eq!(
        dsolve("dsolve(y'' + (1 + x)*y = 0)"),
        Err("no closed general term was found for the power series solutions".to_owned())
    );
    assert_eq!(
        dsolve("dsolve(y'' + x*y = x)"),
        Err(
            "only homogeneous linear equations can be solved with non-constant coefficients"
                .to_owned()
        )
    );
}

#[test]
fn function_and_variable() {
    assert_eq!(
        dsolve("dsolve(diff(y(t), t) = t, y, t)"),
        ok("y(t) = c_1 + t^2/2")
    );
    // The variable is found in `y(t)`
    assert_eq!(
        dsolve("dsolve(diff(y(t), t) = y(t)^2)"),
        ok("y(t) = -1/(c_1 + t) \\ y(t) = 0")
    );
    assert_eq!(dsolve("dsolve(f' = f, f, x)"), ok("f(x) = c_1*exp(x)"));
    // Constants already used in the equation are skipped
    assert_eq!(dsolve("dsolve(y' = c_1*y)"), ok("y(x) = c_2*exp(x*c_1)"));
}

#[test]
fn unsupported() {
    assert_eq!(
        dsolve("dsolve(y'' = y^2)"),
        Err("only linear equations can be solved above the first order".to_owned())
    );
    assert_eq!(
        dsolve("dsolve(y'' + sin(x)*y = 0)"),
        Err(
            "the coefficients of a linear equation must be rational functions of the variable"
                .to_owned()
        )
    );
    assert_eq!(
        dsolve("dsolve(y' = y, y(0) = 1, y(1) = 2)"),
        Err("too many initial conditions for an equation of order 1".to_owned())
    );
    assert_eq!(
        dsolve("dsolve(y = x, y, x)"),
        Err("the equation contains no derivative of `y`".to_owned())
    );
    assert_eq!(
        dsolve("dsolve(y' = y(2*x))"),
        Err("`y` must be evaluated at `x` in the equation".to_owned())
    );
    assert!(dsolve("1 + dsolve(y' = y)").is_err());
    assert!(dsolve("x'").is_err());
    for set in ["C", "Z"] {
        assert_eq!(
            dsolve_in(set, "dsolve(y' = y)"),
            Err("differential equations can't be solved in this set".to_owned())
        );
    }
}
