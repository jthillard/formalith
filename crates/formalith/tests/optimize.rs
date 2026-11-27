//! Global extrema with `argmin` and `argmax`.

/// Evaluate `statements` in `R`, printed as Typst so that the output doesn't depend on colors.
fn eval(statements: &[&str]) -> Result<String, String> {
    crate::common::eval_statements("R".parse().unwrap(), statements, true)
}

fn argmin(statement: &str) -> Result<String, String> {
    eval(&[statement])
}

/// The solutions of `equations`, printed like those of `argmin`, so that terms are ordered like in the result.
fn solved(equations: &str) -> Result<String, String> {
    eval(&[&format!("solve({equations})")])
}

/// The result when the extremum isn't reached.
fn none() -> Result<String, String> {
    Ok("\"no solution\"".to_owned())
}

#[test]
fn polynomials() {
    assert_eq!(argmin("argmin(x^2 - 2*x, x)"), solved("x = 1, x"));
    assert_eq!(argmin("argmin(x^4 - 2*x^2, x)"), solved("x^2 = 1, x"));
    assert_eq!(argmin("argmax(x - x^2, x)"), solved("x = 1/2, x"));
    // Every symbol of the function by default
    assert_eq!(argmin("argmin(x^2 - 2*x)"), solved("x = 1, x"));
    assert_eq!(argmin("argmin(x^3, x)"), none());
    assert_eq!(argmin("argmin(x, x)"), none());
    assert_eq!(argmin("argmax(x^2, x)"), none());
}

#[test]
fn intervals() {
    assert_eq!(argmin("argmin(x^3 - 3*x, x, -3, 3)"), solved("x = -3, x"));
    assert_eq!(argmin("argmax(x^3 - 3*x, x, -3, 3)"), solved("x = 3, x"));
    assert_eq!(
        argmin("argmin(x^3 - 3*x, x, -2, 3)"),
        solved("x^2 + x - 2 = 0, x")
    );
    assert_eq!(argmin("argmin(x^2, x, 1, oo)"), solved("x = 1, x"));
    assert_eq!(argmin("argmax(sin(x), x, 0, 4)"), solved("x = pi/2, x"));
    assert_eq!(argmin("argmin(1/x, x, 1, 2)"), solved("x = 2, x"));
    assert!(
        argmin("argmin(x^2, x, 2, 1)")
            .unwrap_err()
            .contains("lower bound must be below")
    );
}

#[test]
fn transcendental() {
    assert_eq!(argmin("argmax(x*exp(-x), x)"), solved("x = 1, x"));
    assert_eq!(argmin("argmin(x*ln(x), x)"), solved("x = exp(-1), x"));
    assert_eq!(argmin("argmin(exp(x), x)"), none());
    assert_eq!(argmin("argmin(x - 2*sin(x), x)"), none());
    // Periodic minimizers
    assert_eq!(argmin("argmin(cos(x), x)"), solved("cos(x) = -1, x"));
    assert_eq!(argmin("argmax(sin(x), x)"), solved("sin(x) = 1, x"));
}

#[test]
fn domains_and_singularities() {
    assert_eq!(argmin("argmin(sqrt(x), x)"), solved("x = 0, x"));
    assert_eq!(argmin("argmin(x^2 + 1/x^2, x)"), solved("x^2 = 1, x"));
    assert_eq!(argmin("argmin(1/x, x)"), none());
    assert_eq!(argmin("argmin(1/(x^2 - 1), x)"), none());
    // The domain of the function as typed, which normalization drops: `x^3/x` is `x^2` but undefined at 0
    assert_eq!(argmin("argmin(x^3/x, x)"), none());
    assert_eq!(argmin("argmin(x^2 + 1/x - 1/x, x)"), none());
    assert_eq!(argmin("argmin(sqrt(x)^2 + 1, x)"), solved("x = 0, x"));
    assert_eq!(argmin("argmin(exp(ln(x))^2, x)"), none());
    assert_eq!(eval(&["f(x) := x^3/x", "argmin(f(x), x)"]), none());
    assert_eq!(argmin("argmin((x^2 + y^2) x/x, x, y)"), none());
}

#[test]
fn absolute_values() {
    assert_eq!(argmin("argmin(abs(x - 2), x)"), solved("x = 2, x"));
    assert_eq!(argmin("argmin(abs(x^2 - 1) + x, x)"), solved("x = -1, x"));
    assert_eq!(argmin("argmax(abs(x) - x^2, x)"), solved("x^2 = 1/4, x"));
    assert_eq!(
        argmin("argmax(abs(x - 1) + abs(x + 1), x, -2, 3)"),
        solved("x = 3, x")
    );
    // Constant on `{$[-1, 1]$}`
    assert!(argmin("argmin(abs(x - 1) + abs(x + 1), x)").is_err());
}

#[test]
fn parameters() {
    assert_eq!(
        eval(&["assume(a > 0)", "argmin(a*x^2 + b*x, x)"]),
        eval(&["solve(2*a*x + b = 0, x)"])
    );
    assert_eq!(eval(&["assume(a < 0)", "argmin(a*x^2 + b*x, x)"]), none());
    // The sign of `a` is unknown
    assert!(argmin("argmin(a*x^2 + b*x, x)").is_err());
}

#[test]
fn several_variables() {
    assert_eq!(
        argmin("argmin(x^2 + y^2 - 2*x, x, y)"),
        solved("x = 1, y = 0, x, y")
    );
    assert_eq!(
        argmin("argmax(-x^2 - (y - 1)^2, x, y)"),
        solved("x = 0, y = 1, x, y")
    );
    // A line of minimizers
    assert_eq!(argmin("argmin((x - y)^2, x, y)"), solved("x = y, x, y"));
    // A local minimum only
    assert_eq!(argmin("argmin(x^3 - 3*x + y^2, x, y)"), none());
    assert_eq!(argmin("argmin(x*y, x, y)"), none());
    assert!(argmin("argmin(exp(x + y), x, y)").is_err());
    assert!(argmin("argmin(x^2 + a*y^2, x, y)").is_err());
}

#[test]
fn errors() {
    assert!(argmin("argmin(x = 1, x)").is_err());
    assert!(argmin("argmin(x^2, 2)").is_err());
    assert!(argmin("argmin(x^2, x, x)").is_err());
    assert!(argmin("argmin(x^2, pi)").is_err());
    assert!(argmin("argmin(5)").is_err());
    assert!(argmin("argmin(floor(x), x)").is_err());
}

mod local {
    use super::{argmin, eval, none, solved};

    #[test]
    fn polynomials() {
        assert_eq!(argmin("localmin(x^3 - 3*x, x)"), solved("x = 1, x"));
        assert_eq!(argmin("localmax(x^3 - 3*x, x)"), solved("x = -1, x"));
        // An inflection point
        assert_eq!(argmin("localmin(x^3, x)"), none());
        // A degenerate minimum
        assert_eq!(argmin("localmin(x^4, x)"), solved("x = 0, x"));
        assert_eq!(argmin("localmax(x^4 - 2*x^2, x)"), solved("x = 0, x"));
        assert_eq!(argmin("localmin(x^4 - 2*x^2, x)"), solved("x^2 = 1, x"));
    }

    #[test]
    fn intervals() {
        // Bounds are local extrema relative to the interval
        assert_eq!(
            argmin("localmin(x^3 - 3*x, x, -3, 3)"),
            solved("(x + 3)*(x - 1) = 0, x")
        );
        assert_eq!(
            argmin("localmax(x^3 - 3*x, x, -3, 3)"),
            solved("(x - 3)*(x + 1) = 0, x")
        );
        assert_eq!(argmin("localmin(x, x, 0, 1)"), solved("x = 0, x"));
    }

    #[test]
    fn special_points() {
        assert_eq!(argmin("localmin(abs(x), x)"), solved("x = 0, x"));
        assert_eq!(argmin("localmin(sqrt(x), x)"), solved("x = 0, x"));
        assert_eq!(argmin("localmin(x^2 + 1/x^2, x)"), solved("x^2 = 1, x"));
        // `f` is lower on the left of the jump at 0
        assert_eq!(argmin("localmin(sign(x) + x^2, x)"), none());
        assert_eq!(argmin("localmax(sign(x) - x^2, x)"), none());
        // Constant on `{$[-1, 1]$}`
        assert!(argmin("localmin(abs(x - 1) + abs(x + 1), x)").is_err());
    }

    #[test]
    fn transcendental() {
        assert_eq!(argmin("localmax(x*exp(-x), x)"), solved("x = 1, x"));
        assert_eq!(argmin("localmin(x*exp(-x), x)"), none());
        assert_eq!(argmin("localmin(cos(x), x)"), solved("cos(x) = -1, x"));
        assert_eq!(argmin("localmax(cos(x), x)"), solved("cos(x) = 1, x"));
        // No global minimum, but local ones
        assert_eq!(argmin("argmin(x + 2*sin(x), x)"), none());
        assert!(
            argmin("localmin(x + 2*sin(x), x)")
                .unwrap()
                .contains("frac(2, 3) pi")
        );
    }

    #[test]
    fn parameters() {
        assert_eq!(
            eval(&["assume(a < 0)", "localmax(a*x^2 + b*x, x)"]),
            eval(&["solve(2*a*x + b = 0, x)"])
        );
        assert!(argmin("localmin(a*x^2 + b*x, x)").is_err());
    }

    #[test]
    fn several_variables() {
        // A minimum at `{$(1, 0)$}` and a saddle at `{$(-1, 0)$}`
        assert_eq!(
            argmin("localmin(x^3 - 3*x + y^2, x, y)"),
            solved("x = 1, y = 0, x, y")
        );
        assert_eq!(argmin("localmax(x^3 - 3*x + y^2, x, y)"), none());
        assert_eq!(argmin("localmin(x^2 - y^2, x, y)"), none());
        assert_eq!(
            argmin("localmax(-x^2 - y^2 + 2*y, x, y)"),
            solved("x = 0, y = 1, x, y")
        );
        // Not rational, by the Hessian matrix
        assert_eq!(
            argmin("localmin(exp(x^2 + y^2), x, y)"),
            solved("x = 0, y = 0, x, y")
        );
        // Degenerate, global minima
        assert_eq!(argmin("localmin((x - y)^2, x, y)"), solved("x = y, x, y"));
        assert_eq!(
            argmin("localmin(x^4 + y^2, x, y)"),
            solved("x = 0, y = 0, x, y")
        );
        // Degenerate, neither a global minimum nor a global maximum
        assert!(argmin("localmin(x^3 + y^2, x, y)").is_err());
    }
}

mod both {
    use super::argmin;

    fn ok(result: &str) -> Result<String, String> {
        Ok(result.to_owned())
    }

    #[test]
    fn global() {
        assert_eq!(
            argmin("extrema(x^2 - 2*x, x, 0, 3)"),
            ok("\"min:\" x = 1, quad f = -1 \\ \"max:\" x = 3, quad f = 3")
        );
        assert_eq!(
            argmin("extrema(x/(x^2 + 1), x)"),
            ok("\"min:\" x = -1, quad f = -frac(1, 2) \\ \"max:\" x = 1, quad f = frac(1, 2)")
        );
        // Only a minimum
        assert_eq!(
            argmin("extrema(x^2 - 2*x)"),
            ok("\"min:\" x = 1, quad f = -1")
        );
        assert_eq!(argmin("extrema(x^3, x)"), ok("\"no extremum\""));
        // Undefined at 0
        assert_eq!(argmin("extrema(x^3/x)"), ok("\"no extremum\""));
        assert_eq!(
            argmin("extrema(x^3/x, x, -1, 1)"),
            ok("\"max:\" x = -1, quad f = 1 \\ \"max:\" x = 1, quad f = 1")
        );
        // Reached everywhere
        assert_eq!(
            argmin("extrema(5, x)"),
            ok("\"min:\" f = 5 \\ \"max:\" f = 5")
        );
    }

    #[test]
    fn local() {
        assert_eq!(
            argmin("localextrema(x^3 - 3*x, x)"),
            ok("\"min:\" x = 1, quad f = -2 \\ \"max:\" x = -1, quad f = 2")
        );
        let periodic = argmin("localextrema(cos(x), x)").unwrap();
        assert!(periodic.starts_with("\"min:\" x = "), "{periodic}");
        assert!(periodic.contains("quad f = -1 \\ \"max:\""), "{periodic}");
        assert!(periodic.ends_with("quad f = 1 \\ k in ZZ"), "{periodic}");
        assert_eq!(
            argmin("localextrema(x^3 - 3*x + y^2, x, y)"),
            ok("\"min:\" x = 1, y = 0, quad f = -2")
        );
        assert_eq!(
            argmin("localextrema((x - y)^2, x, y)"),
            ok("\"min:\" x = y, quad f = 0")
        );
        assert_eq!(argmin("localextrema(x^3/x)"), ok("\"no extremum\""));
        assert_eq!(
            argmin("localextrema((x^2 + y^2) x/x, x, y)"),
            ok("\"no extremum\"")
        );
        // Either kind failing is an error
        assert!(argmin("localextrema(x^3 + y^2, x, y)").is_err());
    }
}
