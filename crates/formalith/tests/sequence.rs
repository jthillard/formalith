//! Sequences: the sets `R^N` and `C^N`, recurrences, terms, shifts and recursive definitions.

use formalith::{
    dynamic::SetChoice,
    field::{Set, real::R},
    parse,
    parser::environment::Environment,
    symbol,
};

use crate::common::numeric::eval_in;

/// Evaluate the lines in `set`, the last one printed plainly.
fn eval(set: &str, lines: &[&str]) -> Result<String, String> {
    let set: SetChoice = set.parse()?;
    let mut env = Environment::new();
    let mut result = Ok(String::new());
    for line in lines {
        result = eval_in(set, &mut env, line);
    }
    result
}

/// The plain result of `expected` in `set`.
fn same(set: &str, expected: &str) -> Result<String, String> {
    eval(set, &[expected])
}

const FIB: [&str; 3] = [
    "fib(0) := 0",
    "fib(1) := 1",
    "fib(n) := fib(n - 1) + fib(n - 2)",
];

/// `lines` after the definition of the Fibonacci numbers.
fn with_fib<'a>(lines: &[&'a str]) -> Vec<&'a str> {
    FIB.iter().copied().chain(lines.iter().copied()).collect()
}

#[test]
fn closed_forms() {
    let r_n = R.get_sequence_set(symbol!("n"));
    assert_eq!(
        parse!("expand((n + 1)^2 - n^2)", r_n),
        parse!("2 n + 1", r_n)
    );
    assert_eq!(
        eval("R^N", &["simplify((n^2 - 1)/(n - 1))"]),
        same("R", "n + 1")
    );
    assert_eq!(eval("R^N", &["n^2 + 1"]), same("R", "n^2 + 1"));
    assert_eq!(eval("R^N", &["sin(n)/n"]), same("R", "sin(n)/n"));
    assert_eq!(eval("R^N", &["a n + 1"]), same("R", "a n + 1"));
    assert_eq!(eval("R^N", &["term(n^2 + 1, 3)"]), Ok("10".to_owned()));
    assert_eq!(eval("R^N", &["shift(n^2, 1)"]), same("R", "(n + 1)^2"));
    assert_eq!(eval("R^N", &["shift(1/n, -2)"]), same("R", "1/(n - 2)"));
    // Builtins are componentwise
    assert_eq!(
        eval("R^N", &["sum(1/k, k, 1, n)"]),
        same("R", "sum(1/k, k, 1, n)")
    );
    assert_eq!(eval("R^N[k]", &["k^2 + n"]), same("R", "k^2 + n"));
}

#[test]
fn recurrences() {
    let u = "recurrence(u(n) = 2 u(n - 1) + 1, u(0) = 1)";
    assert_eq!(
        eval("R^N", &[&format!("term({u}, 10)")]),
        Ok("2047".to_owned())
    );
    assert_eq!(
        eval("R^N", &[u]),
        Ok("recurrence(u(n) = 2*u(n-1)+1, u(0) = 1)".to_owned())
    );
    assert_eq!(eval("R^N", &[&format!("{u} - {u}")]), Ok("0".to_owned()));
    assert_eq!(
        eval("R^N", &[&format!("shift({u}, 1) - 2 {u}")]),
        Ok("1".to_owned())
    );
    assert_eq!(
        eval("R^N", &[&format!("shift({u}, 3) - 8 {u}")]),
        Ok("7".to_owned())
    );
    // Terms before the start aren't defined
    assert_eq!(
        eval("R^N", &[&format!("term({u}, -1)")]),
        same("R^N", &format!("term({u}, -1)"))
    );
    let fib = "recurrence(u(n) = u(n - 1) + u(n - 2), u(0) = 0, u(1) = 1)";
    assert_eq!(
        eval("R^N", &[&format!("term({fib}, 100)")]),
        Ok("354224848179261915075".to_owned())
    );
    // Several sequences, the last one being the result
    assert_eq!(
        eval(
            "R^N",
            &[
                "term(recurrence(u(n) = u(n - 1) + 1, u(0) = 0, v(n) = v(n - 1) + u(n), v(0) = 0), 4)"
            ]
        ),
        Ok("10".to_owned())
    );
    // Values replacing the rule
    assert_eq!(
        eval(
            "R^N",
            &["term(recurrence(u(n) = 2 u(n - 1), u(0) = 1, u(3) = 0), 4)"]
        ),
        Ok("0".to_owned())
    );
}

#[test]
fn printed_recurrences_are_parsed_back() {
    for input in [
        "recurrence(u(n) = n u(n - 1), u(0) = 1)",
        "recurrence(u(n) = u(n - 1) + u(n - 2), u(0) = 0, u(1) = 1)^2 + (-1)^n",
        "shift(recurrence(u(n) = u(n - 1)^2 - 1, u(0) = 2), 2)",
        "shift(recurrence(u(n) = u(n - 1) + n, u(0) = 0), 300)",
        "recurrence(u(n) = 2 u(n - 1), u(0) = 1, u(3) = 0)",
    ] {
        let printed = eval("R^N", &[input]).unwrap();
        assert_eq!(eval("R^N", &[&printed]), Ok(printed.clone()), "{input}");
        for m in [0, 3, 5] {
            assert_eq!(
                eval("R^N", &[&format!("term({printed}, {m})")]),
                eval("R^N", &[&format!("term({input}, {m})")]),
                "{input} at {m}"
            );
        }
    }
}

#[test]
fn invalid_recurrences() {
    assert!(eval("R^N", &["recurrence(u(n) = u(n + 1), u(0) = 1)"]).is_err());
    assert!(eval("R^N", &["recurrence(u(n) = u(n - 2), u(0) = 1)"]).is_err());
    assert!(eval("R^N", &["recurrence(u(n) = u(n/2), u(0) = 1)"]).is_err());
    assert!(eval("R^N", &["recurrence(u(0) = 1)"]).is_err());
    assert!(eval("R^N", &["recurrence(u(n) = 1, u(n) = 2)"]).is_err());
}

#[test]
fn recursive_definitions() {
    let u = ["u(0) := 1", "u(n) := 2 u(n - 1) + 1"];
    let with_u = |line| [u[0], u[1], line];
    assert_eq!(eval("R", &with_u("u(10)")), Ok("2047".to_owned()));
    assert_eq!(eval("R", &with_u("u(x)")), same("R", "u(x)"));
    assert_eq!(eval("R", &u), Ok(":= 2*u(n-1)+1".to_owned()));
    assert_eq!(eval("R", &u[..1]), Ok(":= 1".to_owned()));
    assert_eq!(eval("R^N", &with_u("u(10)")), Ok("2047".to_owned()));
    assert_eq!(
        eval("R^N", &with_u("u(n + 1) - 2 u(n)")),
        Ok("1".to_owned())
    );
    assert_eq!(
        eval("R^N", &with_u("u")),
        Ok("recurrence(u(n) = 2*u(n-1)+1, u(0) = 1)".to_owned())
    );
    assert_eq!(
        eval("R^N", &u),
        Ok(":= recurrence(u(n) = 2*u(n-1)+1, u(0) = 1)".to_owned())
    );
    // A subsequence stays unevaluated
    assert_eq!(eval("R^N", &with_u("u(2 n)")), same("R", "u(2 n)"));
    // The values can be given after the rule
    assert_eq!(
        eval("R", &["v(n) := v(n - 1) + 1", "v(0) := 0", "v(7)"]),
        Ok("7".to_owned())
    );
    // A value can be replaced
    assert_eq!(
        eval(
            "R",
            &["w(0) := 1", "w(n) := 3 w(n - 1)", "w(0) := 2", "w(2)"]
        ),
        Ok("18".to_owned())
    );
    // Nonlinear and with the index
    assert_eq!(
        eval("R", &["a(0) := 2", "a(n) := a(n - 1)^2 - 1", "a(4)"]),
        Ok("3968".to_owned())
    );
    assert_eq!(
        eval("R", &["f(0) := 1", "f(n) := n f(n - 1)", "f(20)"]),
        Ok("2432902008176640000".to_owned())
    );
    // Other names of the parameter, and the index of `R^N[k]`
    assert_eq!(
        eval("R^N[k]", &["a(0) := 2", "a(k) := a(k - 1)^2 - 1", "a(4)"]),
        Ok("3968".to_owned())
    );
    assert_eq!(
        eval("R^N", &["a(0) := 2", "a(k) := a(k - 1) + k", "a(4)"]),
        Ok("12".to_owned())
    );
}

#[test]
fn fibonacci() {
    assert_eq!(
        eval("R", &with_fib(&["fib(100)"])),
        Ok("354224848179261915075".to_owned())
    );
    assert_eq!(eval("Z", &with_fib(&["fib(30)"])), Ok("832040".to_owned()));
    assert_eq!(
        eval("R^N", &with_fib(&["fib(n + 2) - fib(n + 1) - fib(n)"])),
        Ok("0".to_owned())
    );
    assert_eq!(
        eval(
            "R^N",
            &with_fib(&["fib(n + 100) - fib(n + 99) - fib(n + 98)"])
        ),
        Ok("0".to_owned())
    );
    assert_eq!(
        eval("R^N", &with_fib(&["v(n) := fib(n)^2 + (-1)^n", "v(10)"])),
        Ok("3026".to_owned())
    );
    // Linear time
    let fib_5000 = eval("R", &with_fib(&["fib(5000)"])).unwrap();
    assert_eq!(fib_5000.len(), 1045);
    assert!(fib_5000.starts_with("38789684543883256337"));
}

#[test]
fn values_of_functions() {
    let f = ["f(0) := 1", "f(x) := sin(x)/x"];
    assert_eq!(eval("R", &[f[0], f[1], "f(0)"]), Ok("1".to_owned()));
    assert_eq!(eval("R", &[f[0], f[1], "f(pi)"]), Ok("0".to_owned()));
    assert_eq!(
        eval("R", &[f[0], f[1], "f(x)"]),
        same("R", "piecewise(x = 0, 1, sin(x)/x)")
    );
}

const MANDELBROT: [&str; 2] = ["f(c, 0) := c", "f(c, n) := f(c, n - 1)^2 + c"];

/// `lines` after the definition of the Mandelbrot iteration `f(c, n)`.
fn with_mandelbrot<'a>(lines: &[&'a str]) -> Vec<&'a str> {
    MANDELBROT
        .iter()
        .copied()
        .chain(lines.iter().copied())
        .collect()
}

#[test]
fn sequences_with_parameters() {
    assert_eq!(
        eval("R", &with_mandelbrot(&["f(1/2, 2)"])),
        Ok("17/16".to_owned())
    );
    // In the other order, and with other names in the value
    assert_eq!(
        eval(
            "R",
            &["f(c, n) := f(c, n - 1)^2 + c", "f(a, 0) := a", "f(1/2, 3)"]
        ),
        Ok("417/256".to_owned())
    );
    assert_eq!(
        eval("R", &with_mandelbrot(&["f(x, 2)"])),
        same("R", "(x^2 + x)^2 + x")
    );
    assert_eq!(
        eval("R", &with_mandelbrot(&["f(f(1/2, 1), 1)"])),
        Ok("21/16".to_owned())
    );
    assert_eq!(
        eval("R", &with_mandelbrot(&["f(a, n)"])),
        same("R", "f(a, n)")
    );
    assert_eq!(
        eval("Z", &with_mandelbrot(&["f(-2, 10)"])),
        Ok("2".to_owned())
    );
    // The index first
    assert_eq!(
        eval(
            "R",
            &["g(0, x) := x", "g(n, x) := 2 g(n - 1, x)", "g(3, 5)"]
        ),
        Ok("40".to_owned())
    );
    // The whole sequence keeps its parameter
    assert_eq!(
        eval("R^N", &with_mandelbrot(&["f"])),
        Ok("recurrence(u(n) = c+u(n-1)^2, u(0) = c)".to_owned())
    );
    assert_eq!(
        eval("R^N", &with_mandelbrot(&["f(1, n + 1) - f(1, n)^2"])),
        Ok("1".to_owned())
    );
    assert_eq!(
        eval("R^N", &with_mandelbrot(&["f(-1, 3)"])),
        Ok("0".to_owned())
    );
}

#[test]
fn errors_of_sequences_with_parameters() {
    assert_eq!(
        eval(
            "R",
            &["g(c, 0) := 1", "g(c, n) := g(2 c, n - 1)", "g(1, 3)"]
        ),
        Err(
            "the rule of `g` can only refer to `g(c, n - d)` with d >= 1, found `g(2 c, n - 1)`"
                .to_owned()
        )
    );
    assert_eq!(
        eval("R", &with_mandelbrot(&["f(1)"])),
        Err("`f` expects 2 arguments, found 1".to_owned())
    );
    // Two integers aren't a value of the definition
    assert!(eval("R", &with_mandelbrot(&["f(0, 0) := 1"])).is_err());
}

#[test]
fn printed_definitions_with_parameters() {
    let mut env = Environment::new();
    for line in MANDELBROT {
        env.eval(line, R).unwrap();
    }
    let printed: Vec<String> = env.definitions().map(ToString::to_string).collect();
    assert_eq!(printed, ["f(c, 0) := c\nf(c, n) := f(c, n - 1)^2 + c"]);
    assert_eq!(eval("R", &["f(c, 0) := c"]), Ok(":= c".to_owned()));
}

#[test]
fn complex_sequences() {
    assert_eq!(
        eval("C^N", &["u(0) := 1", "u(n) := i u(n - 1)", "u(5)"]),
        Ok("i".to_owned())
    );
    assert_eq!(
        eval(
            "C^N",
            &["u(0) := 1", "u(n) := i u(n - 1)", "u(n + 2) + u(n)"]
        ),
        Ok("0".to_owned())
    );
    assert_eq!(eval("C^N", &["term(i^n, 3)"]), Ok("-i".to_owned()));
    assert_eq!(
        eval("C", &["u(0) := 1", "u(n) := (1 + i) u(n - 1)", "u(4)"]),
        Ok("-4".to_owned())
    );
}

#[test]
fn errors() {
    assert!(eval("R^N", &["u(0) := 1", "u(n) := u(n + 1)"]).is_err());
    assert!(eval("R^N", &["u(0) := 1", "u(n) := u(n - 2)", "u(5)"]).is_err());
    // Without its initial values, a definition is accepted, its terms stay unevaluated
    assert_eq!(
        eval("R", &["u(n) := u(n - 2)", "u(0) := 1"]),
        Ok(":= 1".to_owned())
    );
    assert_eq!(
        eval("R", &["u(n) := u(n - 2)", "u(0) := 1", "u(4)"]),
        same("R", "u(4)")
    );
}

/// Terms computed in floats are those computed exactly.
#[test]
fn numeric_terms() {
    use formalith::field::sequence::numeric::NumericSequence;
    let set = R.get_sequence_set(symbol!("n"));
    for input in [
        "recurrence(u(n) = u(n - 1) + u(n - 2), u(0) = 0, u(1) = 1)",
        "recurrence(u(n) = 2 u(n - 1) + 1, u(0) = 1)",
        "recurrence(u(n) = 2 u(n - 1), u(0) = 1, u(3) = 0) + n^2",
        "recurrence(u(n) = n u(n - 1), u(1) = 1) * recurrence(u(n) = u(n - 1) + n, u(-2) = 3)",
        "shift(recurrence(u(n) = u(n - 1) + u(n - 2), u(0) = 0, u(1) = 1), 3) - 2^n",
        "(n + 1)^2/(n - 2)",
    ] {
        let u = parse!(input, set);
        let numeric = NumericSequence::of_term(&u, symbol!("n"), &[]).unwrap();
        let terms = numeric.terms(&[], -3, 12);
        let exact: Vec<(i64, f64)> = (-3..=12)
            .filter_map(|m| {
                let value = eval("R^N", &[&format!("term({input}, {m})")]).ok()?;
                let value = eval("R", &[&format!("approx({value})")]).ok()?;
                Some((m, value.parse().ok()?))
            })
            .collect();
        assert_eq!(terms.len(), exact.len(), "{input}: {terms:?} {exact:?}");
        for ((k, a), (m, b)) in terms.iter().zip(&exact) {
            assert!(
                k == m && (a - b).abs() <= 1e-9 * b.abs().max(1.),
                "{input}: {terms:?} {exact:?}"
            );
        }
    }
    // With a parameter
    let u = parse!("recurrence(u(n) = a u(n - 1), u(0) = 1)", set);
    let numeric = NumericSequence::of_term(&u, symbol!("n"), &[symbol!("a")]).unwrap();
    assert_eq!(numeric.terms(&[3.], 0, 2), [(0, 1.), (1, 3.), (2, 9.)]);
}
