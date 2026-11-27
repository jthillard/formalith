//! Inputs printed as Typst as they were typed, without evaluating them.
use formalith::parser::syntax::input_typst;

fn typst(input: &str) -> String {
    input_typst(input).unwrap_or_else(|| panic!("`{input}` should parse"))
}

#[test]
fn expressions() {
    for (input, expected) in [
        ("x - y", "x - y"),
        ("x + -y", "x + (-y)"),
        ("(x+1)/(x-1)", "frac(x + 1, x - 1)"),
        ("1/2 x", "frac(1, 2) x"),
        ("2x y", "2 x y"),
        ("2*3", "2 dot 3"),
        ("(x + 1)(x - 1)", "(x + 1) (x - 1)"),
        ("-x^2", "-x^(2)"),
        ("(-x)^2", "(-x)^(2)"),
        ("x^(1/2)", "x^(frac(1, 2))"),
        ("2^3^2", "2^(3^(2))"),
        ("n!^2", "n!^(2)"),
        ("(n+1)!", "(n + 1)!"),
        ("1.5e-20", "1.5 times 10^(-20)"),
        ("abc + x_1 + alpha", "\"abc\" + x_1 + alpha"),
        ("pi + oo + euler_gamma", "pi + oo + gamma"),
        ("f'(2)", "f'(2)"),
        ("myfun(x, y)", "op(\"myfun\")(x, y)"),
        ("sqrt(x) + abs(x) + atan(x)", "sqrt(x) + abs(x) + arctan(x)"),
        ("root(x, 3)", "root(3, x)"),
        ("[[1, 2], [3, 4]]", "mat(1, 2; 3, 4)"),
    ] {
        assert_eq!(typst(input), expected, "{input}");
    }
}

#[test]
fn builtins() {
    for (input, expected) in [
        ("integrate(x^2, x, 0, 1)", "integral_(0)^(1) x^(2) dif x"),
        ("integrate(x + 1, x)", "integral (x + 1) dif x"),
        ("sum(1/k^2, k, 1, oo)", "sum_(k = 1)^(oo) frac(1, k^(2))"),
        ("lim(sin(x)/x, x, 0)", "lim_(x -> 0) (frac(sin(x), x))"),
        ("lim(1/x, x, 0, -1)", "lim_(x -> 0^-) (frac(1, x))"),
        ("diff(x^3, x)", "frac(dif, dif x) x^(3)"),
        ("diff(x^3, x, 2)", "frac(dif^(2), dif x^(2)) x^(3)"),
        (
            "piecewise(x < 0, -x, x)",
            "cases(-x & \"if \" x < 0, x & \"otherwise\")",
        ),
        ("polygamma(1, x)", "psi^((1))(x)"),
        ("lambertw(x, -1)", "W_(-1)(x)"),
        ("assume(a > 0, n integer)", "op(\"assume\")(a > 0, n in ZZ)"),
    ] {
        assert_eq!(typst(input), expected, "{input}");
    }
}

#[test]
fn statements() {
    assert_eq!(typst("f(x) := x^2"), "f(x) := x^(2)");
    assert_eq!(typst("x + y = 3, x - y = 1"), "x + y = 3, quad x - y = 1");
    assert_eq!(typst("x^2 <= 4"), "x^(2) <= 4");
}

#[test]
fn invalid_inputs() {
    for input in [
        "",
        "x +",
        "sin x",
        "(",
        "x 2",
        "[[1, 2], [3]]",
        "f' + 1",
        "2 := x",
        "x ?",
    ] {
        assert_eq!(input_typst(input), None, "{input}");
    }
}
