//! Set selection and evaluation of the command line interface.
use formalith::repl::{Coefficients, SetChoice};

fn parse(name: &str) -> Result<SetChoice, String> {
    name.parse()
}

#[test]
fn set_names() {
    for name in [
        "N", "Z", "R", "C", "M", "Z/7", "R[x]", "C[t]", "Z/2[x]", "Z/7[y_1]",
    ] {
        assert_eq!(parse(name).map(SetChoice::name), Ok(name.to_owned()));
    }
    assert_eq!(parse("r"), Ok(SetChoice::R));
    assert_eq!(parse("z/7z"), Ok(SetChoice::Zn(7)));
    assert_eq!(parse(" Z / 7 "), Ok(SetChoice::Zn(7)));
    assert!(matches!(
        parse("Z/5[x]"),
        Ok(SetChoice::Poly(Coefficients::Zn(5), _))
    ));
}

#[test]
fn invalid_set_names() {
    for name in [
        "Q", "Z/1", "Z/0", "Z/x", "Z/-3", "Q[x]", "Z[x]", "M[x]", "R[2x]", "R[]", "C[i]", "R[abs]",
        "R[x",
    ] {
        assert!(parse(name).is_err(), "{name}");
    }
}

#[test]
fn eval() {
    let eval = |input, set: &str| parse(set).unwrap().eval(input, false);
    assert_eq!(eval("3*5", "Z/7"), Ok("1".to_owned()));
    assert_eq!(
        eval("factor(x^4-1)", "Z/5"),
        eval("(x+1)*(x+2)*(x+3)*(x+4)", "Z/5")
    );
    assert_eq!(eval("gcd(x^2-1, x-1)", "R[x]"), eval("x-1", "R[x]"));
    assert_eq!(eval("(t+1)^2", "Z/2[t]"), eval("t^2+1", "Z/2[t]"));
    assert_eq!(eval("x+1", "Z/2[x]"), Ok("x + 1".to_owned()));
    assert_eq!(eval("quo(17, 5)", "Z"), Ok("3".to_owned()));
    assert_eq!(eval("rem(-17, 5)", "Z"), Ok("3".to_owned()));
    assert_eq!(eval("quo(-17, 5)", "Z"), Ok("-4".to_owned()));
}
