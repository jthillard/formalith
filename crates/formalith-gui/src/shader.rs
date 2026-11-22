//! WGSL code of the graphs: [`Numeric`] expressions compiled to WGSL functions, inside the shaders drawing them
//! ([`render`]) and searching their remarkable points ([`analysis`]).
//!
//! WGSL has no recursion, so the expression tree is flattened into a sequence of `let`s. Values are `f32`, undefined
//! ones NaN, like with [`Numeric::eval`].

use std::fmt::Write as _;

use formalith_session::{
    formalith::field::real::numeric::{NumFn, Numeric},
    graph::{Comparison, Graph},
};

/// The functions used by emitted expressions.
pub const PRELUDE: &str = include_str!("shader/prelude.wgsl");
/// The template of [`render`].
pub const RENDER: &str = include_str!("shader/render.wgsl");
/// The template of [`analysis`].
pub const ANALYSIS: &str = include_str!("shader/analysis.wgsl");

/// The largest number of parameters of a drawn graph, the size of the parameter array of [`RENDER`].
pub const MAX_PARAMS: usize = 64;

/// Writes the statements of an expression.
struct Emitter<'a> {
    out: &'a mut String,
    next: usize,
    param_offset: usize,
}

impl Emitter<'_> {
    /// Bind `value` to a new variable, returning its name.
    fn bind(&mut self, value: &str) -> String {
        let name = format!("v{}", self.next);
        self.next += 1;
        let _ = writeln!(self.out, "    let {name} = {value};");
        name
    }

    /// Write the statements computing `expr`, returning the WGSL expression of its value.
    fn emit(&mut self, expr: &Numeric) -> String {
        match expr {
            Numeric::Const(value) => literal(*value),
            Numeric::Var(Graph::X) => "x".to_owned(),
            Numeric::Var(Graph::Y) => "y".to_owned(),
            Numeric::Var(i) => format!("param({}u)", self.param_offset + i - 2),
            Numeric::Add(terms) => self.fold(terms, " + ", "0.0"),
            Numeric::Mul(factors) => self.fold(factors, " * ", "1.0"),
            Numeric::Pow(base, exponent) => {
                let base = self.emit(base);
                let exponent = self.emit(exponent);
                self.bind(&format!("nf_pow({base}, {exponent})"))
            }
            Numeric::RationalPow(base, num, den) => {
                let base = self.emit(base);
                match (i32::try_from(*num), i32::try_from(*den)) {
                    (Ok(num), Ok(den)) => self.bind(&format!("nf_rpow({base}, {num}, {den})")),
                    _ => {
                        let exponent = literal(*num as f64 / *den as f64);
                        self.bind(&format!("nf_pow({base}, {exponent})"))
                    }
                }
            }
            Numeric::Fun(fun, args) => {
                let args: Vec<String> = args.iter().map(|arg| self.emit(arg)).collect();
                self.function(*fun, &args)
            }
            Numeric::Unsupported(_) => "nf_nan()".to_owned(),
        }
    }

    /// The sum or product of `terms`, `empty` without terms.
    fn fold(&mut self, terms: &[Numeric], operator: &str, empty: &str) -> String {
        if terms.is_empty() {
            return empty.to_owned();
        }
        let terms: Vec<String> = terms.iter().map(|term| self.emit(term)).collect();
        self.bind(&terms.join(operator))
    }

    /// The application of `fun` to the values `args`.
    fn function(&mut self, fun: NumFn, args: &[String]) -> String {
        let arg = |i: usize| args.get(i).map_or("nf_nan()", String::as_str);
        let name = match fun {
            NumFn::Min | NumFn::Max => {
                let name = if fun == NumFn::Min {
                    "nf_min"
                } else {
                    "nf_max"
                };
                let mut value = if fun == NumFn::Min {
                    "nf_inf()".to_owned()
                } else {
                    "-nf_inf()".to_owned()
                };
                for arg in args {
                    value = self.bind(&format!("{name}({value}, {arg})"));
                }
                return value;
            }
            NumFn::Piecewise => {
                let mut value = if args.len() % 2 == 1 {
                    args[args.len() - 1].clone()
                } else {
                    "nf_nan()".to_owned()
                };
                for pair in args.chunks_exact(2).rev() {
                    value = self.bind(&format!("nf_branch({}, {}, {value})", pair[0], pair[1]));
                }
                return value;
            }
            NumFn::Polygamma | NumFn::Binomial => {
                let name = if fun == NumFn::Polygamma {
                    "nf_polygamma"
                } else {
                    "nf_binomial"
                };
                return self.bind(&format!("{name}({}, {})", arg(0), arg(1)));
            }
            NumFn::Lt | NumFn::Le | NumFn::Gt | NumFn::Ge | NumFn::Eq | NumFn::Ne => {
                let name = match fun {
                    NumFn::Lt => "nf_lt",
                    NumFn::Le => "nf_le",
                    NumFn::Gt => "nf_gt",
                    NumFn::Ge => "nf_ge",
                    NumFn::Eq => "nf_eq",
                    _ => "nf_ne",
                };
                return self.bind(&format!("{name}({}, {})", arg(0), arg(1)));
            }
            NumFn::Exp => "nf_exp",
            NumFn::Ln => "nf_ln",
            NumFn::Sin => "nf_sin",
            NumFn::Cos => "nf_cos",
            NumFn::Tan => "nf_tan",
            NumFn::Asin => "nf_asin",
            NumFn::Acos => "nf_acos",
            NumFn::Atan => "nf_atan",
            NumFn::Sinh => "nf_sinh",
            NumFn::Cosh => "nf_cosh",
            NumFn::Tanh => "nf_tanh",
            NumFn::Asinh => "nf_asinh",
            NumFn::Acosh => "nf_acosh",
            NumFn::Atanh => "nf_atanh",
            NumFn::Abs => "nf_abs",
            NumFn::Sign => "nf_sign",
            NumFn::Floor => "nf_floor",
            NumFn::Ceil => "nf_ceil",
            NumFn::Erf => "nf_erf",
            NumFn::Erfi => "nf_erfi",
            NumFn::Gamma => "nf_gamma",
            NumFn::Zeta => "nf_zeta",
            NumFn::Factorial => "nf_factorial",
            NumFn::LambertW => "nf_lambertw",
            NumFn::Si => "nf_si",
            NumFn::Ci => "nf_ci",
            NumFn::Ei => "nf_ei",
        };
        self.bind(&format!("{name}({})", arg(0)))
    }
}

/// A WGSL `f32` literal of `value`, rounded to `f32`.
fn literal(value: f64) -> String {
    #[allow(clippy::cast_possible_truncation)]
    let value = value as f32;
    if value.is_nan() {
        "nf_nan()".to_owned()
    } else if value.is_infinite() {
        if value > 0. {
            "nf_inf()"
        } else {
            "(-nf_inf())"
        }
        .to_owned()
    } else if value.abs() < f32::MIN_POSITIVE {
        "0.0".to_owned()
    } else if value < 0. {
        format!("(-{:e}f)", -value)
    } else {
        format!("{value:e}f")
    }
}

/// A WGSL function `fn name(x: f32, y: f32) -> f32` computing `expr`, whose parameter `i` (the variable `i + 2`) is
/// `param(param_offset + i)`.
#[must_use]
pub fn function(expr: &Numeric, name: &str, param_offset: usize) -> String {
    let mut out = format!("fn {name}(x: f32, y: f32) -> f32 {{\n");
    let mut emitter = Emitter {
        out: &mut out,
        next: 0,
        param_offset,
    };
    let value = emitter.emit(expr);
    let _ = writeln!(out, "    return {value};\n}}");
    out
}

/// The number of a comparison in [`RENDER`].
#[must_use]
pub const fn relation_code(relation: Comparison) -> f32 {
    match relation {
        Comparison::Equal => 0.,
        Comparison::Less => 1.,
        Comparison::LessEqual => 2.,
        Comparison::Greater => 3.,
        Comparison::GreaterEqual => 4.,
    }
}

/// The shader drawing the graph of the relations `F_i(x, y) op 0` (a single one, compared with `=`, for curves),
/// see [`RENDER`]: `F_i` are `F_at(i, x, y)`, their comparisons `relation_of(i)`, and `F` is `F_0`.
#[must_use]
pub fn render(relations: &[(&Numeric, Comparison)]) -> String {
    let mut out = format!("{PRELUDE}\n{RENDER}\n");
    for (i, (expr, _)) in relations.iter().enumerate() {
        out.push_str(&function(expr, &format!("F_{i}"), 0));
    }
    let _ = writeln!(out, "const COUNT: u32 = {}u;", relations.len());
    out.push_str("fn F(x: f32, y: f32) -> f32 {\n    return F_0(x, y);\n}\n");
    out.push_str("fn F_at(i: u32, x: f32, y: f32) -> f32 {\n    switch i {\n");
    for i in 0..relations.len() {
        let _ = writeln!(out, "        case {i}u: {{ return F_{i}(x, y); }}");
    }
    out.push_str("        default: { return nf_nan(); }\n    }\n}\n");
    out.push_str("fn relation_of(i: u32) -> f32 {\n    switch i {\n");
    for (i, (_, relation)) in relations.iter().enumerate() {
        let _ = writeln!(
            out,
            "        case {i}u: {{ return {}; }}",
            literal(f64::from(relation_code(*relation)))
        );
    }
    out.push_str("        default: { return 0.0; }\n    }\n}\n");
    out
}

/// The curves of a search of remarkable points.
pub struct AnalysisCurves<'a> {
    /// The curve `y = f(x)` whose points are searched, with its parameters.
    pub f: (&'a Numeric, usize),
    /// `f'`, else computed by finite differences.
    pub derivative: Option<&'a Numeric>,
    /// The other curves, intersected with `f`, with their numbers of parameters.
    pub others: Vec<(&'a Numeric, usize)>,
}

impl AnalysisCurves<'_> {
    /// The number of targets of the search: `f`, `f'`, then `f - g` for each other curve `g`.
    #[must_use]
    pub fn modes(&self) -> usize {
        2 + self.others.len()
    }
}

/// The shader searching the remarkable points of `curves`, see [`ANALYSIS`]. Parameters of `f`, then of each other
/// curve, follow each other in its parameter array.
#[must_use]
pub fn analysis(curves: &AnalysisCurves<'_>) -> String {
    let (f, f_params) = curves.f;
    let mut out = format!("{PRELUDE}\n{ANALYSIS}\n{}", function(f, "f_0", 0));
    out.push_str("fn f(x: f32) -> f32 {\n    return f_0(x, nf_nan());\n}\n");
    if let Some(derivative) = curves.derivative {
        out.push_str(&function(derivative, "d_0", 0));
    }
    let mut offset = f_params;
    for (k, (g, params)) in curves.others.iter().enumerate() {
        out.push_str(&function(g, &format!("g_{k}"), offset));
        offset += params;
    }
    out.push_str("fn objective(mode: u32, x: f32) -> f32 {\n    switch mode {\n");
    out.push_str("        case 0u: { return f(x); }\n");
    if curves.derivative.is_some() {
        out.push_str("        case 1u: { return d_0(x, nf_nan()); }\n");
    } else {
        out.push_str(
            "        case 1u: { return (f(x + cfg.h) - f(x - cfg.h)) / (2.0 * cfg.h); }\n",
        );
    }
    for k in 0..curves.others.len() {
        let _ = writeln!(
            out,
            "        case {}u: {{ return f(x) - g_{k}(x, nf_nan()); }}",
            k + 2
        );
    }
    out.push_str("        default: { return nf_nan(); }\n    }\n}\n");
    out
}

#[cfg(test)]
pub(crate) mod tests {
    use formalith_session::formalith::{field::real::R, parse, symbol};

    use super::*;

    /// Compile `input` with the variables `x`, `y`, `a`, `b`.
    pub fn compile(input: &str) -> Numeric {
        Numeric::compile(
            &parse!(input, R),
            &[symbol!("x"), symbol!("y"), symbol!("a"), symbol!("b")],
        )
    }

    /// Expressions using every kind of node and function.
    pub const EXPRESSIONS: [&str; 15] = [
        "x^2 + 3*x*y - 1/2",
        "sqrt(x) + x^(1/3) + x^(-2/5) + x^y + 2^x + x^123456789012",
        "exp(x) + ln(x) + sin(x) + cos(x) + tan(x)",
        "asin(x) + acos(x) + atan(x) + sinh(x) + cosh(x) + tanh(x)",
        "asinh(x) + acosh(x) + atanh(x) + abs(x) + sign(x) + floor(x) + ceil(x)",
        "min(x, y, a) + max(x, b)",
        "erf(x) + erfi(x) + gamma(x) + factorial(x) + lambertw(x)",
        "polygamma(2, x) + zeta(x) + binomial(x, 3)",
        "Si(x) + Ci(x) + Ei(x)",
        "piecewise(x < 0, -x, x <= 1, x^2, x > 2, a, x >= 3, b, 1)",
        "piecewise(x < 0, -x, x > 1, x^2)",
        "a*x + b + pi + e + euler_gamma",
        "10^40 * x + 10^-50 + oo",
        "integrate(exp(x^3), x)",
        "x",
    ];

    /// Check that `source` is valid WGSL.
    pub fn validate(source: &str) {
        let module = naga::front::wgsl::parse_str(source)
            .unwrap_or_else(|err| panic!("{}\n{source}", err.emit_to_string(source)));
        naga::valid::Validator::new(
            naga::valid::ValidationFlags::all(),
            naga::valid::Capabilities::all(),
        )
        .validate(&module)
        .unwrap_or_else(|err| panic!("{}\n{source}", err.emit_to_string(source)));
    }

    #[test]
    fn test_literal() {
        assert_eq!(literal(1.5), "1.5e0f");
        assert_eq!(literal(-2.), "(-2e0f)");
        assert_eq!(literal(1e300), "nf_inf()");
        assert_eq!(literal(-1e300), "(-nf_inf())");
        assert_eq!(literal(1e-300), "0.0");
        assert_eq!(literal(f64::NAN), "nf_nan()");
    }

    #[test]
    fn test_render() {
        for input in EXPRESSIONS {
            validate(&render(&[(&compile(input), Comparison::Equal)]));
        }
        let (f, g) = (compile("x^2 + y^2 - a"), compile("y - b"));
        validate(&render(&[
            (&f, Comparison::Less),
            (&g, Comparison::GreaterEqual),
        ]));
    }

    #[test]
    fn test_analysis() {
        let f = compile("a*x^3 - x");
        let derivative = compile("3*a*x^2 - 1");
        let g = compile("b*x");
        let h = compile("sin(x)");
        validate(&analysis(&AnalysisCurves {
            f: (&f, 1),
            derivative: Some(&derivative),
            others: vec![(&g, 1), (&h, 0)],
        }));
        validate(&analysis(&AnalysisCurves {
            f: (&f, 1),
            derivative: None,
            others: vec![],
        }));
    }
}
