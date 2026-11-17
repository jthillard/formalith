use formalith::{
    field::{matrix::M, real::R},
    parse,
    term::Expand,
};

pub fn main() {
    tracing_subscriber::fmt::init();
    println!("{}", parse!("x^2 + x^2", R));
    println!("{}", parse!("(x+y)^3", R).expand());
    println!("{}", parse!("71/1200 + (x^6*2)^-1", R));
    println!("{}", parse!("-5+x", R));

    println!("{}", parse!("[[x, 4], [2, 3]]^-1", M));
    println!("{}", parse!("[[x, 4], [2, 3]]^-1", M).expand());
    println!("{}", parse!("[[x, 4], [2, 3]]^-1", M).simplify());

    println!(
        "{}",
        parse!("x^n", R)
            .to_polynomial()
            .gcd(&parse!("x^2", R).to_polynomial())
    );
    println!(
        "{}",
        parse!("x^(2*n)", R)
            .to_polynomial()
            .gcd(&parse!("x^n", R).to_polynomial())
    );
    println!("{}", parse!("(x^n + 3)^3", R).to_polynomial());
    println!("=");
    println!(
        "{}",
        parse!("x^(3*n)", R)
            .to_polynomial()
            .quot_rem(&parse!("n*x", R).to_polynomial())
            .0
    );
    let matrix = parse!("[[x, 4], [2, 3]]", M);
    let det = matrix.det().unwrap();
    println!("{det}");
    let det = parse!("det([[x, 4], [2, 3]])", R);
    println!("{det}");
}
