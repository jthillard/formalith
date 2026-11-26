//! Generic matrices and the matrix set `M`.
use formalith::{dynamic::SetChoice, parser::environment::Environment};
use formalith::{
    field::{integer::Z, matrix::M, modular::Zn, real::R},
    matrix::{Matrix, MatrixError},
    parse,
    term::TermSet,
    try_parse,
};
use malachite::{Integer, Rational};

use crate::common::{line, pretty};

fn matrix(height: usize, width: usize, data: &[i64]) -> Matrix<R<Rational>> {
    assert_eq!(data.len(), height * width);
    Matrix::new(
        (height, width),
        data.iter().map(|&x| Rational::from(x)).collect(),
        R,
    )
}

fn entries(m: &Matrix<R<Rational>>) -> Vec<Rational> {
    (0..m.height())
        .flat_map(|i| (0..m.width()).map(move |j| (i, j)))
        .map(|index| m[index].clone())
        .collect()
}

fn q(num: i64, den: i64) -> Rational {
    Rational::from_signeds(num, den)
}

#[test]
fn dimensions_and_indexing() {
    let m = matrix(2, 3, &[1, 2, 3, 4, 5, 6]);
    assert_eq!(m.height(), 2);
    assert_eq!(m.width(), 3);
    assert_eq!(m.size(), 6);
    assert_eq!(m[(0, 0)], 1);
    assert_eq!(m[(0, 2)], 3);
    assert_eq!(m[(1, 0)], 4);
    assert_eq!(m[(1, 2)], 6);
    assert_eq!(m[4], 5);
}

#[test]
fn index_mut() {
    let mut m = matrix(2, 2, &[1, 2, 3, 4]);
    m[(1, 0)] = Rational::from(9);
    m[1] = Rational::from(8);
    assert_eq!(m, matrix(2, 2, &[1, 8, 9, 4]));
}

#[test]
fn zero_matrix() {
    assert_eq!(Matrix::zero((2, 3), R), matrix(2, 3, &[0; 6]));
}

#[test]
fn addition_and_negation() {
    let a = matrix(2, 2, &[1, 2, 3, 4]);
    let b = matrix(2, 2, &[1, 1, 1, 1]);
    assert_eq!(a.clone() + b.clone(), matrix(2, 2, &[2, 3, 4, 5]));
    assert_eq!(a.clone() + &b, matrix(2, 2, &[2, 3, 4, 5]));
    assert_eq!(&a + &b, matrix(2, 2, &[2, 3, 4, 5]));
    assert_eq!(-&a, matrix(2, 2, &[-1, -2, -3, -4]));
    assert_eq!(-a.clone(), matrix(2, 2, &[-1, -2, -3, -4]));
    assert_eq!(&a + &-&a, Matrix::zero((2, 2), R));
}

#[test]
fn row_operations() {
    let mut m = matrix(2, 2, &[1, 2, 3, 4]);
    m.swap_rows(0, 1);
    assert_eq!(m, matrix(2, 2, &[3, 4, 1, 2]));
    m.scale_row(1, &Rational::from(2));
    assert_eq!(m, matrix(2, 2, &[3, 4, 2, 4]));
    m.row_add(0, 1, &Rational::from(-1));
    assert_eq!(m, matrix(2, 2, &[1, 0, 2, 4]));
    m.external_product(&Rational::from(3));
    assert_eq!(m, matrix(2, 2, &[3, 0, 6, 12]));
}

#[test]
fn determinant() {
    assert_eq!(matrix(1, 1, &[7]).det().unwrap(), 7);
    assert_eq!(matrix(2, 2, &[1, 2, 3, 4]).det().unwrap(), -2);
    assert_eq!(matrix(2, 2, &[0, 1, 1, 0]).det().unwrap(), -1);
    assert_eq!(
        matrix(3, 3, &[1, 2, 3, 4, 5, 6, 7, 8, 10]).det().unwrap(),
        -3
    );
    assert_eq!(matrix(3, 3, &[2, 0, 1, 1, 3, 2, 1, 1, 2]).det().unwrap(), 6);
    assert_eq!(matrix(3, 3, &[1, 0, 0, 0, 1, 0, 0, 0, 1]).det().unwrap(), 1);
    // Singular matrices
    assert_eq!(matrix(3, 3, &[1, 2, 3, 2, 4, 6, 1, 1, 1]).det().unwrap(), 0);
    assert_eq!(matrix(3, 3, &[0; 9]).det().unwrap(), 0);
    // Upper triangular: product of the diagonal
    assert_eq!(
        matrix(4, 4, &[2, 1, 1, 1, 0, 3, 1, 1, 0, 0, 4, 1, 0, 0, 0, 5])
            .det()
            .unwrap(),
        120
    );
}

#[test]
fn determinant_of_non_square_matrix() {
    assert!(matches!(
        matrix(2, 3, &[1, 2, 3, 4, 5, 6]).det(),
        Err(MatrixError::NotSquare)
    ));
    assert!(matches!(
        matrix(2, 3, &[1, 2, 3, 4, 5, 6]).det_in_place(),
        Err(MatrixError::NotSquare)
    ));
}

#[test]
fn rank() {
    assert_eq!(
        matrix(3, 3, &[1, 2, 3, 2, 4, 6, 1, 1, 1])
            .partial_row_reduce()
            .unwrap(),
        2
    );
    assert_eq!(
        matrix(3, 3, &[1, 0, 0, 0, 1, 0, 0, 0, 1])
            .partial_row_reduce()
            .unwrap(),
        3
    );
    assert_eq!(matrix(2, 2, &[0; 4]).partial_row_reduce().unwrap(), 0);
    assert_eq!(
        matrix(2, 3, &[1, 2, 3, 2, 4, 6])
            .partial_row_reduce()
            .unwrap(),
        1
    );
}

#[test]
fn row_reduce() {
    let mut m = matrix(2, 3, &[1, 2, 3, 4, 5, 6]);
    m.row_reduce().unwrap();
    assert_eq!(m, matrix(2, 3, &[1, 0, -1, 0, 1, 2]));

    let mut m = matrix(2, 2, &[0, 2, 3, 0]);
    m.row_reduce().unwrap();
    assert_eq!(m, matrix(2, 2, &[1, 0, 0, 1]));
}

#[test]
fn inverse() {
    let inv = matrix(2, 2, &[1, 2, 3, 4]).inv().unwrap();
    assert_eq!((inv.height(), inv.width()), (2, 2));
    assert_eq!(entries(&inv), vec![q(-2, 1), q(1, 1), q(3, 2), q(-1, 2)]);

    let inv = matrix(2, 2, &[0, 1, 1, 0]).inv().unwrap();
    assert_eq!(entries(&inv), vec![q(0, 1), q(1, 1), q(1, 1), q(0, 1)]);

    let inv = matrix(3, 3, &[2, 0, 1, 1, 3, 2, 1, 1, 2]).inv().unwrap();
    assert_eq!(
        entries(&inv),
        vec![
            q(2, 3),
            q(1, 6),
            q(-1, 2),
            q(0, 1),
            q(1, 2),
            q(-1, 2),
            q(-1, 3),
            q(-1, 3),
            q(1, 1)
        ]
    );
}

#[test]
fn inverse_of_non_square_matrix() {
    assert!(matches!(
        matrix(2, 3, &[1, 2, 3, 4, 5, 6]).inv(),
        Err(MatrixError::NotSquare)
    ));
}

#[test]
fn print_square_matrix() {
    let m = matrix(2, 2, &[1, 2, 3, 4]);
    assert_eq!(line(&m), "[[1,2],[3,4]]");
    assert_eq!(pretty(&m), "⎡1  2⎤\n⎢    ⎥\n⎣3  4⎦");
}

#[test]
fn pretty_print_non_square_matrix() {
    assert_eq!(
        pretty(&matrix(2, 3, &[1, 2, 3, 4, 5, 6])),
        "⎡1  2  3⎤\n⎢       ⎥\n⎣4  5  6⎦"
    );
}

// Matrices as terms, in the set `M`

#[test]
fn parse_matrix_literals() {
    assert_eq!(line(&parse!("[[1,2],[3,4]]", M)), "[[1,2],[3,4]]");
    assert_eq!(
        line(&parse!("[[x+1, 2], [3, x^2]]", M)),
        "[[x+1,2],[3,x^2]]"
    );
    assert_eq!(line(&parse!("5", M)), "5");
}

#[test]
fn parse_invalid_matrix_literals() {
    for input in [
        "[[1,2],[3]]",
        "[[]]",
        "[]",
        "[1,2]",
        "[[1,2],[3,4]",
        "[[1,2] [3,4]]",
        "[[[1]]]",
    ] {
        assert!(try_parse!(input, M).is_err(), "{input}");
    }
}

#[test]
fn matrix_term_operations() {
    assert_eq!(
        parse!("[[1,2],[3,4]]+[[1,0],[0,1]]", M),
        parse!("[[2,2],[3,5]]", M)
    );
    assert_eq!(
        parse!("[[1,2],[3,4]]-[[1,2],[3,4]]", M),
        parse!("[[0,0],[0,0]]", M)
    );
    assert_eq!(parse!("[[1,2],[3,4]]*2", M), parse!("[[2,4],[6,8]]", M));
    assert_eq!(line(&parse!("[[1,2],[3,4]]^-1", M)), "[[-2,1],[3/2,-1/2]]");
}

#[test]
fn matrix_term_det() {
    assert_eq!(
        parse!("[[x, 4], [2, 3]]", M).det().unwrap(),
        parse!("3*x-8", R)
    );
    assert_eq!(parse!("[[1,2],[3,4]]", M).det().unwrap(), (-2).into());
    assert_eq!(parse!("5", M).det().unwrap(), 5.into());
}

#[test]
fn determinant_with_row_swap() {
    assert_eq!(
        matrix(3, 3, &[0, 1, 0, 1, 0, 0, 0, 0, 1]).det().unwrap(),
        -1
    );
    assert_eq!(
        matrix(3, 3, &[0, 1, 2, 1, 0, 3, 4, -3, 8]).det().unwrap(),
        -2
    );
    assert_eq!(
        matrix(4, 4, &[0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
            .det()
            .unwrap(),
        -1
    );
}

#[test]
fn determinant_of_empty_matrix() {
    assert_eq!(matrix(0, 0, &[]).det().unwrap(), 1);
}

#[test]
fn inverse_equals_expected_matrix() {
    let expected = Matrix::new((2, 2), vec![q(1, 2), q(0, 1), q(0, 1), q(1, 2)], R);
    assert_eq!(matrix(2, 2, &[2, 0, 0, 2]).inv().unwrap(), expected);
    assert_eq!(
        parse!("[[1,2],[3,4]]^-1", M),
        parse!("[[-2,1],[3/2,-1/2]]", M)
    );
}

#[test]
fn inverse_of_singular_matrix() {
    assert!(matrix(2, 2, &[1, 2, 2, 4]).inv().is_err());
    assert!(matrix(3, 3, &[2, 0, 1, 1, 3, 2, 1, 1, 1]).inv().is_err());
    assert!(matrix(2, 2, &[0; 4]).inv().is_err());
}

#[test]
fn multiplication() {
    let a = matrix(2, 2, &[1, 2, 3, 4]);
    assert_eq!(&a * &matrix(2, 2, &[1, 0, 0, 1]), a);
    assert_eq!(
        a.clone() * matrix(2, 2, &[5, 6, 7, 8]),
        matrix(2, 2, &[19, 22, 43, 50])
    );
    assert_eq!(
        matrix(1, 2, &[1, 2]) * matrix(2, 1, &[3, 4]),
        matrix(1, 1, &[11])
    );
}

#[test]
fn print_non_square_matrix() {
    assert_eq!(line(&matrix(1, 3, &[1, 2, 3])), "[[1,2,3]]");
    assert_eq!(
        line(&matrix(2, 3, &[1, 2, 3, 4, 5, 6])),
        "[[1,2,3],[4,5,6]]"
    );
    assert_eq!(line(&matrix(2, 1, &[1, 2])), "[[1],[2]]");
}

#[test]
fn matrix_term_product() {
    assert_eq!(
        parse!("[[1,2],[3,4]]*[[5,6],[7,8]]", M),
        parse!("[[19,22],[43,50]]", M)
    );
    assert_eq!(parse!("[[1,2],[3,4]]^2", M), parse!("[[7,10],[15,22]]", M));
    assert_eq!(
        parse!("[[1,2],[3,4]]^3", M),
        parse!("[[37,54],[81,118]]", M)
    );
    assert_eq!(
        parse!("[[1,1],[0,1]]^1000", M),
        parse!("[[1,1000],[0,1]]", M)
    );
}

#[test]
fn scalar_times_matrix() {
    assert_eq!(parse!("2*[[1,2],[3,4]]", M), parse!("[[2,4],[6,8]]", M));
}

#[test]
fn invalid_matrix_addition_does_not_panic() {
    let _ = try_parse!("[[1,2],[3,4]]+1", M);
    let _ = try_parse!("[[1,2],[3,4]]+[[1,2,3],[4,5,6]]", M);
}

#[test]
fn invalid_matrix_product_does_not_panic() {
    let _ = try_parse!("[[1,2]]*[[1,2]]", M);
    let _ = try_parse!("[[1,2],[3,4]]*[[1,2,3]]", M);
}

#[test]
fn small_and_degenerate_matrices() {
    assert_eq!(line(&parse!("[[2]]", M)), "[[2]]");
    assert_eq!(parse!("det([[a]])", R), parse!("a", R));
    assert_eq!(parse!("det([[a, b], [c, d]])", R), parse!("a*d-b*c", R));
    assert!(try_parse!("[[]]", M).is_err());
    assert!(try_parse!("[[1],[2,3]]", M).is_err());
}

#[test]
fn matrix_powers() {
    assert_eq!(line(&parse!("[[1,2],[3,4]]^2", M)), "[[7,10],[15,22]]");
    assert_eq!(line(&parse!("[[1,1],[0,1]]^10", M)), "[[1,10],[0,1]]");
    assert_eq!(line(&parse!("[[0,1],[1,0]]^-1", M)), "[[0,1],[1,0]]");
    // Fibonacci numbers
    assert_eq!(
        line(&parse!("[[1,1],[1,0]]^30", M)),
        "[[1346269,832040],[832040,514229]]"
    );
}

#[test]
fn matrix_to_the_zero() {
    assert_eq!(line(&parse!("[[1,2],[3,4]]^0", M)), "[[1,0],[0,1]]");
}

#[test]
fn singular_matrices_are_not_inverted() {
    assert_eq!(line(&parse!("[[1,2],[2,4]]^-1", M)), "[[1,2],[2,4]]^-1");
}

#[test]
fn determinant_is_multiplicative() {
    assert_eq!(parse!("det([[1,2],[3,4]]*[[5,6],[7,8]])", R), 4.into());
}

#[test]
fn invalid_operations_stay_unevaluated() {
    assert_eq!(line(&parse!("[[1,2,3]]+[[1,2]]", M)), "[[1,2,3]]+[[1,2]]");
    assert_eq!(
        line(&parse!("det([[1,2,3],[4,5,6]])", M)),
        "det([[1,2,3],[4,5,6]])"
    );
    assert_eq!(
        line(&parse!("[[1,2,3],[4,5,6]]*[[1],[2],[3]]", M)),
        "[[14],[32]]"
    );
}

#[test]
fn symbolic_matrices_are_simplified() {
    assert_eq!(
        parse!("factor(det([[1,1,1],[a,b,c],[a^2,b^2,c^2]]))", R),
        parse!("-(a-b)*(a-c)*(b-c)", R)
    );
    assert_eq!(
        parse!(
            "simplify(det([[1,1,1,1],[a,b,c,d],[a^2,b^2,c^2,d^2],[a^3,b^3,c^3,d^3]]))",
            R
        ),
        parse!("expand((b-a)*(c-a)*(d-a)*(c-b)*(d-b)*(d-c))", R)
    );
    assert_eq!(
        line(&parse!("[[a, b], [c, d]]*[[a, b], [c, d]]^-1", M)),
        "[[1,0],[0,1]]"
    );
}

// Linear algebra

fn integers(height: usize, width: usize, data: &[i64]) -> Matrix<Z<Integer>> {
    assert_eq!(data.len(), height * width);
    Matrix::new(
        (height, width),
        data.iter().map(|&x| Integer::from(x)).collect(),
        Z,
    )
}

/// Whether the integer matrix `m` is invertible over `{$ZZ$}`, its determinant (computed over ℚ) being `±1`.
fn unimodular(m: &Matrix<Z<Integer>>) -> bool {
    let rational = Matrix::new(
        (m.height(), m.width()),
        (0..m.height())
            .flat_map(|i| (0..m.width()).map(move |j| (i, j)))
            .map(|index| Rational::from(&m[index]))
            .collect(),
        R,
    );
    let det = rational.det().unwrap();
    det == 1 || det == -1
}

#[test]
fn transpose_trace_rank() {
    let m = matrix(2, 3, &[1, 2, 3, 4, 5, 6]);
    assert_eq!(m.transpose(), matrix(3, 2, &[1, 4, 2, 5, 3, 6]));
    assert_eq!(m.transpose().transpose(), m);
    assert!(matches!(m.trace(), Err(MatrixError::NotSquare)));
    assert_eq!(matrix(2, 2, &[1, 2, 3, 4]).trace().unwrap(), 5);
    assert_eq!(m.rank().unwrap(), 2);
    assert_eq!(matrix(2, 3, &[1, 2, 3, 2, 4, 6]).rank().unwrap(), 1);
}

#[test]
fn kernel() {
    let m = matrix(2, 3, &[1, 2, 3, 4, 5, 6]);
    let kernel = m.kernel().unwrap();
    assert_eq!(kernel, matrix(3, 1, &[1, -2, 1]));
    assert_eq!(&m * &kernel, Matrix::zero((2, 1), R));
    let kernel = matrix(1, 3, &[1, 1, 1]).kernel().unwrap();
    assert_eq!(kernel, matrix(3, 2, &[-1, -1, 1, 0, 0, 1]));
    // Trivial kernel, as a zero column
    assert_eq!(
        matrix(2, 2, &[1, 2, 3, 4]).kernel().unwrap(),
        Matrix::zero((2, 1), R)
    );
}

#[test]
fn characteristic_polynomial() {
    let coefficients = |m: Matrix<R<Rational>>| m.charpoly_coefficients().unwrap();
    assert_eq!(
        coefficients(matrix(2, 2, &[1, 2, 3, 4])),
        vec![q(1, 1), q(-5, 1), q(-2, 1)]
    );
    // `{$det(x I - A) = x^3 - 2 x^2 - 5 x + 6$}`, the constant being `{$-det(A)$}`
    let m = matrix(3, 3, &[1, 2, 0, 2, 1, 0, 0, 0, 0]);
    assert_eq!(coefficients(m), vec![q(1, 1), q(-2, 1), q(-3, 1), q(0, 1)]);
    let m = matrix(3, 3, &[2, 0, 1, 1, 3, 2, 1, 1, 2]);
    let c = coefficients(m.clone());
    assert_eq!(c[1], -m.trace().unwrap());
    assert_eq!(c[3], -m.det().unwrap());
    // Without divisions, over `{$ZZ$}`
    assert_eq!(
        integers(2, 2, &[0, 1, 1, 0])
            .charpoly_coefficients()
            .unwrap(),
        vec![Integer::from(1), Integer::from(0), Integer::from(-1)]
    );
    assert_eq!(
        line(&parse!("charpoly([[1,2],[3,4]], t)", R)),
        line(&parse!("t^2 - 5t - 2", R))
    );
    assert_eq!(
        parse!("charpoly([[1,2],[3,4]])", R),
        parse!("x^2 - 5x - 2", R)
    );
}

#[test]
fn hermite_normal_form() {
    let a = integers(3, 4, &[2, 3, 6, 2, 5, 6, 1, 6, 8, 3, 1, 1]);
    let (u, h, rank) = a.hermite_decomposition();
    assert_eq!(
        h,
        integers(3, 4, &[1, 0, 50, -11, 0, 3, 28, -2, 0, 0, 61, -13])
    );
    assert_eq!(rank, 3);
    assert_eq!(&u * &a, h);
    assert!(unimodular(&u));
    // Rank deficient
    let a = integers(3, 2, &[2, 4, 3, 6, 1, 2]);
    let (u, h, rank) = a.hermite_decomposition();
    assert_eq!((h, rank), (integers(3, 2, &[1, 2, 0, 0, 0, 0]), 1));
    assert_eq!(&u * &a, integers(3, 2, &[1, 2, 0, 0, 0, 0]));
}

#[test]
fn smith_normal_form() {
    let a = integers(3, 3, &[2, 4, 4, -6, 6, 12, 10, -4, -16]);
    let (u, d, v) = a.smith_decomposition();
    assert_eq!(d, integers(3, 3, &[2, 0, 0, 0, 6, 0, 0, 0, 12]));
    assert_eq!(&(&u * &a) * &v, d);
    assert!(unimodular(&u) && unimodular(&v));
    // Divisibility chain, which needs combining rows: `diag(2, 3)` becomes `diag(1, 6)`
    assert_eq!(
        integers(2, 2, &[2, 0, 0, 3]).smith(),
        integers(2, 2, &[1, 0, 0, 6])
    );
    assert_eq!(
        integers(2, 3, &[0, 0, 0, 0, 0, 0]).smith(),
        integers(2, 3, &[0; 6])
    );
    assert_eq!(
        integers(2, 3, &[1, 2, 3, 4, 5, 6]).smith(),
        integers(2, 3, &[1, 0, 0, 0, 3, 0])
    );
}

#[test]
fn matrix_builtins() {
    assert_eq!(
        line(&parse!("transpose([[1,2,3],[4,5,6]])", M)),
        "[[1,4],[2,5],[3,6]]"
    );
    assert_eq!(
        line(&parse!("transpose([[1,2],[3,4]])*[[1],[1]]", M)),
        "[[4],[6]]"
    );
    assert_eq!(line(&parse!("trace([[1,2],[3,4]])", M)), "5");
    assert_eq!(line(&parse!("rank([[1,2],[2,4]])", M)), "1");
    assert_eq!(line(&parse!("det([[1,2],[3,4]])", M)), "-2");
    assert_eq!(line(&parse!("kernel([[1,2],[2,4]])", M)), "[[-2],[1]]");
    assert_eq!(
        line(&parse!("kernel([[a,b],[2a,2b]])", M)),
        "[[-(a^-1)*b],[1]]"
    );
    // Scalar builtins in scalar sets
    assert_eq!(parse!("trace([[1,2],[3,4]])", R), 5.into());
    assert_eq!(parse!("rank([[1,2],[3,4]])", R), 2.into());
    assert_eq!(parse!("trace([[x,1],[1,y]])", R), parse!("x+y", R));
    // Unevaluated
    assert_eq!(
        line(&parse!("trace([[1,2,3],[4,5,6]])", M)),
        "trace([[1,2,3],[4,5,6]])"
    );
}

#[test]
fn eigenvalues_and_eigenvectors() {
    assert_eq!(line(&parse!("eigenvalues([[2,1],[1,2]])", M)), "[[1],[3]]");
    assert_eq!(
        line(&parse!("eigenvectors([[2,1],[1,2]])", M)),
        "[[-1,1],[1,1]]"
    );
    // Repeated eigenvalue with a single eigenvector
    assert_eq!(line(&parse!("eigenvalues([[2,1],[0,2]])", M)), "[[2],[2]]");
    assert_eq!(line(&parse!("eigenvectors([[2,1],[0,2]])", M)), "[[1],[0]]");
    assert_eq!(
        line(&parse!("eigenvectors([[1,0],[0,1]])", M)),
        "[[1,0],[0,1]]"
    );
    assert_eq!(
        line(&parse!("eigenvalues([[2,0,0],[0,3,4],[0,4,9]])", M)),
        "[[1],[2],[11]]"
    );
    // Radical eigenvalues: `{$A v = lambda v$}`
    let values = parse!("eigenvalues([[1,2],[3,4]])", M);
    assert_eq!(
        line(&values),
        "[[-1/2*(33^(1/2))+5/2],[1/2*(33^(1/2))+5/2]]"
    );
    let a = Matrix::new(
        (2, 2),
        [1, 2, 3, 4].map(|x| parse!(&x.to_string(), R)).to_vec(),
        TermSet::new(R),
    );
    let spaces = a.eigenspaces().unwrap();
    assert_eq!(spaces.len(), 2);
    for space in spaces {
        assert_eq!((space.multiplicity, space.basis.width()), (1, 1));
        let av = &a * &space.basis;
        for i in 0..2 {
            let difference = av[(i, 0)].clone() - space.value.clone() * space.basis[(i, 0)].clone();
            assert!(difference.simplify().is_zero(), "{difference}");
        }
    }
    // Complex eigenvalues aren't real, so they stay unevaluated in `M`
    assert_eq!(
        line(&parse!("eigenvalues([[0,-1],[1,0]])", M)),
        "eigenvalues([[0,-1],[1,0]])"
    );
}

#[test]
fn integer_and_modular_matrices() {
    let mz = M::new(TermSet::new(Z));
    let m6 = M::new(TermSet::new(Zn::new(6)));
    assert_eq!(
        line(&parse!("hermite([[2,3,6,2],[5,6,1,6],[8,3,1,1]])", mz)),
        "[[1,0,50,-11],[0,3,28,-2],[0,0,61,-13]]"
    );
    assert_eq!(
        line(&parse!("smith([[2,4,4],[-6,6,12],[10,-4,-16]])", mz)),
        "[[2,0,0],[0,6,0],[0,0,12]]"
    );
    // A lattice basis of the kernel
    assert_eq!(line(&parse!("kernel([[2,3]])", mz)), "[[3],[-2]]");
    assert_eq!(line(&parse!("rank([[2,4],[1,2]])", mz)), "1");
    assert_eq!(line(&parse!("smith([[2,4],[6,8]])", m6)), "[[2,0],[0,2]]");
    assert_eq!(line(&parse!("hermite([[2,4],[3,1]])", m6)), "[[1,1],[0,2]]");
    assert_eq!(line(&parse!("kernel([[1,1]])", m6)), "[[5],[1]]");
    // The pivot 4 isn't invertible
    assert_eq!(
        line(&parse!("rank([[1,2],[3,4]])", m6)),
        "rank([[1,2],[3,4]])"
    );
}

#[test]
fn identity() {
    assert_eq!(line(&parse!("I(2)", M)), "[[1,0],[0,1]]");
    // The size is an integer expression
    assert_eq!(line(&parse!("I(1+1)", M)), "[[1,0],[0,1]]");
    assert_eq!(line(&parse!("I(3)*[[1],[2],[3]]", M)), "[[1],[2],[3]]");
    assert_eq!(line(&parse!("det(I(4))", M)), "1");
    // Scalars times builtins returning matrices are products in `M`, not scalars
    assert_eq!(line(&parse!("2*I(2)", M)), "[[2,0],[0,2]]");
    assert_eq!(line(&parse!("2*transpose([[1,2]])", M)), "[[2],[4]]");
    assert_eq!(
        line(&parse!("[[1,2],[3,4]] - x*I(2)", M)),
        line(&parse!("[[1-x,2],[3,4-x]]", M))
    );
    assert_eq!(
        line(&parse!("expand(det(x*I(2) - [[1,2],[3,4]]))", M)),
        line(&parse!("charpoly([[1,2],[3,4]])", M))
    );
    assert_eq!(
        line(&parse!("I(2)", M::new(TermSet::new(Zn::new(5))))),
        "[[1,0],[0,1]]"
    );
    // Unevaluated without a positive integer size, or outside of matrices
    assert_eq!(line(&parse!("I(n)", M)), "I(n)");
    assert_eq!(line(&parse!("I(0)", M)), "I(0)");
    assert_eq!(line(&parse!("I(3)", R)), "I(3)");
}

#[test]
fn gradient_jacobian_hessian() {
    assert_eq!(line(&parse!("gradient(x^2*y, x, y)", M)), "[[2*x*y],[x^2]]");
    // Every symbol sorted by name by default, without constants
    assert_eq!(
        line(&parse!("gradient(x^2*y + pi*sin(z))", M)),
        line(&parse!("[[2*x*y],[x^2],[pi*cos(z)]]", M))
    );
    assert_eq!(
        line(&parse!("jacobian([[x*y],[x+y]], x, y)", M)),
        "[[y,x],[1,1]]"
    );
    // Rows of functions and variables, and a scalar function
    assert_eq!(
        line(&parse!("jacobian([[x*y, x+y]], [[x, y]])", M)),
        "[[y,x],[1,1]]"
    );
    assert_eq!(line(&parse!("jacobian(x*y)", M)), "[[y,x]]");
    assert_eq!(
        line(&parse!("hessian(x^3*y, x, y)", M)),
        line(&parse!("[[6*x*y, 3*x^2], [3*x^2, 0]]", M))
    );
    // Polar coordinates
    assert_eq!(
        line(&parse!(
            "simplify(det(jacobian([[r*cos(t)],[r*sin(t)]], r, t)))",
            M
        )),
        "r"
    );
    // A constant has no variable, and a matrix isn't a scalar function
    assert_eq!(line(&parse!("gradient(5)", M)), "gradient(5)");
    assert_eq!(
        line(&parse!("gradient([[x, y]], x)", M)),
        "gradient([[x,y]], x)"
    );
}

#[test]
fn zeros_and_diag() {
    assert_eq!(line(&parse!("zeros(2)", M)), "[[0,0],[0,0]]");
    assert_eq!(line(&parse!("zeros(1, 3)", M)), "[[0,0,0]]");
    assert_eq!(line(&parse!("zeros(2) + I(2)", M)), "[[1,0],[0,1]]");
    assert_eq!(line(&parse!("diag(1, 2)", M)), "[[1,0],[0,2]]");
    assert_eq!(line(&parse!("diag([[a, b]])", M)), "[[a,0],[0,b]]");
    assert_eq!(line(&parse!("diag([[1],[2]])", M)), "[[1,0],[0,2]]");
    assert_eq!(line(&parse!("2*diag(1, 2)", M)), "[[2,0],[0,4]]");
    assert_eq!(line(&parse!("det(diag(2, 3, 5))", M)), "30");
    // Sizes must be positive
    assert_eq!(line(&parse!("zeros(0)", M)), "zeros(0)");
}

#[test]
fn roots() {
    assert_eq!(line(&parse!("roots(x^3 - x^2)", M)), "[[0],[0],[1]]");
    assert_eq!(line(&parse!("roots(t^2 - 3*t + 2, t)", M)), "[[1],[2]]");
    let roots = parse!("roots(x^2 - 2)", M);
    assert_eq!(line(&roots), line(&parse!("[[sqrt(2)],[-sqrt(2)]]", M)));
    // Without real root, or not a polynomial
    assert_eq!(line(&parse!("roots(x^2 + 1)", M)), "roots(x^2+1)");
    assert_eq!(line(&parse!("roots(5)", M)), "roots(5)");
    assert_eq!(line(&parse!("roots(sin(x))", M)), "roots(sin(x))");
    // Without radicals
    assert_eq!(
        line(&parse!("roots((x^5 - x - 1)^2*(x - 1))", M)),
        "[[rootof(-x+x^5-1, 1)],[rootof(-x+x^5-1, 1)],[1]]"
    );
    let companion = "[[0,0,0,0,-1],[1,0,0,0,-4],[0,1,0,0,0],[0,0,1,0,5],[0,0,0,1,0]]";
    assert_eq!(
        line(&parse!(&format!("eigenvalues({companion})"), M)),
        format!(
            "[{}]",
            (1..=5)
                .map(|k| format!("[rootof(4*x-5*(x^3)+x^5+1, {k})]"))
                .collect::<Vec<_>>()
                .join(",")
        )
    );
}

#[test]
fn factorint() {
    assert_eq!(line(&parse!("factorint(360)", M)), "[[2,3],[3,2],[5,1]]");
    assert_eq!(line(&parse!("factorint(-3/4)", M)), "[[-1,1],[2,-2],[3,1]]");
    assert_eq!(line(&parse!("factorint(1)", M)), "[[1,1]]");
    assert_eq!(
        line(&parse!("factorint(2^67 - 1)", M)),
        "[[193707721,1],[761838257287,1]]"
    );
    let mz = M::new(TermSet::new(Z));
    assert_eq!(line(&parse!("factorint(-12)", mz)), "[[-1,1],[2,2],[3,1]]");
    assert_eq!(line(&parse!("factorint(0)", M)), "factorint(0)");
}

#[test]
fn leading_minus_of_scalars() {
    let m = |input: &str| {
        SetChoice::M
            .eval(input, false, &mut Environment::new())
            .unwrap()
    };
    assert_eq!(m("-72*x + 7"), m("7 - 72*x"));
    assert_eq!(m("-2*x*y"), m("(-2)*x*y"));
    assert_eq!(m("-2*I(2) + [[1, 2], [3, 4]]"), m("[[-1, 2], [3, 2]]"));
}

#[test]
fn scalar_builtins_evaluated_in_m() {
    let m = |input: &str| {
        SetChoice::M
            .eval(input, false, &mut Environment::new())
            .unwrap()
    };
    assert_eq!(m("trace([[1, 2], [3, 4]])"), "5");
    assert_eq!(m("rank([[1, 2], [2, 4]])"), "1");
    assert_eq!(m("charpoly([[1, 2], [3, 4]], y)"), m("y^2 - 5*y - 2"));
    assert_eq!(m("charpoly([[1, 2], [3, 4]])"), m("x^2 - 5*x - 2"));
    assert_eq!(m("det([[x, 1], [1, x]])"), m("x^2 - 1"));
    // Scalars times matrices, inverses and division by a scalar
    assert_eq!(
        m("trace([[x, 1], [1, y]])*[[1, 0], [0, 1]]"),
        m("[[x + y, 0], [0, x + y]]")
    );
    assert_eq!(m("[[x, 1], [0, x]]^-1"), m("[[1/x, -1/x^2], [0, 1/x]]"));
    assert_eq!(m("[[1, 2], [3, 4]]/2"), m("[[1/2, 1], [3/2, 2]]"));
}

#[test]
fn complex_matrices() {
    let mc = |input: &str| {
        SetChoice::MC
            .eval(input, false, &mut Environment::new())
            .unwrap()
    };
    assert_eq!(mc("eigenvalues([[0, -1], [1, 0]])"), mc("[[-i], [i]]"));
    assert_eq!(
        mc("eigenvectors([[0, -1], [1, 0]])"),
        mc("[[-i, i], [1, 1]]")
    );
    assert_eq!(
        mc("eigenvalues([[0, -1, 0], [1, 0, 0], [0, 0, 2]])"),
        mc("[[-i], [i], [2]]")
    );
    assert_eq!(mc("eigenvalues([[i, 1], [0, -i]])"), mc("[[-i], [i]]"));
    assert_eq!(
        mc("eigenvectors([[i, 1], [0, -i]])"),
        mc("[[i/2, 1], [1, 0]]")
    );
    assert_eq!(mc("eigenvalues([[2, 1], [1, 2]])"), mc("[[1], [3]]"));
    assert_eq!(mc("det([[i, 1], [2, i]])"), "-3");
    assert_eq!(mc("[[i, 1], [2, i]]^-1"), mc("[[-i/3, 1/3], [2/3, -i/3]]"));
    assert_eq!(mc("roots(x^2 + 1)"), mc("[[-i], [i]]"));
    // Cubics by Cardano's formula
    let entries = |input: &str| {
        let typst = SetChoice::MC
            .eval(input, true, &mut Environment::new())
            .unwrap();
        assert!(typst.starts_with("mat("), "{typst}");
        typst.matches(';').count() + 1
    };
    assert_eq!(
        entries("eigenvalues([[3, 2, 3], [-2, 2, -1], [3, 1, -1]])"),
        3
    );
    assert_eq!(entries("roots(x^3 + x + 1)"), 3);
    assert_eq!(mc("gradient(x^2 + i*y, x, y)"), mc("[[2*x], [i]]"));
    // Real matrices keep non-real eigenvalues unevaluated
    let m = SetChoice::M
        .eval(
            "eigenvalues([[0, -1], [1, 0]])",
            false,
            &mut Environment::new(),
        )
        .unwrap();
    assert!(m.contains("eigenvalues"), "{m}");
}

#[test]
fn builtins_on_matrix_entries() {
    let mut env = Environment::new();
    let mut m = |input: &str| SetChoice::M.eval(input, false, &mut env).unwrap();
    assert_eq!(
        m("simplify([[sin(x)^2 + cos(x)^2, 1], [0, x]])"),
        m("[[1, 1], [0, x]]")
    );
    assert_eq!(m("simplify([[x, 1], [0, x]])"), m("[[x, 1], [0, x]]"));
    assert_eq!(m("expand([[(x + 1)^2]])"), m("[[x^2 + 2*x + 1]]"));
    assert_eq!(m("factor([[x^2 - 1]])"), m("[[(x - 1)*(x + 1)]]"));
    assert_eq!(
        m("diff([[x^2, x], [1, x^3]], x)"),
        m("[[2*x, 1], [0, 3*x^2]]")
    );
    assert_eq!(
        m("diff([[x^2, x], [1, x^3]], x, 2)"),
        m("[[2, 0], [0, 6*x]]")
    );
    assert_eq!(m("diff(I(2)*x, x)"), m("I(2)"));
    assert_eq!(m("subs([[x, 1]], x, 2)"), m("[[2, 1]]"));
    assert_eq!(m("integrate([[x, cos(x)]], x)"), m("[[x^2/2, sin(x)]]"));
    assert_eq!(
        m("simplify([[x, 1], [0, x]]) + I(2)"),
        m("[[x + 1, 1], [0, x + 1]]")
    );
    // Definitions of matrices
    m("A := [[x^2, x]]");
    assert_eq!(m("diff(A, x)"), m("[[2*x, 1]]"));
    // Scalars are unchanged
    assert_eq!(m("simplify(x^2)"), m("x^2"));
    assert_eq!(m("2*diff(x^2, x)"), m("4*x"));
    let mzn = |input: &str| {
        SetChoice::MZn(7)
            .eval(input, false, &mut Environment::new())
            .unwrap()
    };
    assert_eq!(mzn("expand([[(x + 1)^2, 9]])"), mzn("[[x^2 + 2*x + 1, 2]]"));
}
