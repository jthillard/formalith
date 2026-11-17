//! Generic matrices and the matrix set `M`.
use formalith::{
    field::{matrix::M, real::R},
    matrix::{Matrix, MatrixError},
    parse, try_parse,
};
use malachite::Rational;

mod common;
use common::{line, pretty};

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
}

#[test]
#[ignore = "known bug: a scalar on the left of a matrix fails to parse"]
fn scalar_times_matrix() {
    assert_eq!(parse!("2*[[1,2],[3,4]]", M), parse!("[[2,4],[6,8]]", M));
}

#[test]
fn invalid_matrix_addition_does_not_panic() {
    let _ = try_parse!("[[1,2],[3,4]]+1", M);
    let _ = try_parse!("[[1,2],[3,4]]+[[1,2,3],[4,5,6]]", M);
}
