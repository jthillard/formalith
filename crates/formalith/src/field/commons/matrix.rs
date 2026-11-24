//! The matrix ring `{$M$}`.

use malachite::{Integer, rational::Rational};
use std::{
    cmp::Ordering,
    collections::BTreeSet,
    fmt::{self, Debug, Display},
};

use crate::{
    context::{Context, Symbol},
    field::{
        EuclideanRing, Group, Monoid, PartiallyOrderedSet, Ring, Semiring, Set, SetParseExpression,
        integer::Z, modular::Zn, primes, real::R,
    },
    matrix::{Matrix, MatrixResult, eigen::real_roots},
    parser::{Parser, ParserError, lexer::TokenKind},
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    solve::polynomial::polynomial_form,
    term::{self, Expand, Function, Term, TermSet, Value},
};

/// An enum representing elements inside a vector space.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VectorSpaceElement<T: Set, Vector> {
    /// A scalar element living in `T`
    Scalar(T::Element, T),
    /// A vector living in the vector space
    Vector(Vector),
}

impl<T: Ring> VectorSpaceElement<T, Matrix<T>> {
    /// Compute the determinant of self in set `T`.
    ///
    /// # Errors
    /// This will returns an error if the element is a matrix and the determinant cannot be computed,
    /// for instance if the matrix is not square.
    pub fn det(&self) -> MatrixResult<T::Element> {
        match self {
            Self::Scalar(scalar, _) => Ok(scalar.clone()),
            Self::Vector(matrix) => matrix.det(),
        }
    }
}

impl<T: PartiallyOrderedSet, Vector: PartialEq> PartialOrd for VectorSpaceElement<T, Vector> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Scalar(s1, set), Self::Scalar(s2, _)) => set.partial_cmp(s1, s2),
            _ => None,
        }
    }
}
impl<T: Set, Vector: Print> Print for VectorSpaceElement<T, Vector> {
    fn print(
        &self,
        options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            Self::Scalar(scalar, set) => set.print(scalar, options, f),
            Self::Vector(vector) => vector.print(options, f),
        }
    }
}

impl<T: Set, Vector: PrettyPrint> PrettyPrint for VectorSpaceElement<T, Vector> {
    fn pretty_print(&self, options: &crate::printer::PrintOptions) -> PrettyPrinter {
        match self {
            Self::Scalar(scalar, set) => set.pretty_print(scalar, options),
            Self::Vector(vector) => vector.pretty_print(options),
        }
    }
}

impl<T: Set, Vector: PrettyPrint> Display for VectorSpaceElement<T, Vector> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// The matrix ring.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct M<T> {
    pub(crate) scalar_sub_set: T,
}

impl<T> M<T> {
    /// Create a new matrix ring over T
    pub const fn new(scalar_sub_set: T) -> Self {
        Self { scalar_sub_set }
    }
}

impl<T: Set> Set for M<T> {
    type Element = VectorSpaceElement<T, Matrix<T>>;

    type ExponantSet = M<T::ExponantSet>;
    type ProductCoefficientSet = M<T::ProductCoefficientSet>;
    fn get_exponant_set(&self) -> Self::ExponantSet {
        self.scalar_sub_set.get_exponant_set().get_matrix_set()
    }
    fn get_coefficient_set(&self) -> Self::ProductCoefficientSet {
        self.scalar_sub_set.get_coefficient_set().get_matrix_set()
    }
    fn print(
        &self,
        elem: &Self::Element,
        options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match elem {
            VectorSpaceElement::Scalar(scalar, _) => self.scalar_sub_set.print(scalar, options, f),
            VectorSpaceElement::Vector(matrix) => Print::print(matrix, options, f),
        }
    }
    fn pretty_print(
        &self,
        elem: &Self::Element,
        options: &crate::printer::PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        match elem {
            VectorSpaceElement::Scalar(scalar, _) => {
                self.scalar_sub_set.pretty_print(scalar, options)
            }
            VectorSpaceElement::Vector(matrix) => PrettyPrint::pretty_print(matrix, options),
        }
    }
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        a == b
    }
}

impl<T: PartiallyOrderedSet> PartiallyOrderedSet for M<T> {
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        match (a, b) {
            (VectorSpaceElement::Scalar(a, _), VectorSpaceElement::Scalar(b, _)) => {
                self.scalar_sub_set.partial_cmp(a, b)
            }
            _ => None,
        }
    }
    fn total_cmp(&self, a: &Self::Element, b: &Self::Element) -> Ordering {
        match (a, b) {
            (VectorSpaceElement::Scalar(a, _), VectorSpaceElement::Scalar(b, _)) => {
                self.scalar_sub_set.total_cmp(a, b)
            }
            _ => Ordering::Equal,
        }
    }
}

impl<T: Group> Monoid for M<T> {
    fn zero(&self) -> Self::Element {
        VectorSpaceElement::Scalar(self.scalar_sub_set.zero(), self.scalar_sub_set)
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        self.try_add(a, b)
            .unwrap_or_else(|| panic!("Can't add {a} and {b} !"))
    }

    fn try_add(&self, a: &Self::Element, b: &Self::Element) -> Option<Self::Element> {
        match (a, b) {
            (VectorSpaceElement::Scalar(a, _), VectorSpaceElement::Scalar(b, _)) => Some(
                VectorSpaceElement::Scalar(self.scalar_sub_set.add(a, b), self.scalar_sub_set),
            ),
            (VectorSpaceElement::Vector(a), VectorSpaceElement::Vector(b))
                if a.height() == b.height() && a.width() == b.width() =>
            {
                Some(VectorSpaceElement::Vector(a + b))
            }
            _ => None,
        }
    }
}

impl<T: Group> Group for M<T> {
    fn nth(&self, nth: i64) -> Self::Element {
        VectorSpaceElement::Scalar(self.scalar_sub_set.nth(nth), self.scalar_sub_set)
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        match a {
            VectorSpaceElement::Scalar(a, _) => {
                VectorSpaceElement::Scalar(self.scalar_sub_set.neg(a), self.scalar_sub_set)
            }
            VectorSpaceElement::Vector(a) => VectorSpaceElement::Vector(-a),
        }
    }
}
impl<T: Ring> M<T> {
    /// Apply `f` (an operation of the scalar set: normalize, expand or simplify) to a scalar, or to every entry
    /// of a matrix. `f` must return a value; `done` names the operation in the panic message otherwise.
    fn map_entries(
        &self,
        element: &VectorSpaceElement<T, Matrix<T>>,
        done: &str,
        f: impl Fn(Term<T>) -> Term<T>,
    ) -> Term<Self> {
        let not_a_value = || {
            format!(
                "{done} expression is not a value and should be converted inside the matrix ring"
            )
        };
        let element = match element {
            VectorSpaceElement::Vector(matrix) => {
                let mut res = matrix.clone();
                for x in &mut res.data {
                    *x = f(Term::Value(Value::new(x.clone(), self.scalar_sub_set)))
                        .as_value()
                        .unwrap_or_else(|| panic!("{}", not_a_value()))
                        .value;
                }
                VectorSpaceElement::Vector(res)
            }
            VectorSpaceElement::Scalar(scalar, _) => {
                match f(Term::Value(Value::new(scalar.clone(), self.scalar_sub_set))) {
                    Term::Value(Value { value, .. }) => {
                        VectorSpaceElement::Scalar(value, self.scalar_sub_set)
                    }
                    _ => unimplemented!("{}", not_a_value()),
                }
            }
        };
        Term::Value(Value::new(element, *self))
    }

    /// Evaluate the matrix builtins (`det`, `transpose`, `trace`, `rank`, `kernel`, `charpoly`, `eigenvalues`,
    /// `eigenvectors`, `hermite` and `smith`) of a matrix value, `gradient`, `jacobian`, `hessian`, and the identity
    /// `I(n)`. Returns `None` for other functions, or when they can't be evaluated, like the trace of a non-square
    /// matrix.
    fn eval_builtin(&self, fun: &dyn Function<Self>) -> Option<VectorSpaceElement<T, Matrix<T>>> {
        // Bounded, so that a huge size doesn't abort on allocation
        const MAX_SIZE: usize = 1000;
        if fun.get_ident() == Context::IDENTITY {
            let Some(Term::Value(Value { value: n, .. })) = fun.get_args::<Z<Integer>>()?.first()
            else {
                return None;
            };
            let n = usize::try_from(n)
                .ok()
                .filter(|n| (1..=MAX_SIZE).contains(n))?;
            return Some(VectorSpaceElement::Vector(Matrix::identity(
                n,
                self.scalar_sub_set,
            )));
        }
        if fun.get_ident() == Context::ZEROS {
            let sizes = fun
                .get_args::<Z<Integer>>()?
                .iter()
                .map(|size| match size {
                    Term::Value(Value { value: n, .. }) => usize::try_from(n)
                        .ok()
                        .filter(|n| (1..=MAX_SIZE).contains(n)),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            let (height, width) = match sizes.as_slice() {
                [n] => (*n, *n),
                [n, m] => (*n, *m),
                _ => return None,
            };
            return Some(VectorSpaceElement::Vector(Matrix::zero(
                (height, width),
                self.scalar_sub_set,
            )));
        }
        let args = fun.get_args::<Self>()?;
        if matches!(
            fun.get_ident(),
            Context::GRADIENT | Context::JACOBIAN | Context::HESSIAN
        ) {
            return self
                .eval_derivatives(fun.get_ident(), args)
                .map(VectorSpaceElement::Vector);
        }
        let scalars = self.scalar_sub_set;
        let scalar = |element| VectorSpaceElement::Scalar(element, scalars);
        match fun.get_ident() {
            Context::DIAG => {
                let entries = match args.as_slice() {
                    [vector] => Self::vector_entries(vector)?,
                    _ => args
                        .iter()
                        .map(|arg| match arg {
                            Term::Value(Value {
                                value: VectorSpaceElement::Scalar(x, _),
                                ..
                            }) => Some(x.clone()),
                            _ => None,
                        })
                        .collect::<Option<_>>()?,
                };
                let n = entries.len();
                let mut matrix = Matrix::zero((n, n), scalars);
                for (i, entry) in entries.into_iter().enumerate() {
                    matrix[(i, i)] = entry;
                }
                return Some(VectorSpaceElement::Vector(matrix));
            }
            Context::ROOTS => {
                let (p, x) = match args.as_slice() {
                    [p] => (Self::scalar(p)?, None),
                    [p, x] => (Self::scalar(p)?, Some(Self::symbol(x)?)),
                    _ => return None,
                };
                let x = if let Some(x) = x {
                    x
                } else {
                    let symbols: Vec<_> = <T as MatrixEntries>::symbols(p)?
                        .into_iter()
                        .filter(|x| !Context::is_builtin_constant(*x))
                        .collect();
                    match symbols.as_slice() {
                        [x] => *x,
                        _ => return None,
                    }
                };
                let roots = <T as MatrixEntries>::roots(p, x)?;
                return Some(VectorSpaceElement::Vector(Matrix::new(
                    (roots.len(), 1),
                    roots,
                    scalars,
                )));
            }
            Context::FACTORINT => {
                let [n] = args.as_slice() else { return None };
                return <T as MatrixEntries>::factorint(Self::scalar(n)?)
                    .map(VectorSpaceElement::Vector);
            }
            _ => {}
        }
        let matrix = match args.first()? {
            Term::Value(Value {
                value: VectorSpaceElement::Vector(matrix),
                ..
            }) => matrix,
            Term::Value(Value {
                value: value @ VectorSpaceElement::Scalar(..),
                ..
            }) if fun.get_ident() == Context::DET => return Some(value.clone()),
            _ => return None,
        };
        let eigenspaces = || <T as MatrixEntries>::eigenspaces(matrix);
        Some(match fun.get_ident() {
            Context::DET => scalar(matrix.det().ok()?),
            Context::TRANSPOSE => VectorSpaceElement::Vector(matrix.transpose()),
            Context::TRACE => scalar(matrix.trace().ok()?),
            Context::RANK => {
                scalar(scalars.nth(i64::try_from(<T as MatrixEntries>::rank(matrix)?).ok()?))
            }
            Context::KERNEL => VectorSpaceElement::Vector(<T as MatrixEntries>::kernel(matrix)?),
            Context::CHARPOLY => {
                let x = match args.get(1) {
                    None => Symbol::new("x"),
                    Some(Term::Symbol(x)) => x.symbol,
                    Some(Term::Value(Value {
                        value: VectorSpaceElement::Scalar(x, _),
                        ..
                    })) => <T as MatrixEntries>::as_symbol(x)?,
                    Some(_) => return None,
                };
                scalar(<T as MatrixEntries>::charpoly(matrix, x)?)
            }
            Context::HERMITE => VectorSpaceElement::Vector(<T as MatrixEntries>::hermite(matrix)?),
            Context::SMITH => VectorSpaceElement::Vector(<T as MatrixEntries>::smith(matrix)?),
            Context::EIGENVALUES => {
                let values: Vec<_> = eigenspaces()?
                    .into_iter()
                    .flat_map(|(value, multiplicity, _)| std::iter::repeat_n(value, multiplicity))
                    .collect();
                VectorSpaceElement::Vector(Matrix::new((values.len(), 1), values, scalars))
            }
            Context::EIGENVECTORS => VectorSpaceElement::Vector(
                eigenspaces()?
                    .into_iter()
                    .map(|(_, _, basis)| basis)
                    .reduce(|vectors, basis| vectors.concat_columns(&basis))?,
            ),
            _ => return None,
        })
    }
}

impl<T: Ring> M<T> {
    /// The scalar `term` is, if it is one.
    const fn scalar(term: &Term<Self>) -> Option<&T::Element> {
        match term {
            Term::Value(Value {
                value: VectorSpaceElement::Scalar(x, _),
                ..
            }) => Some(x),
            _ => None,
        }
    }

    /// The symbol `term` is, a symbol of this set or a scalar symbol.
    fn symbol(term: &Term<Self>) -> Option<Symbol> {
        match term {
            Term::Symbol(x) => Some(x.symbol),
            _ => <T as MatrixEntries>::as_symbol(Self::scalar(term)?),
        }
    }

    /// The entries of a scalar (one entry) or of a row or column vector.
    fn vector_entries(term: &Term<Self>) -> Option<Vec<T::Element>> {
        match term {
            Term::Value(Value {
                value: VectorSpaceElement::Scalar(x, _),
                ..
            }) => Some(vec![x.clone()]),
            Term::Value(Value {
                value: VectorSpaceElement::Vector(matrix),
                ..
            }) if matrix.height() == 1 || matrix.width() == 1 => Some(matrix.data.clone()),
            _ => None,
        }
    }

    /// `gradient(f, x_1, ..., x_n)` (a column), `jacobian(F, x_1, ..., x_n)` (one row per function of the row or
    /// column `F`) and `hessian(f, x_1, ..., x_n)`. The variables are symbols or rows or columns of symbols, every
    /// symbol of the functions sorted by name when there are none.
    fn eval_derivatives(&self, ident: Symbol, args: &[Term<Self>]) -> Option<Matrix<T>> {
        let (functions, variables) = args.split_first()?;
        let functions = Self::vector_entries(functions)?;
        if ident != Context::JACOBIAN && functions.len() != 1 {
            return None;
        }
        let mut symbols = vec![];
        for variable in variables {
            match variable {
                Term::Symbol(x) => symbols.push(x.symbol),
                _ => {
                    for x in Self::vector_entries(variable)? {
                        symbols.push(<T as MatrixEntries>::as_symbol(&x)?);
                    }
                }
            }
        }
        if variables.is_empty() {
            let mut all = BTreeSet::new();
            for f in &functions {
                all.extend(<T as MatrixEntries>::symbols(f)?);
            }
            symbols = all
                .into_iter()
                .filter(|x| !Context::is_builtin_constant(*x))
                .collect();
            symbols.sort_by_key(|x| x.name());
        }
        if symbols.is_empty() {
            return None;
        }
        let derivative = <T as MatrixEntries>::derivative;
        let n = symbols.len();
        let (size, data) = match ident {
            Context::GRADIENT => (
                (n, 1),
                symbols
                    .iter()
                    .map(|x| derivative(&functions[0], *x))
                    .collect::<Option<_>>()?,
            ),
            Context::JACOBIAN => (
                (functions.len(), n),
                functions
                    .iter()
                    .flat_map(|f| symbols.iter().map(move |x| derivative(f, *x)))
                    .collect::<Option<_>>()?,
            ),
            Context::HESSIAN => {
                let gradient = symbols
                    .iter()
                    .map(|x| derivative(&functions[0], *x))
                    .collect::<Option<Vec<_>>>()?;
                (
                    (n, n),
                    gradient
                        .iter()
                        .flat_map(|g| symbols.iter().map(move |x| derivative(g, *x)))
                        .collect::<Option<_>>()?,
                )
            }
            _ => return None,
        };
        Some(Matrix::new(size, data, self.scalar_sub_set))
    }
}

/// An eigenvalue of a matrix over `T`, with its algebraic multiplicity and a basis of its eigenspace as columns.
pub type EigenvalueSpace<T> = (<T as Set>::Element, usize, Matrix<T>);

/// Matrix operations depending on the set of the entries.
///
/// They are specialized for the sets where they can be evaluated: normal forms over `{$ZZ$}` and `{$ZZ\/n ZZ$}`, eigenvalues over `{$RR$}`. Every method returns `None` when the
/// operation can't be evaluated.
pub trait MatrixEntries: Ring {
    /// The rank of `matrix`.
    fn rank(matrix: &Matrix<Self>) -> Option<usize>;
    /// A basis of the kernel of `matrix`, see [`Matrix::kernel`].
    fn kernel(matrix: &Matrix<Self>) -> Option<Matrix<Self>>;
    /// The characteristic polynomial of `matrix` in `x`.
    fn charpoly(matrix: &Matrix<Self>, x: Symbol) -> Option<Self::Element>;
    /// The Hermite normal form of `matrix`, see [`Matrix::hermite`].
    fn hermite(matrix: &Matrix<Self>) -> Option<Matrix<Self>>;
    /// The Smith normal form of `matrix`, see [`Matrix::smith`].
    fn smith(matrix: &Matrix<Self>) -> Option<Matrix<Self>>;
    /// The eigenvalues of `matrix`, with their algebraic multiplicity and a basis of their eigenspace.
    fn eigenspaces(matrix: &Matrix<Self>) -> Option<Vec<EigenvalueSpace<Self>>>;
    /// The symbol `element` is, if it is one.
    fn as_symbol(element: &Self::Element) -> Option<Symbol>;
    /// The symbols of `element`.
    fn symbols(element: &Self::Element) -> Option<BTreeSet<Symbol>>;
    /// The derivative of `element` with respect to `x`.
    fn derivative(element: &Self::Element, x: Symbol) -> Option<Self::Element>;
    /// The roots of the polynomial `p` in `x`, repeated by multiplicity.
    fn roots(p: &Self::Element, x: Symbol) -> Option<Vec<Self::Element>>;
    /// The prime factorization of the number `n`, as rows `[p, e]` (see the builtin `factorint`).
    fn factorint(n: &Self::Element) -> Option<Matrix<Self>>;
}

impl<T: Ring> MatrixEntries for T {
    default fn rank(matrix: &Matrix<Self>) -> Option<usize> {
        matrix.rank().ok()
    }
    default fn kernel(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        matrix.kernel().ok()
    }
    default fn charpoly(_: &Matrix<Self>, _: Symbol) -> Option<Self::Element> {
        None
    }
    default fn hermite(_: &Matrix<Self>) -> Option<Matrix<Self>> {
        None
    }
    default fn smith(_: &Matrix<Self>) -> Option<Matrix<Self>> {
        None
    }
    default fn eigenspaces(_: &Matrix<Self>) -> Option<Vec<EigenvalueSpace<Self>>> {
        None
    }
    default fn as_symbol(_: &Self::Element) -> Option<Symbol> {
        None
    }
    default fn symbols(_: &Self::Element) -> Option<BTreeSet<Symbol>> {
        None
    }
    default fn derivative(_: &Self::Element, _: Symbol) -> Option<Self::Element> {
        None
    }
    default fn roots(_: &Self::Element, _: Symbol) -> Option<Vec<Self::Element>> {
        None
    }
    default fn factorint(_: &Self::Element) -> Option<Matrix<Self>> {
        None
    }
}

impl<T: Ring> MatrixEntries for TermSet<T> {
    default fn rank(matrix: &Matrix<Self>) -> Option<usize> {
        matrix.rank().ok()
    }
    default fn kernel(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        matrix.kernel().ok()
    }
    default fn charpoly(matrix: &Matrix<Self>, x: Symbol) -> Option<Self::Element> {
        matrix.charpoly(x).ok().map(|charpoly| charpoly.expand())
    }
    default fn hermite(_: &Matrix<Self>) -> Option<Matrix<Self>> {
        None
    }
    default fn smith(_: &Matrix<Self>) -> Option<Matrix<Self>> {
        None
    }
    default fn eigenspaces(_: &Matrix<Self>) -> Option<Vec<EigenvalueSpace<Self>>> {
        None
    }
    default fn as_symbol(element: &Self::Element) -> Option<Symbol> {
        match element {
            Term::Symbol(symbol) => Some(symbol.symbol),
            _ => None,
        }
    }
    default fn symbols(element: &Self::Element) -> Option<BTreeSet<Symbol>> {
        Some(element.symbols())
    }
    default fn derivative(_: &Self::Element, _: Symbol) -> Option<Self::Element> {
        None
    }
    default fn roots(_: &Self::Element, _: Symbol) -> Option<Vec<Self::Element>> {
        None
    }
    default fn factorint(_: &Self::Element) -> Option<Matrix<Self>> {
        None
    }
}

/// The entries of `matrix`, if they are all values.
fn values<T: Ring>(matrix: &Matrix<TermSet<T>>) -> Option<Matrix<T>> {
    let data = matrix
        .data
        .iter()
        .map(|entry| match entry {
            Term::Value(value) => Some(value.value.clone()),
            _ => None,
        })
        .collect::<Option<_>>()?;
    Some(Matrix::new(
        (matrix.height(), matrix.width()),
        data,
        *matrix.set.get_set(),
    ))
}

/// `matrix` with its entries as constant expressions.
fn constants<T: Ring>(matrix: Matrix<T>) -> Matrix<TermSet<T>> {
    let set = matrix.set;
    Matrix::new(
        (matrix.height(), matrix.width()),
        matrix
            .data
            .into_iter()
            .map(|value| Term::constant(value, set))
            .collect(),
        set.get_term_set(),
    )
}

/// The entries of `matrix` lifted to `{$ZZ$}`, if they are all values.
fn lift(matrix: &Matrix<TermSet<Zn>>) -> Option<Matrix<Z<Integer>>> {
    let values = values(matrix)?;
    Some(Matrix::new(
        (values.height(), values.width()),
        values.data.into_iter().map(Integer::from).collect(),
        Z,
    ))
}

/// The matrix of the rows `[p, e]` given by [`primes::factor_rational`], with entries built by `entry`.
fn factorint_matrix<T: Ring>(
    n: &Rational,
    set: T,
    entry: impl Fn(Integer) -> T::Element,
) -> Option<Matrix<TermSet<T>>> {
    let rows = primes::factor_rational(n)?;
    let data = rows
        .into_iter()
        .flat_map(|(p, e)| [entry(p), entry(Integer::from(e))])
        .map(|value| Term::constant(value, set))
        .collect::<Vec<_>>();
    Some(Matrix::new((data.len() / 2, 2), data, set.get_term_set()))
}

impl MatrixEntries for TermSet<Z<Integer>> {
    fn factorint(n: &Self::Element) -> Option<Matrix<Self>> {
        let Term::Value(n) = n else { return None };
        factorint_matrix(&Rational::from(&n.value), Z, |x| x)
    }
    /// The rank over `{$QQ$}`, the number of pivots of the Hermite normal form.
    fn rank(matrix: &Matrix<Self>) -> Option<usize> {
        Some(values(matrix)?.hermite_decomposition().2)
    }
    /// A basis of the lattice of integer vectors of the kernel: the last rows of `U` in the Hermite
    /// decomposition `{$U A^T = H$}`, whose rows of `H` are zero.
    fn kernel(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        let matrix = values(matrix)?;
        let (transform, _, rank) = matrix.transpose().hermite_decomposition();
        Some(constants(if rank == matrix.width() {
            Matrix::zero((matrix.width(), 1), Z)
        } else {
            transform
                .submatrix(rank..matrix.width(), 0..matrix.width())
                .transpose()
        }))
    }
    fn hermite(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        Some(constants(values(matrix)?.hermite()))
    }
    fn smith(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        Some(constants(values(matrix)?.smith()))
    }
}

impl MatrixEntries for TermSet<Zn> {
    /// The rank, only when the pivots of the row reduction are invertible.
    fn rank(matrix: &Matrix<Self>) -> Option<usize> {
        let mut matrix = values(matrix)?;
        let width = matrix.width();
        matrix.row_reduce_left(width).ok()
    }
    fn kernel(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        Some(constants(values(matrix)?.kernel().ok()?))
    }
    /// The Hermite normal form of the rows of `A` and `{$n I$}` over `{$ZZ$}`, which generate the same module as
    /// `A` modulo `n`, reduced modulo `n` without its zero rows.
    fn hermite(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        let set = *matrix.set.get_set();
        let lifted = lift(matrix)?;
        let width = lifted.width();
        let mut modulus = Matrix::identity(width, Z);
        modulus.external_product(&Integer::from(set.modulus()));
        let mut data = lifted.data;
        data.extend(modulus.data);
        let hermite = Matrix::new((data.len() / width, width), data, Z).hermite();
        let rows: Vec<Vec<u64>> = (0..hermite.height())
            .map(|i| (0..width).map(|j| set.reduce(&hermite[(i, j)])).collect())
            .filter(|row: &Vec<u64>| row.iter().any(|&x| x != 0))
            .collect();
        let height = rows.len().max(1);
        let mut data: Vec<u64> = rows.into_iter().flatten().collect();
        data.resize(height * width, 0);
        Some(constants(Matrix::new((height, width), data, set)))
    }
    /// The Smith normal form over `{$ZZ$}`, whose diagonal entries `d` are replaced by `{$gcd(d, n)$}` (reduced
    /// modulo `n`), the other ones being units modulo `n`.
    fn smith(matrix: &Matrix<Self>) -> Option<Matrix<Self>> {
        let set = *matrix.set.get_set();
        let smith = lift(matrix)?.smith();
        let modulus = Integer::from(set.modulus());
        Some(constants(Matrix::new(
            (smith.height(), smith.width()),
            smith
                .data
                .iter()
                .map(|d| set.reduce(&Z.gcd(d, &modulus)))
                .collect(),
            set,
        )))
    }
}

impl MatrixEntries for TermSet<R<Rational>> {
    fn derivative(element: &Self::Element, x: Symbol) -> Option<Self::Element> {
        Some(element.derivative(x))
    }
    fn roots(p: &Self::Element, x: Symbol) -> Option<Vec<Self::Element>> {
        let p = p.expand();
        // A polynomial of positive degree
        if polynomial_form(&p, x).ok()?.len() < 2 {
            return None;
        }
        let roots: Vec<_> = real_roots(&p, x)?
            .into_iter()
            .flat_map(|(value, multiplicity)| std::iter::repeat_n(value, multiplicity))
            .collect();
        (!roots.is_empty()).then_some(roots)
    }
    fn factorint(n: &Self::Element) -> Option<Matrix<Self>> {
        let Term::Value(n) = n else { return None };
        factorint_matrix(&n.value, R, Rational::from)
    }
    fn eigenspaces(matrix: &Matrix<Self>) -> Option<Vec<EigenvalueSpace<Self>>> {
        Some(
            matrix
                .eigenspaces()?
                .into_iter()
                .map(|space| (space.value, space.multiplicity, space.basis))
                .collect(),
        )
    }
}

impl<T: Ring> Semiring for M<T> {
    fn one(&self) -> Self::Element {
        VectorSpaceElement::Scalar(self.scalar_sub_set.one(), self.scalar_sub_set)
    }

    fn one_like(&self, a: &Self::Element) -> Self::Element {
        match a {
            VectorSpaceElement::Vector(matrix) if matrix.width() == matrix.height() => {
                let mut identity =
                    Matrix::zero((matrix.height(), matrix.width()), self.scalar_sub_set);
                for i in 0..matrix.height() {
                    identity[(i, i)] = self.scalar_sub_set.one();
                }
                VectorSpaceElement::Vector(identity)
            }
            _ => self.one(),
        }
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        self.try_mul(a, b)
            .unwrap_or_else(|| panic!("Can't multiply {a} and {b} !"))
    }

    fn try_mul(&self, a: &Self::Element, b: &Self::Element) -> Option<Self::Element> {
        match (a, b) {
            (VectorSpaceElement::Scalar(a, _), VectorSpaceElement::Scalar(b, _)) => Some(
                VectorSpaceElement::Scalar(self.scalar_sub_set.mul(a, b), self.scalar_sub_set),
            ),
            (VectorSpaceElement::Vector(a), VectorSpaceElement::Vector(b))
                if a.width() == b.height() =>
            {
                Some(VectorSpaceElement::Vector(a * b))
            }
            (VectorSpaceElement::Vector(_), VectorSpaceElement::Vector(_)) => None,
            (VectorSpaceElement::Scalar(a, _), VectorSpaceElement::Vector(b))
            | (VectorSpaceElement::Vector(b), VectorSpaceElement::Scalar(a, _)) => {
                Some(VectorSpaceElement::Vector({
                    let mut b = b.clone();
                    b.external_product(a);
                    b
                }))
            }
        }
    }

    fn normalize(&self, mut a: Term<Self>) -> Term<Self> {
        a = if let Term::Pow(pow) = &a
            && let Term::Value(term::Value {
                value: VectorSpaceElement::Scalar(ref base, _),
                ..
            }) = *pow.base
            && let Term::Value(term::Value {
                value: VectorSpaceElement::Scalar(ref exponant, _),
                ..
            }) = **pow.exponant
        {
            Term::Value(Value::new(VectorSpaceElement::Scalar(self.scalar_sub_set.normalize(Term::Pow(term::Pow::new(
                Term::Value(Value::new(base.clone(), self.scalar_sub_set)),
                Term::Value(Value::new(
                    exponant.clone(),
                    self.scalar_sub_set.get_exponant_set(),
                )),
                self.scalar_sub_set,
            ))).as_value().expect("Normalized expression is not a value and should be converted inside the matrix ring").value,
                self.scalar_sub_set),*self))
        } else {
            a
        };
        if let Term::Fun(fun) = &a
            && let Some(res) = self.eval_builtin(&**fun)
        {
            return self.normalize(Term::Value(Value::new(res, *self)));
        }
        match &a {
            Term::Value(value) => {
                let scalars = self.scalar_sub_set;
                return self.map_entries(&value.value, "Normalized", |x| {
                    // Fractions are simplified, so that `{$A A^(-1) = I$}` for symbolic matrices
                    let x = scalars.normalize(x);
                    match &x {
                        Term::Value(v) if !scalars.is_one(&scalars.as_fraction(&v.value).1) => {
                            scalars.simplify(x)
                        }
                        _ => x,
                    }
                });
            }
            Term::Pow(term::Pow { base, exponant, .. }) => {
                if let (
                    Term::Value(Value {
                        value: VectorSpaceElement::Vector(matrix),
                        ..
                    }),
                    Term::Value(Value {
                        value: exponant, ..
                    }),
                ) = (&**base, &***exponant)
                    && self.get_exponant_set().is_strictly_negative(exponant)
                    && let Ok(inverse) = matrix.inv()
                {
                    return Term::Pow(term::Pow::new(
                        Term::Value(Value::new(VectorSpaceElement::Vector(inverse), *self)),
                        Term::Value(Value::new(
                            self.get_exponant_set().neg(exponant),
                            self.get_exponant_set(),
                        )),
                        *self,
                    ));
                }
                if let (
                    Term::Value(Value {
                        value: VectorSpaceElement::Vector(matrix),
                        ..
                    }),
                    Term::Value(Value {
                        value: exponant, ..
                    }),
                ) = (&**base, &***exponant)
                    && matrix.height() == matrix.width()
                {
                    // Exponentiation by squaring, only evaluating natural powers
                    let exponant_set = self.get_exponant_set();
                    let fits = |power: &_, remaining: &_| {
                        matches!(
                            exponant_set.partial_cmp(power, remaining),
                            Some(Ordering::Less | Ordering::Equal)
                        )
                    };
                    // Powers of two up to the exponant, with the matching powers of the matrix
                    let mut squares = vec![];
                    let (mut power, mut square) = (exponant_set.nth(1), matrix.clone());
                    while fits(&power, exponant) {
                        let next = (exponant_set.add(&power, &power), &square * &square);
                        squares.push((power, square));
                        (power, square) = next;
                    }
                    let mut remaining = exponant.clone();
                    let mut res: Option<Matrix<T>> = None;
                    for (power, square) in squares.into_iter().rev() {
                        if fits(&power, &remaining) {
                            exponant_set.sub_assign(&mut remaining, &power);
                            res = Some(res.map_or(square.clone(), |res| &res * &square));
                        }
                    }
                    if let Some(res) = res
                        && exponant_set.is_zero(&remaining)
                    {
                        return Term::Value(Value::new(VectorSpaceElement::Vector(res), *self));
                    }
                }
            }
            _ => {}
        }
        a
    }

    fn expand(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Value(value) => {
                self.map_entries(&value.value, "Expanded", |x| self.scalar_sub_set.expand(x))
            }
            _ => a,
        }
    }

    fn simplify(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Value(value) => self.map_entries(&value.value, "Simplified", |x| {
                self.scalar_sub_set.simplify(x)
            }),
            _ => a,
        }
    }
}

impl<T: Ring> Ring for M<T> {
    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        match a {
            VectorSpaceElement::Scalar(scalar, _) => self
                .scalar_sub_set
                .try_inv(scalar)
                .map(|elem| VectorSpaceElement::Scalar(elem, self.scalar_sub_set)),
            VectorSpaceElement::Vector(matrix) => matrix.inv().ok().map(VectorSpaceElement::Vector),
        }
    }

    fn as_fraction(&self, a: &Self::Element) -> (Self::Element, Self::Element) {
        let num = match &a {
            VectorSpaceElement::Vector(matrix) => {
                let mut res = matrix.clone();
                res.data.iter_mut().for_each(|x| {
                    *x = self
                            .scalar_sub_set
                            .normalize(Term::Value(Value::new(x.clone(), self.scalar_sub_set)))
                            .as_value()
                            .expect("Unified expression is not a value and should be converted inside the matrix ring")
                            .value;
                });
                VectorSpaceElement::Vector(res)
            }
            VectorSpaceElement::Scalar(_, _) => a.clone(),
        };
        (num, self.one())
    }
}

impl<T: SetParseExpression> SetParseExpression for M<T> {
    type MatrixArgumentSet = Self;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        *self
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        // Builtins returning matrices are functions of this set, not scalars like other functions
        if let TokenKind::Ident(name) = &parser.token.kind
            && Context::returns_matrix(Symbol::new(name.as_str()))
        {
            return Ok(None);
        }
        // The scalar stops before them too, `{$2 I(2)$}` being a scalar times a matrix
        let scalar_of_matrix = std::mem::replace(&mut parser.scalar_of_matrix, true);
        let parsed = self.scalar_sub_set.parse_literal(parser);
        parser.scalar_of_matrix = scalar_of_matrix;
        Ok(parsed?.map(|parsed| VectorSpaceElement::Scalar(parsed, self.scalar_sub_set)))
    }
    fn is_constant(&self, name: &str) -> bool {
        self.scalar_sub_set.is_constant(name)
    }
    fn parse_expression(&self, parser: &mut Parser) -> Result<Option<Term<Self>>, ParserError> {
        match parser.token.kind {
            TokenKind::OpenBracket => {
                parser.next_token();
                let mut lines = vec![];
                let mut size = None;
                loop {
                    parser.expect_token(&TokenKind::OpenBracket)?;

                    let mut line_size = 0;
                    loop {
                        // Entries are whole expressions
                        parser.priority = 0;
                        if let Some(element) = parser.parse_literal(self.scalar_sub_set)? {
                            lines.push(element);
                        } else {
                            return Ok(None);
                        }
                        line_size += 1;

                        if parser.token.kind != TokenKind::Comma {
                            break;
                        }
                        parser.next_token();
                    }
                    if let Some(size) = size {
                        if size != line_size {
                            return Err(ParserError::new(
                                "Matrix dimension aren't coherent !".to_string(),
                            ));
                        }
                    } else {
                        size = Some(line_size);
                    }

                    parser.expect_token(&TokenKind::CloseBracket)?;

                    if parser.token.kind != TokenKind::Comma {
                        break;
                    }
                    parser.next_token();
                }
                parser.expect_token(&TokenKind::CloseBracket)?;
                Ok(Some(Term::Value(Value::new(
                    VectorSpaceElement::Vector(Matrix::new(
                        (lines.len() / size.unwrap(), size.unwrap()),
                        lines,
                        self.scalar_sub_set,
                    )),
                    *self,
                ))))
            }
            _ => Ok(None),
        }
    }
}

/// The matrix field, with real coefficients. See [const@R]
pub const M: M<TermSet<R<Rational>>> = M {
    scalar_sub_set: TermSet::new(R),
};
