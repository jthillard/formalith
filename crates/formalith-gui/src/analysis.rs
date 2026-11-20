//! Remarkable points of curves `y = f(x)` in a range: roots, extrema and intersections.

/// The kind of a remarkable point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `f(x) = 0`.
    Root,
    /// A local minimum.
    Minimum,
    /// A local maximum.
    Maximum,
    /// Two curves meet.
    Intersection,
}

impl Kind {
    /// The name of the kind.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Root => "root",
            Self::Minimum => "minimum",
            Self::Maximum => "maximum",
            Self::Intersection => "intersection",
        }
    }
}

/// A remarkable point.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Point {
    /// Its kind.
    pub kind: Kind,
    /// Its abscissa.
    pub x: f64,
    /// Its ordinate.
    pub y: f64,
}

/// Maximum number of points of each kind, past which they aren't shown (like for `sin(1/x)`).
const MAX_POINTS: usize = 100;

/// The zeros of `f` in `[a, b]` found on `samples` intervals: sign changes refined by bisection, and touching
/// zeros where `|f|` has a local minimum below `epsilon`. Sign changes at poles are dropped.
fn zeros(f: &impl Fn(f64) -> f64, a: f64, b: f64, samples: usize, epsilon: f64) -> Vec<f64> {
    let step = (b - a) / samples as f64;
    let values: Vec<(f64, f64)> = (0..=samples)
        .map(|i| {
            let x = a + i as f64 * step;
            (x, f(x))
        })
        .collect();
    let mut zeros: Vec<f64> = vec![];
    for (k, window) in values.windows(2).enumerate() {
        let [(x0, y0), (x1, y1)] = [window[0], window[1]];
        if !(y0.is_finite() && y1.is_finite()) {
            continue;
        }
        if y0 == 0. {
            zeros.push(x0);
        } else if y0.signum() != y1.signum() && y1 != 0. {
            let root = bisect(f, x0, y0, x1);
            // A pole changes the sign with large values
            if f(root).abs() <= y0.abs().max(y1.abs()) {
                zeros.push(root);
            }
        } else if k > 0 {
            // A local minimum of `|f|` close to 0, like the root of `x^2`
            let (_, y_prev) = values[k - 1];
            if y_prev.is_finite()
                && y0.abs() < y_prev.abs()
                && y0.abs() < y1.abs()
                && y0.abs() < epsilon
            {
                let x = golden_minimum(&|x| f(x).abs(), x0 - step, x1);
                if f(x).abs() < epsilon * 1e-3 {
                    zeros.push(x);
                }
            }
        }
        if zeros.len() > MAX_POINTS {
            return vec![];
        }
    }
    zeros.dedup_by(|a, b| (*a - *b).abs() < step * 1e-3);
    zeros
}

/// A zero of `f` in `[x0, x1]`, where `f` changes its sign, `f(x0) = y0`.
fn bisect(f: &impl Fn(f64) -> f64, mut x0: f64, y0: f64, mut x1: f64) -> f64 {
    for _ in 0..100 {
        let mid = 0.5 * (x0 + x1);
        if mid == x0 || mid == x1 {
            break;
        }
        let y = f(mid);
        if y == 0. {
            return mid;
        }
        if y.signum() == y0.signum() {
            x0 = mid;
        } else {
            x1 = mid;
        }
    }
    0.5 * (x0 + x1)
}

/// The minimum of `f` in `[a, b]`, by golden section search.
fn golden_minimum(f: &impl Fn(f64) -> f64, mut a: f64, mut b: f64) -> f64 {
    let ratio = (5f64.sqrt() - 1.) / 2.;
    let mut c = b - ratio * (b - a);
    let mut d = a + ratio * (b - a);
    for _ in 0..100 {
        if f(c) < f(d) {
            b = d;
        } else {
            a = c;
        }
        c = b - ratio * (b - a);
        d = a + ratio * (b - a);
    }
    0.5 * (a + b)
}

/// The scale of the values of `f` in `[a, b]`, to tell values close to 0.
fn scale(f: &impl Fn(f64) -> f64, a: f64, b: f64, samples: usize) -> f64 {
    let step = (b - a) / samples as f64;
    let max = (0..=samples)
        .map(|i| f(a + i as f64 * step).abs())
        .filter(|y| y.is_finite())
        .fold(0., f64::max);
    if max > 0. { max } else { 1. }
}

/// The roots and extrema of `f` in `[a, b]`, extrema being zeros of `derivative`, or of a finite difference of
/// `f` without it.
pub fn remarkable_points(
    f: &impl Fn(f64) -> f64,
    derivative: Option<&dyn Fn(f64) -> f64>,
    a: f64,
    b: f64,
    samples: usize,
) -> Vec<Point> {
    let epsilon = 1e-3 * scale(f, a, b, samples);
    let mut points: Vec<Point> = zeros(f, a, b, samples, epsilon)
        .into_iter()
        .map(|x| Point {
            kind: Kind::Root,
            x,
            y: 0.,
        })
        .collect();
    let h = (b - a) * 1e-7;
    let difference = |x: f64| (f(x + h) - f(x - h)) / (2. * h);
    let derivative: &dyn Fn(f64) -> f64 = derivative.unwrap_or(&difference);
    let derivative_epsilon = 1e-3 * scale(&derivative, a, b, samples);
    for x in zeros(&derivative, a, b, samples, derivative_epsilon) {
        let y = f(x);
        let (left, right) = (f(x - 1e3 * h), f(x + 1e3 * h));
        if !(y.is_finite() && left.is_finite() && right.is_finite()) {
            continue;
        }
        let kind = if left > y && right > y {
            Kind::Minimum
        } else if left < y && right < y {
            Kind::Maximum
        } else {
            continue;
        };
        points.push(Point { kind, x, y });
    }
    points
}

/// The intersections of the curves of `f` and `g` in `[a, b]`.
pub fn intersections(
    f: &impl Fn(f64) -> f64,
    g: &impl Fn(f64) -> f64,
    a: f64,
    b: f64,
    samples: usize,
) -> Vec<Point> {
    let difference = |x: f64| f(x) - g(x);
    let epsilon = 1e-3 * scale(&difference, a, b, samples);
    zeros(&difference, a, b, samples, epsilon)
        .into_iter()
        .map(|x| Point {
            kind: Kind::Intersection,
            x,
            y: f(x),
        })
        .filter(|point| point.y.is_finite())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn find(points: &[Point], kind: Kind) -> Vec<f64> {
        points
            .iter()
            .filter(|point| point.kind == kind)
            .map(|point| point.x)
            .collect()
    }

    fn assert_close(a: &[f64], b: &[f64]) {
        assert_eq!(a.len(), b.len(), "{a:?} != {b:?}");
        for (a, b) in a.iter().zip(b) {
            assert!((a - b).abs() < 1e-6, "{a:?} != {b:?}");
        }
    }

    #[test]
    fn test_remarkable_points() {
        // `x^3 - x` has roots -1, 0, 1 and extrema at `±1/sqrt(3)`
        let f = |x: f64| x * x * x - x;
        let derivative = |x: f64| 3. * x * x - 1.;
        let e = 1. / 3f64.sqrt();
        for derivative in [Some(&derivative as &dyn Fn(f64) -> f64), None] {
            let points = remarkable_points(&f, derivative, -2., 2.3, 200);
            assert_close(&find(&points, Kind::Root), &[-1., 0., 1.]);
            assert_close(&find(&points, Kind::Maximum), &[-e]);
            assert_close(&find(&points, Kind::Minimum), &[e]);
        }
        // Touching root, and no root at the pole of `1/x`
        let points = remarkable_points(&|x: f64| (x - 0.3).powi(2), None, -2., 2., 200);
        assert_close(&find(&points, Kind::Root), &[0.3]);
        assert_close(&find(&points, Kind::Minimum), &[0.3]);
        let points = remarkable_points(&|x: f64| 1. / x, None, -2., 2.1, 200);
        assert!(points.is_empty(), "{points:?}");
    }

    #[test]
    fn test_intersections() {
        let points = intersections(&|x: f64| x * x, &|x: f64| x + 2., -5., 5.5, 200);
        assert_close(&find(&points, Kind::Intersection), &[-1., 2.]);
        assert!((points[1].y - 4.).abs() < 1e-6);
    }
}
