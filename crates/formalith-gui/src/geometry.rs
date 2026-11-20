//! Geometry of graphs in a view: polylines of curves `y = f(x)`, contours `F(x, y) = 0` and regions
//! `F(x, y) < 0`, independent of the interface.

use std::collections::HashMap;

/// A rectangle of the plane, `[x_min, x_max] × [y_min, y_max]`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct View {
    /// The smallest abscissa.
    pub x_min: f64,
    /// The largest abscissa.
    pub x_max: f64,
    /// The smallest ordinate.
    pub y_min: f64,
    /// The largest ordinate.
    pub y_max: f64,
}

impl View {
    /// The width of the view.
    #[must_use]
    pub fn width(&self) -> f64 {
        self.x_max - self.x_min
    }

    /// The height of the view.
    #[must_use]
    pub fn height(&self) -> f64 {
        self.y_max - self.y_min
    }

    /// The view with `x` and `y` swapped.
    #[must_use]
    pub const fn transposed(&self) -> Self {
        Self {
            x_min: self.y_min,
            x_max: self.y_max,
            y_min: self.x_min,
            y_max: self.x_max,
        }
    }
}

/// A polyline.
pub type Polyline = Vec<[f64; 2]>;

/// Maximum number of bisections of a sampling interval.
const MAX_DEPTH: u32 = 10;

/// Sample `y = f(x)` on the abscissas of `view`, about one point per pixel among `pixels`, refined where the curve
/// bends, and split into polylines at undefined points and at discontinuities like poles.
pub fn sample_function(f: impl Fn(f64) -> f64, view: &View, pixels: usize) -> Vec<Polyline> {
    let pixels = pixels.clamp(16, 4096);
    let step = view.width() / pixels as f64;
    // Errors below a fraction of a pixel are invisible
    let tolerance = view.height() / 2000.;
    let mut sampler = Sampler {
        f: &f,
        tolerance,
        jump: view.height() * 2.,
        clamp: (
            view.y_min - view.height() * 4.,
            view.y_max + view.height() * 4.,
        ),
        lines: vec![],
        current: vec![],
    };
    let mut x0 = view.x_min;
    let mut y0 = f(x0);
    sampler.push(x0, y0);
    for i in 1..=pixels {
        let x1 = view.x_min + i as f64 * step;
        let y1 = f(x1);
        sampler.refine(x0, y0, x1, y1, 0);
        x0 = x1;
        y0 = y1;
    }
    sampler.finish()
}

/// The state of [`sample_function`].
struct Sampler<'a, F: Fn(f64) -> f64> {
    f: &'a F,
    tolerance: f64,
    /// Larger differences of consecutive values are discontinuities, once refined.
    jump: f64,
    /// The range values are clamped to, so huge values are still drawn towards them.
    clamp: (f64, f64),
    lines: Vec<Polyline>,
    current: Polyline,
}

impl<F: Fn(f64) -> f64> Sampler<'_, F> {
    /// Add a point to the current polyline, or end it at an undefined point.
    fn push(&mut self, x: f64, y: f64) {
        if y.is_finite() {
            self.current.push([x, y.clamp(self.clamp.0, self.clamp.1)]);
        } else {
            self.cut();
        }
    }

    /// End the current polyline.
    fn cut(&mut self) {
        if !self.current.is_empty() {
            self.lines.push(std::mem::take(&mut self.current));
        }
    }

    /// Add the points of `(x0, x1]`, `(x0, y0)` being already added.
    fn refine(&mut self, x0: f64, y0: f64, x1: f64, y1: f64, depth: u32) {
        let finite = y0.is_finite() && y1.is_finite();
        let mid = 0.5 * (x0 + x1);
        let y_mid = (self.f)(mid);
        let bends = finite && y_mid.is_finite() && (y_mid - 0.5 * (y0 + y1)).abs() > self.tolerance;
        if depth < MAX_DEPTH {
            // Look for the border of the domain between a defined and an undefined value
            let border = y0.is_finite() != y1.is_finite() && depth < MAX_DEPTH - 4;
            if bends || border || (finite && !y_mid.is_finite()) {
                self.refine(x0, y0, mid, y_mid, depth + 1);
                self.refine(mid, y_mid, x1, y1, depth + 1);
                return;
            }
        } else if bends || (finite && (y1 - y0).abs() > self.jump) {
            // Still bending or jumping on a tiny interval: a pole or a step
            self.cut();
        }
        self.push(x1, y1);
    }

    fn finish(mut self) -> Vec<Polyline> {
        self.cut();
        self.lines.retain(|line| line.len() > 1);
        self.lines
    }
}

/// Values of `F` on a grid of `nx × ny` cells covering `view`, row by row from `y_min`.
pub struct Grid {
    /// The number of cells along `x`.
    pub nx: usize,
    /// The number of cells along `y`.
    pub ny: usize,
    view: View,
    values: Vec<f64>,
}

impl Grid {
    /// Evaluate `f` at the corners of the cells.
    pub fn new(f: impl Fn(f64, f64) -> f64, view: &View, nx: usize, ny: usize) -> Self {
        let mut values = Vec::with_capacity((nx + 1) * (ny + 1));
        for j in 0..=ny {
            let y = view.y_min + view.height() * j as f64 / ny as f64;
            for i in 0..=nx {
                let x = view.x_min + view.width() * i as f64 / nx as f64;
                values.push(f(x, y));
            }
        }
        Self {
            nx,
            ny,
            view: *view,
            values,
        }
    }

    fn value(&self, i: usize, j: usize) -> f64 {
        self.values[j * (self.nx + 1) + i]
    }

    fn point(&self, i: f64, j: f64) -> [f64; 2] {
        [
            self.view.x_min + self.view.width() * i / self.nx as f64,
            self.view.y_min + self.view.height() * j / self.ny as f64,
        ]
    }

    /// The curve `F = 0`, by marching squares, as polylines. `f` checks crossings, to skip sign changes at poles.
    pub fn contour(&self, f: impl Fn(f64, f64) -> f64) -> Vec<Polyline> {
        // Edges are identified by their first corner and direction: 0 along x, 1 along y
        type Edge = (usize, usize, u8);
        let mut crossings: HashMap<Edge, [f64; 2]> = HashMap::new();
        let mut crossing = |edge: Edge| -> Option<[f64; 2]> {
            if let Some(point) = crossings.get(&edge) {
                return Some(*point);
            }
            let (i, j, dir) = edge;
            let (i1, j1) = if dir == 0 { (i + 1, j) } else { (i, j + 1) };
            let (a, b) = (self.value(i, j), self.value(i1, j1));
            if !(a.is_finite() && b.is_finite()) || (a > 0.) == (b > 0.) {
                return None;
            }
            let t = a / (a - b);
            let point = if dir == 0 {
                self.point(i as f64 + t, j as f64)
            } else {
                self.point(i as f64, j as f64 + t)
            };
            // Near a pole, the value at the crossing is large rather than 0
            if f(point[0], point[1]).abs() > a.abs().max(b.abs()) {
                return None;
            }
            crossings.insert(edge, point);
            Some(point)
        };
        let mut segments: Vec<(Edge, Edge)> = vec![];
        for j in 0..self.ny {
            for i in 0..self.nx {
                // Bottom, right, top, left edges of the cell
                let edges = [(i, j, 0), (i + 1, j, 1), (i, j + 1, 0), (i, j, 1)];
                let crossed: Vec<Edge> = edges
                    .into_iter()
                    .filter(|&edge| crossing(edge).is_some())
                    .collect();
                match crossed.as_slice() {
                    [a, b] => segments.push((*a, *b)),
                    [a, b, c, d] => {
                        // A saddle: pair edges by the value at the center
                        let center = self.value(i, j)
                            + self.value(i + 1, j)
                            + self.value(i, j + 1)
                            + self.value(i + 1, j + 1);
                        if (center > 0.) == (self.value(i, j) > 0.) {
                            segments.push((*a, *b));
                            segments.push((*c, *d));
                        } else {
                            segments.push((*a, *d));
                            segments.push((*b, *c));
                        }
                    }
                    _ => {}
                }
            }
        }
        join(&segments, |edge| crossings[edge])
    }

    /// The cells whose center satisfies `holds`, row by row from the top (`y_max`), like an image.
    pub fn mask(&self, f: impl Fn(f64, f64) -> f64, holds: impl Fn(f64) -> bool) -> Vec<bool> {
        let mut mask = Vec::with_capacity(self.nx * self.ny);
        for j in (0..self.ny).rev() {
            for i in 0..self.nx {
                let [x, y] = self.point(i as f64 + 0.5, j as f64 + 0.5);
                mask.push(holds(f(x, y)));
            }
        }
        mask
    }
}

/// Join segments between edges into polylines.
fn join<E: Copy + Eq + std::hash::Hash>(
    segments: &[(E, E)],
    point: impl Fn(&E) -> [f64; 2],
) -> Vec<Polyline> {
    let mut neighbours: HashMap<E, Vec<usize>> = HashMap::new();
    for (k, (a, b)) in segments.iter().enumerate() {
        neighbours.entry(*a).or_default().push(k);
        neighbours.entry(*b).or_default().push(k);
    }
    let mut used = vec![false; segments.len()];
    let mut lines = vec![];
    // Follow the segments from an edge, in one direction
    let walk = |start: E, used: &mut Vec<bool>| {
        let mut chain = vec![start];
        let mut edge = start;
        while let Some(&k) = neighbours[&edge].iter().find(|&&k| !used[k]) {
            used[k] = true;
            let (a, b) = segments[k];
            edge = if a == edge { b } else { a };
            chain.push(edge);
        }
        chain
    };
    for k in 0..segments.len() {
        if used[k] {
            continue;
        }
        used[k] = true;
        let (a, b) = segments[k];
        let mut backward = walk(a, &mut used);
        let forward = walk(b, &mut used);
        backward.reverse();
        backward.extend(forward);
        lines.push(backward.iter().map(&point).collect());
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    const VIEW: View = View {
        x_min: -2.,
        x_max: 2.,
        y_min: -2.,
        y_max: 2.,
    };

    #[test]
    fn test_sample_function() {
        let lines = sample_function(|x| x * x, &VIEW, 100);
        assert_eq!(lines.len(), 1);
        assert!(
            lines[0]
                .iter()
                .all(|[x, y]| (y - x * x).abs() < 1e-9 || *y >= 2. + 16.)
        );
        // `1/x` is split at its pole, `sqrt(x)` starts at 0
        assert_eq!(sample_function(|x| 1. / x, &VIEW, 100).len(), 2);
        let lines = sample_function(f64::sqrt, &VIEW, 100);
        assert_eq!(lines.len(), 1);
        assert!(lines[0][0][0] < 1e-2);
        let view = View {
            x_min: -5.,
            x_max: 5.,
            ..VIEW
        };
        assert_eq!(sample_function(f64::tan, &view, 400).len(), 5);
        assert_eq!(sample_function(f64::floor, &VIEW, 400).len(), 4);
    }

    #[test]
    fn test_contour() {
        let f = |x: f64, y: f64| x * x + y * y - 1.;
        let grid = Grid::new(f, &VIEW, 50, 50);
        let lines = grid.contour(f);
        assert_eq!(lines.len(), 1);
        assert!(lines[0].len() > 50);
        assert!(
            lines[0]
                .iter()
                .all(|[x, y]| (x.hypot(*y) - 1.).abs() < 1e-2)
        );
        // A closed curve ends where it starts
        assert_eq!(lines[0].first(), lines[0].last());
        // No contour at the poles of `y - tan(x)`
        let f = |x: f64, y: f64| y - (3. * x).tan();
        let lines = Grid::new(f, &VIEW, 80, 80).contour(f);
        assert!(
            lines
                .iter()
                .all(|line| line.iter().all(|[x, y]| (y - (3. * x).tan()).abs() < 0.1))
        );
        let mask = grid.mask(|x, y| x * x + y * y - 1., |value| value < 0.);
        let inside = mask.iter().filter(|inside| **inside).count() as f64;
        // Area of the disk over the area of the view
        assert!((inside / 2500. - std::f64::consts::PI / 16.).abs() < 0.01);
    }
}
