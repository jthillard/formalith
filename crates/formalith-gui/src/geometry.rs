//! Geometry of the plane, independent of the interface: graphs sampled in `f64` into polylines, refined to a
//! fraction of a pixel and cut at undefined values and discontinuities.

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

    /// The view grown by `factor` times its width on the left and on the right, and its height above and below.
    #[must_use]
    pub fn grown(&self, factor: f64) -> Self {
        Self {
            x_min: self.x_min - factor * self.width(),
            x_max: self.x_max + factor * self.width(),
            y_min: self.y_min - factor * self.height(),
            y_max: self.y_max + factor * self.height(),
        }
    }

    /// Whether `other` is inside the view.
    #[must_use]
    pub fn contains(&self, other: &Self) -> bool {
        self.x_min <= other.x_min
            && other.x_max <= self.x_max
            && self.y_min <= other.y_min
            && other.y_max <= self.y_max
    }

    /// Whether the bounding box of `points` meets the view.
    fn meets(&self, points: &[[f64; 2]]) -> bool {
        let (mut low, mut high) = ([f64::INFINITY; 2], [f64::NEG_INFINITY; 2]);
        for point in points {
            for i in 0..2 {
                low[i] = low[i].min(point[i]);
                high[i] = high[i].max(point[i]);
            }
        }
        low[0] <= self.x_max
            && high[0] >= self.x_min
            && low[1] <= self.y_max
            && high[1] >= self.y_min
    }
}

/// A polyline.
pub type Polyline = Vec<[f64; 2]>;

/// Bisections refining a sampling interval of a curve where it bends: down to 1/16 of a pixel.
const BEND_DEPTH: u32 = 4;

/// Bisections looking for the border of the domain or following a jump.
const BISECTIONS: u32 = 60;

/// The largest number of samples of a curve or a path before refinement.
const MAX_SAMPLES: usize = 1 << 15;

/// Sample `y = f(x)` over the abscissas of `window`, a pixel being `pixel` units along x and y: one sample per pixel,
/// refined where the curve bends, split into polylines at undefined values (drawn up to the border of the domain)
/// and at discontinuities (steep segments whose jump doesn't shrink under bisection: poles and steps, drawn up to
/// what is left of the jump on both sides). Values are clamped to `window` grown by its height above and below, so
/// huge values still go towards the edges.
pub fn sample_function(f: impl Fn(f64) -> f64, window: &View, pixel: [f64; 2]) -> Vec<Polyline> {
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let samples = ((window.width() / pixel[0]).ceil() as usize).clamp(16, MAX_SAMPLES);
    let step = window.width() / samples as f64;
    let mut sampler = Sampler {
        f: &f,
        tolerance: pixel[1] / 4.,
        pixel: pixel[1],
        scale: pixel,
        clamp: (
            window.y_min - window.height(),
            window.y_max + window.height(),
        ),
        lines: vec![],
        current: vec![],
    };
    let mut x0 = window.x_min;
    let mut y0 = f(x0);
    sampler.push(x0, y0);
    for i in 1..=samples {
        let x1 = (i as f64).mul_add(step, window.x_min);
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
    /// Distances from the chord under which the curve is straight.
    tolerance: f64,
    /// The height of a pixel.
    pixel: f64,
    /// The size of a pixel.
    scale: [f64; 2],
    /// The range values are clamped to.
    clamp: (f64, f64),
    lines: Vec<Polyline>,
    current: Polyline,
}

impl<F: Fn(f64) -> f64> Sampler<'_, F> {
    /// Add a point to the current polyline, or end it at an undefined point.
    fn push(&mut self, x: f64, y: f64) {
        if y.is_finite() {
            let point = [x, y.clamp(self.clamp.0, self.clamp.1)];
            if self.current.last() != Some(&point) {
                self.current.push(point);
            }
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
        let (d0, d1) = (y0.is_finite(), y1.is_finite());
        if depth < BEND_DEPTH && d0 == d1 {
            let mid = 0.5 * (x0 + x1);
            let y_mid = (self.f)(mid);
            // Where the curve bends or has a hole, or a piece of the domain between undefined values
            let split = if d0 {
                !y_mid.is_finite() || (y_mid - 0.5 * (y0 + y1)).abs() > self.tolerance
            } else {
                y_mid.is_finite()
            };
            if split {
                self.refine(x0, y0, mid, y_mid, depth + 1);
                self.refine(mid, y_mid, x1, y1, depth + 1);
                return;
            }
        }
        match (d0, d1) {
            (true, true) => {
                if (y1 - y0).abs() > 2. * self.pixel {
                    self.jump(x0, y0, x1, y1);
                }
                self.push(x1, y1);
            }
            (true, false) => {
                let (x, y) = self.border(x0, y0, x1);
                self.push(x, y);
                self.cut();
            }
            (false, true) => {
                let (x, y) = self.border(x1, y1, x0);
                self.push(x, y);
                self.push(x1, y1);
            }
            (false, false) => {}
        }
    }

    /// The last defined point from `(defined, value)` towards the undefined abscissa `undefined`.
    fn border(&self, mut defined: f64, mut value: f64, mut undefined: f64) -> (f64, f64) {
        for _ in 0..BISECTIONS {
            let mid = 0.5 * (defined + undefined);
            if mid == defined || mid == undefined {
                break;
            }
            let y = (self.f)(mid);
            if y.is_finite() {
                defined = mid;
                value = y;
            } else {
                undefined = mid;
            }
        }
        (defined, value)
    }

    /// A steep segment from `(x0, y0)` to `(x1, y1)`: continuous if the jump shrinks when following it, else a pole
    /// or a step, where the polyline is cut, up to what is left of the jump on both sides (to the edge of the view
    /// at a pole, to both levels at a step). `(x1, y1)` is added after it.
    fn jump(&mut self, x0: f64, y0: f64, x1: f64, y1: f64) {
        let (low, high) = self.clamp;
        let jump = (y1 - y0).abs();
        let (mut lo, mut v_lo, mut hi, mut v_hi) = (x0, y0, x1, y1);
        for _ in 0..BISECTIONS {
            if (v_lo > high && v_hi > high) || (v_lo < low && v_hi < low) {
                // Along the edge, where it doesn't matter
                return;
            }
            // Nothing more to see once the rest of the jump is under a pixel
            if (v_hi - v_lo).abs() < self.pixel {
                break;
            }
            let mid = 0.5 * (lo + hi);
            if mid == lo || mid == hi {
                break;
            }
            let v_mid = (self.f)(mid);
            if !v_mid.is_finite() {
                break;
            }
            if (v_mid - v_lo).abs() > (v_hi - v_mid).abs() {
                hi = mid;
                v_hi = v_mid;
            } else {
                lo = mid;
                v_lo = v_mid;
            }
        }
        let rest = (v_hi - v_lo).abs();
        // Following a continuous curve, the rest goes under a pixel
        if !rest.is_finite() || (rest >= self.pixel && rest > 0.25 * jump) {
            self.push(lo, v_lo);
            self.cut();
            self.push(hi, v_hi);
        }
    }

    fn finish(mut self) -> Vec<Polyline> {
        self.cut();
        self.lines.retain(|line| line.len() > 1);
        self.lines
            .into_iter()
            .map(|line| simplify(line, self.scale))
            .collect()
    }
}

/// Bisections refining a segment of a path where it bends.
const PATH_DEPTH: u32 = 8;

/// Sample the path `f(t)` for `t` from `t0` to `t1` on `segments` segments, refined where it bends inside `window`, a
/// pixel being `pixel` units along x and y. It is cut at undefined points and at poles and jumps (long segments whose
/// length doesn't shrink under bisection, like in [`sample_function`]), and clipped to `window`.
pub fn sample_path(
    f: impl Fn(f64) -> [f64; 2],
    t0: f64,
    t1: f64,
    segments: usize,
    window: &View,
    pixel: [f64; 2],
) -> Vec<Polyline> {
    let segments = segments.clamp(1, MAX_SAMPLES);
    let step = (t1 - t0) / segments as f64;
    let mut sampler = PathSampler {
        f: &f,
        window,
        pixel,
        lines: vec![],
        current: vec![],
    };
    let mut s0 = t0;
    let mut p0 = f(s0);
    sampler.push(p0);
    for i in 1..=segments {
        let s1 = (i as f64).mul_add(step, t0);
        let p1 = f(s1);
        sampler.refine(s0, p0, s1, p1, 0);
        s0 = s1;
        p0 = p1;
    }
    sampler.cut();
    let lines = sampler
        .lines
        .into_iter()
        .map(|line| simplify(line, pixel))
        .collect();
    clip(lines, window)
}

/// The state of [`sample_path`].
struct PathSampler<'a, F: Fn(f64) -> [f64; 2]> {
    f: &'a F,
    window: &'a View,
    pixel: [f64; 2],
    lines: Vec<Polyline>,
    current: Polyline,
}

impl<F: Fn(f64) -> [f64; 2]> PathSampler<'_, F> {
    /// Add a point to the current polyline, or end it at an undefined point.
    fn push(&mut self, point: [f64; 2]) {
        if finite(point) {
            self.current.push(point);
        } else {
            self.cut();
        }
    }

    /// End the current polyline.
    fn cut(&mut self) {
        if self.current.len() > 1 {
            self.lines.push(std::mem::take(&mut self.current));
        } else {
            self.current.clear();
        }
    }

    /// Add the points of `(t0, t1]`, `p0 = f(t0)` being already added.
    fn refine(&mut self, t0: f64, p0: [f64; 2], t1: f64, p1: [f64; 2], depth: u32) {
        if !(finite(p0) && finite(p1)) {
            self.cut();
            self.push(p1);
            return;
        }
        let mid = 0.5 * (t0 + t1);
        let p_mid = (self.f)(mid);
        // In pixels
        let scaled = |p: [f64; 2]| [p[0] / self.pixel[0], p[1] / self.pixel[1]];
        let (a, b, m) = (scaled(p0), scaled(p1), scaled(p_mid));
        let chord = self.distance(p0, p1);
        let deviation = if finite(p_mid) {
            segment_distance(m, a, b)
        } else {
            f64::INFINITY
        };
        // Bends outside of the window are invisible
        let visible = !finite(p_mid) || self.window.meets(&[p0, p1, p_mid]);
        if depth < PATH_DEPTH && deviation > 0.25 && visible {
            self.refine(t0, p0, mid, p_mid, depth + 1);
            self.refine(mid, p_mid, t1, p1, depth + 1);
            return;
        }
        if visible && chord > 2. {
            self.jump(t0, p0, t1, p1, chord);
        }
        self.push(p1);
    }

    /// The distance in pixels between `a` and `b`.
    fn distance(&self, a: [f64; 2], b: [f64; 2]) -> f64 {
        ((b[0] - a[0]) / self.pixel[0]).hypot((b[1] - a[1]) / self.pixel[1])
    }

    /// A long segment from `p0 = f(t0)` to `p1 = f(t1)`, `chord` pixels long: continuous if its length shrinks when
    /// following the longer half, else a pole or a jump, where the polyline is cut, up to what is left on both
    /// sides. `p1` is added after it.
    fn jump(&mut self, t0: f64, p0: [f64; 2], t1: f64, p1: [f64; 2], chord: f64) {
        let (mut lo, mut p_lo, mut hi, mut p_hi) = (t0, p0, t1, p1);
        for _ in 0..BISECTIONS {
            if !self.window.meets(&[p_lo, p_hi]) {
                // Out of the window, where it doesn't matter
                return;
            }
            // Nothing more to see once the rest is under a pixel
            if self.distance(p_lo, p_hi) < 1. {
                break;
            }
            let mid = 0.5 * (lo + hi);
            if mid == lo || mid == hi {
                break;
            }
            let p_mid = (self.f)(mid);
            if !finite(p_mid) {
                break;
            }
            if self.distance(p_lo, p_mid) > self.distance(p_mid, p_hi) {
                hi = mid;
                p_hi = p_mid;
            } else {
                lo = mid;
                p_lo = p_mid;
            }
        }
        let rest = self.distance(p_lo, p_hi);
        if !rest.is_finite() || (rest >= 1. && rest > 0.25 * chord) {
            self.push(p_lo);
            self.cut();
            self.push(p_hi);
        }
    }
}

/// Whether both coordinates of `p` are finite.
const fn finite(p: [f64; 2]) -> bool {
    p[0].is_finite() && p[1].is_finite()
}

/// The distance from `p` to the segment `[a, b]`.
fn segment_distance(p: [f64; 2], a: [f64; 2], b: [f64; 2]) -> f64 {
    let ab = [b[0] - a[0], b[1] - a[1]];
    let len2 = ab[0].mul_add(ab[0], ab[1] * ab[1]);
    let t = if len2 > 0. {
        (((p[0] - a[0]) * ab[0] + (p[1] - a[1]) * ab[1]) / len2).clamp(0., 1.)
    } else {
        0.
    };
    (p[0] - t.mul_add(ab[0], a[0])).hypot(p[1] - t.mul_add(ab[1], a[1]))
}

/// Distances in pixels from the drawn polyline under which points are dropped by [`simplify`].
const SIMPLIFY_TOLERANCE: f64 = 0.125;

/// `line` without the points closer than [`SIMPLIFY_TOLERANCE`] pixels to the segments joining the points kept
/// (Douglas-Peucker), a pixel being `pixel` units along x and y. Lines are stroked with a constant width only when
/// their segments aren't much shorter than a pixel.
fn simplify(line: Polyline, pixel: [f64; 2]) -> Polyline {
    let n = line.len();
    if n < 3 {
        return line;
    }
    let scaled: Vec<[f64; 2]> = line
        .iter()
        .map(|p| [p[0] / pixel[0], p[1] / pixel[1]])
        .collect();
    let mut keep = vec![false; n];
    keep[0] = true;
    keep[n - 1] = true;
    let mut ranges = vec![(0, n - 1)];
    while let Some((i, j)) = ranges.pop() {
        let (mut farthest, mut index) = (0., i);
        for k in i + 1..j {
            let distance = segment_distance(scaled[k], scaled[i], scaled[j]);
            if distance > farthest {
                farthest = distance;
                index = k;
            }
        }
        if farthest > SIMPLIFY_TOLERANCE {
            keep[index] = true;
            ranges.push((i, index));
            ranges.push((index, j));
        }
    }
    line.into_iter()
        .zip(keep)
        .filter_map(|(point, keep)| keep.then_some(point))
        .collect()
}

/// The parts of `lines` inside `rect`.
fn clip(lines: Vec<Polyline>, rect: &View) -> Vec<Polyline> {
    let mut parts = vec![];
    for line in lines {
        let mut current: Polyline = vec![];
        for segment in line.windows(2) {
            let [a, b] = [segment[0], segment[1]];
            match clip_segment(a, b, rect) {
                Some((s0, s1)) => {
                    // From the closest end, which may be huge
                    let at = |s: f64| {
                        let (from, s) = if s < 0.5 { (a, s) } else { (b, s - 1.) };
                        [
                            s.mul_add(b[0] - a[0], from[0]),
                            s.mul_add(b[1] - a[1], from[1]),
                        ]
                    };
                    // Continues the current part only from its last point
                    if s0 > 0. && !current.is_empty() {
                        parts.push(std::mem::take(&mut current));
                    }
                    if current.is_empty() {
                        current.push(if s0 > 0. { at(s0) } else { a });
                    }
                    current.push(if s1 < 1. { at(s1) } else { b });
                    if s1 < 1. {
                        parts.push(std::mem::take(&mut current));
                    }
                }
                None => {
                    if !current.is_empty() {
                        parts.push(std::mem::take(&mut current));
                    }
                }
            }
        }
        if !current.is_empty() {
            parts.push(current);
        }
    }
    parts.retain(|line| line.len() > 1);
    parts
}

/// The parameters of the ends of the part of the segment `[a, b]` inside `rect`, if any (Liang-Barsky).
fn clip_segment(a: [f64; 2], b: [f64; 2], rect: &View) -> Option<(f64, f64)> {
    let (mut s0, mut s1) = (0_f64, 1_f64);
    let low = [rect.x_min, rect.y_min];
    let high = [rect.x_max, rect.y_max];
    for i in 0..2 {
        let d = b[i] - a[i];
        if d == 0. {
            if a[i] < low[i] || a[i] > high[i] {
                return None;
            }
        } else {
            let (mut e0, mut e1) = ((low[i] - a[i]) / d, (high[i] - a[i]) / d);
            if e0 > e1 {
                std::mem::swap(&mut e0, &mut e1);
            }
            s0 = s0.max(e0);
            s1 = s1.min(e1);
        }
    }
    (s0 < s1).then_some((s0, s1))
}

/// The largest `|k|` of the lines of [`sample_grid`], so `2 K + 1` lines per family.
pub const GRID_K: i32 = 10;

/// The segments of each line of [`sample_grid`] before refinement.
const GRID_SEGMENTS: usize = 1024;

/// The images under `f` of the lines `y = k` and `x = k` for integers `k` from `-K` to `K` (`K` being [`GRID_K`]),
/// a point moving between `-K` and `K` along them, sampled like [`sample_path`].
pub fn sample_grid(
    f: impl Fn(f64, f64) -> [f64; 2],
    window: &View,
    pixel: [f64; 2],
) -> [Vec<Polyline>; 2] {
    let end = f64::from(GRID_K);
    let family = |horizontal: bool| -> Vec<Polyline> {
        (-GRID_K..=GRID_K)
            .flat_map(|k| {
                let k = f64::from(k);
                let image = |t| if horizontal { f(t, k) } else { f(k, t) };
                sample_path(image, -end, end, GRID_SEGMENTS, window, pixel)
            })
            .collect()
    };
    [family(true), family(false)]
}

/// The part of the curve `line` (with increasing abscissas) over `[a, b]` as points `(x, y)` including the ends and
/// the crossings of the axis, the area between it and the axis being drawn between `min(y, 0)` and `max(y, 0)`.
#[must_use]
pub fn area(line: &[[f64; 2]], a: f64, b: f64) -> Polyline {
    let mut points: Polyline = vec![];
    for segment in line.windows(2) {
        let [p, q] = [segment[0], segment[1]];
        if q[0] < a || p[0] > b || q[0] <= p[0] {
            continue;
        }
        let at = |x: f64| [x, (x - p[0]) / (q[0] - p[0]) * (q[1] - p[1]) + p[1]];
        let (start, end) = (
            if p[0] < a { at(a) } else { p },
            if q[0] > b { at(b) } else { q },
        );
        if points.last() != Some(&start) {
            points.push(start);
        }
        if (start[1] < 0. && end[1] > 0.) || (start[1] > 0. && end[1] < 0.) {
            let x = start[0] - start[1] * (end[0] - start[0]) / (end[1] - start[1]);
            points.push([x, 0.]);
        }
        points.push(end);
    }
    points
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

    /// A pixel of [`VIEW`] on 400 pixels.
    const PIXEL: [f64; 2] = [0.01, 0.01];

    #[test]
    fn test_sample_function() {
        let lines = sample_function(|x| x * x, &VIEW, PIXEL);
        assert_eq!(lines.len(), 1);
        assert!(
            lines[0]
                .iter()
                .all(|[x, y]| (y - x * x).abs() < 1e-12 || *y == 2. + 4.)
        );
        // `1/x` is split at its pole, going to the edges on both sides, without a segment through it
        let lines = sample_function(|x| 1. / x, &VIEW, PIXEL);
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0].last().unwrap()[1], -2. - 4.);
        assert_eq!(lines[1][0][1], 2. + 4.);
        // `sqrt(x)` starts at 0
        let lines = sample_function(f64::sqrt, &VIEW, PIXEL);
        assert_eq!(lines.len(), 1);
        assert!(lines[0][0][0].abs() < 1e-12);
        let view = View {
            x_min: -5.,
            x_max: 5.,
            ..VIEW
        };
        assert_eq!(sample_function(f64::tan, &view, PIXEL).len(), 5);
        // Narrow branches still go to the edges near their poles
        let lines = sample_function(|x| (4. * x).tan(), &view, PIXEL);
        assert!(lines.iter().all(|line| {
            line.first().unwrap()[1] == -2. - 4. || line.first().unwrap()[0] == view.x_min
        }));
        // Steps are split, a steep continuous curve isn't
        let lines = sample_function(f64::floor, &VIEW, PIXEL);
        assert_eq!(lines.len(), 4);
        assert!(
            lines
                .iter()
                .all(|line| line.iter().all(|[x, y]| *y == x.floor() || *x == y + 1.))
        );
        assert_eq!(sample_function(|x| 1e4 * x, &VIEW, PIXEL).len(), 1);
        assert_eq!(sample_function(f64::cbrt, &VIEW, PIXEL).len(), 1);
    }

    #[test]
    fn test_precision() {
        // A view 1e-5 wide at 1000, where `f32` has no distinct abscissas between pixels: a few periods
        let view = View {
            x_min: 1000.,
            x_max: 1000.00001,
            y_min: -2.,
            y_max: 2.,
        };
        let pixel = [view.width() / 1000., view.height() / 1000.];
        let f = |x: f64| (1e6 * (x - 1000.)).sin();
        let lines = sample_function(f, &view, pixel);
        assert_eq!(lines.len(), 1);
        assert!(lines[0].len() >= 50);
        assert!(lines[0].iter().all(|[x, y]| *y == f(*x)));
        assert!(lines[0].windows(2).all(|pair| pair[0][0] < pair[1][0]));
        // Every pixel between the points kept is within a fraction of a pixel of the curve
        for pair in lines[0].windows(2) {
            let [p, q] = [pair[0], pair[1]];
            for k in 1..8 {
                let x = p[0] + (q[0] - p[0]) * f64::from(k) / 8.;
                let chord = p[1] + (q[1] - p[1]) * (x - p[0]) / (q[0] - p[0]);
                assert!((chord - f(x)).abs() < 0.5 * pixel[1]);
            }
        }
    }

    #[test]
    fn test_simplify() {
        // Collinear points go, corners stay
        let line = vec![[0., 0.], [1., 1.], [2., 2.], [3., 0.], [4., 0.]];
        assert_eq!(
            simplify(line, [1., 1.]),
            [[0., 0.], [2., 2.], [3., 0.], [4., 0.]]
        );
    }

    #[test]
    fn test_sample_path() {
        // The unit circle, inside the window
        let lines = sample_path(|t| [t.cos(), t.sin()], -10., 10., 1024, &VIEW, PIXEL);
        assert_eq!(lines.len(), 1);
        assert!(
            lines[0]
                .iter()
                .all(|[x, y]| (x.hypot(*y) - 1.).abs() < 1e-12)
        );
        // Clipped to the window
        let lines = sample_path(|t| [t, t * t], -10., 10., 1024, &VIEW, PIXEL);
        assert_eq!(lines.len(), 1);
        assert!(
            lines[0]
                .iter()
                .all(|[x, y]| x.abs() <= 2. && *y <= 2. + 1e-12)
        );
        // Cut at the pole of `1/t`
        let lines = sample_path(|t| [t, 1. / t], -10., 10., 1023, &VIEW, PIXEL);
        assert_eq!(lines.len(), 2);
    }

    #[test]
    fn test_sample_grid() {
        let window = View {
            x_min: -10.,
            x_max: 10.,
            y_min: -6.,
            y_max: 6.,
        };
        let pixel = [0.05, 0.05];
        // The identity: horizontal lines inside the window, then vertical ones
        let [rows, columns] = sample_grid(|x, y| [x, y], &window, pixel);
        assert_eq!((rows.len(), columns.len()), (13, 21));
        // `z^2`: the image of `Im z = 1` is the parabola `x = y^2 / 4 - 1`
        let [rows, _] = sample_grid(|x, y| [x * x - y * y, 2. * x * y], &window, pixel);
        assert!(rows.iter().any(|line| {
            line.iter()
                .all(|[x, y]| (x - (y * y / 4. - 1.)).abs() < 0.02)
                && line.len() > 10
        }));
        // `1/z`: the image of `Im z = 0` is cut at the pole, not joined across the plot
        let [rows, _] = sample_grid(
            |x, y| {
                let norm = x.mul_add(x, y * y);
                [x / norm, -y / norm]
            },
            &window,
            pixel,
        );
        let axis: Vec<&Polyline> = rows
            .iter()
            .filter(|line| line.iter().all(|[_, y]| *y == 0.))
            .collect();
        assert!(axis.len() >= 2);
        assert!(
            axis.iter()
                .all(|line| line.iter().all(|[x, _]| *x <= -0.099 || *x >= 0.099))
        );
    }

    #[test]
    fn test_area() {
        let line = [[-2., 3.], [0., -1.], [2., 3.]];
        let points = area(&line, -1., 3.);
        assert_eq!(
            points,
            [[-1., 1.], [-0.5, 0.], [0., -1.], [0.5, 0.], [2., 3.]]
        );
    }
}
