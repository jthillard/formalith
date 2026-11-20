//! Geometry of the plane, independent of the interface.

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
