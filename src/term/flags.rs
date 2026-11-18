//! Trait to set and unset flags on expression.

/// Flag marking a [Term] as already normalized
pub(crate) const NORMALIZED: u8 = 0x1;
/// Flag marking a [Value](crate::term::Value) as a numerical approximation, or the coefficient of a
/// [Mul](crate::term::Mul) as one, printed as a decimal number (see `approx`)
pub(crate) const APPROXIMATE: u8 = 0x2;

/// Utility trait to manage expression's flags
pub trait Flags {
    /// Return the flags of the expression
    fn get_flags(&self) -> u8;
    /// Return a mutable reference to the flags of the expression
    fn get_flags_mut(&mut self) -> &mut u8;
    /// Add a flag to the expression
    fn add_flag(&mut self, flag: u8) {
        *self.get_flags_mut() |= flag;
    }
    /// Remove a flag from the expression
    fn remove_flag(&mut self, flag: u8) {
        *self.get_flags_mut() &= !flag;
    }
    /// If `normalized` is `true`, set the expression as already normalized (see [`crate::term::Normalize::normalize`])
    fn set_normalized(&mut self, normalized: bool) {
        if normalized {
            self.add_flag(NORMALIZED);
        } else {
            self.remove_flag(NORMALIZED);
        }
    }
    /// Return `true` if the expression is a numerical approximation (see `approx`)
    fn is_approximate(&self) -> bool {
        (self.get_flags() & APPROXIMATE) == APPROXIMATE
    }
    /// If `approximate` is `true`, mark the expression as a numerical approximation
    fn set_approximate(&mut self, approximate: bool) {
        if approximate {
            self.add_flag(APPROXIMATE);
        } else {
            self.remove_flag(APPROXIMATE);
        }
    }
    /// Return `true` if the expression needs to be normalized
    fn needs_normalization(&self) -> bool {
        (self.get_flags() & NORMALIZED) != NORMALIZED
    }
}
