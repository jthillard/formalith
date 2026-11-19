//! A small seeded pseudo-random generator (SplitMix64), so that randomized checks reproduce.

/// The seed used when `FORMALITH_SEED` is not set.
pub const DEFAULT_SEED: u64 = 0x5EED_F0E3_A117_0001;

/// The seed of randomized checks: `FORMALITH_SEED` if set, else [`DEFAULT_SEED`].
pub fn seed() -> u64 {
    std::env::var("FORMALITH_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_SEED)
}

/// SplitMix64 pseudo-random generator.
#[derive(Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    /// A generator starting from `seed`.
    pub const fn new(seed: u64) -> Self {
        Self(seed)
    }

    /// A generator for case `case` of a run seeded by `seed`, independent of the other cases.
    pub fn for_case(seed: u64, case: usize) -> Self {
        let mut rng = Self(seed ^ (case as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        rng.next_u64();
        rng
    }

    /// The next 64 random bits.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A uniform integer in `0..n`.
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }

    /// A uniform integer in `lo..=hi`.
    pub fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next_u64() % (hi - lo + 1) as u64) as i64
    }

    /// True with probability `p`.
    pub fn chance(&mut self, p: f64) -> bool {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64 <= p
    }

    /// A non-zero integer in `-n..=n`.
    pub fn nonzero(&mut self, n: i64) -> i64 {
        let v = self.range(1, n);
        if self.chance(0.5) { v } else { -v }
    }

    /// An element of `items`.
    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }

    /// A rational `p/q` in `[lo, hi]` with a prime denominator `q` in `7..=31` not dividing `p`, as `(p, q)`, so
    /// that it avoids the small rationals where removable singularities usually are (and integers in particular).
    pub fn rational_in(&mut self, lo: f64, hi: f64) -> (i64, i64) {
        let q = *self.pick(&[7, 11, 13, 17, 19, 23, 29, 31]);
        let p_lo = (lo * q as f64).ceil() as i64;
        let p_hi = (hi * q as f64).floor() as i64;
        loop {
            let p = self.range(p_lo, p_hi.max(p_lo));
            if p % q != 0 || p_lo >= p_hi {
                return (p, q);
            }
        }
    }
}
