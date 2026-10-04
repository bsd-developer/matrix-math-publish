//! Validated prime field moduli (spec §0.2, §6.6).
//!
//! Version 1 primality validation is exact trial division through
//! `floor(sqrt(p))` with checked arithmetic. Probabilistic primality tests are
//! forbidden in certificate acceptance (§6.6), because acceptance must imply the
//! mathematical claim with certainty, not with high probability.

use crate::codes::ErrorCode;
use crate::error::{CoreError, CoreResult};
use alloc::format;
use core::fmt;

/// The largest modulus version 1 accepts, `2^31 - 1` (§0.2).
pub const MAX_MODULUS: u32 = 0x7fff_ffff;

/// A validated prime modulus `p <= 2^31 - 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PrimeModulus(u32);

impl PrimeModulus {
    /// The characteristic-two field used by the Track B baseline search.
    pub const TWO: Self = Self(2);

    /// Construct a modulus, proving primality by exact trial division.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] when `p` exceeds `2^31 - 1`
    /// or is below 2, and [`ErrorCode::CompositeModulus`] when `p` is composite.
    pub fn new(value: u32) -> CoreResult<Self> {
        if value > MAX_MODULUS {
            return Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                format!("a field modulus must not exceed {MAX_MODULUS}"),
            )
            .equation("§0.2")
            .value(format!("{value}")));
        }
        if value < 2 {
            return Err(CoreError::new(
                ErrorCode::CompositeModulus,
                "a field modulus must be at least 2",
            )
            .equation("§6.6")
            .value(format!("{value}")));
        }
        if !is_prime_trial_division(value) {
            return Err(CoreError::new(
                ErrorCode::CompositeModulus,
                "the field modulus is not prime",
            )
            .equation("§6.6")
            .value(format!("{value}")));
        }
        Ok(Self(value))
    }

    /// The underlying integer.
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }

    /// The modulus widened to `u64` for intermediate products.
    #[must_use]
    pub const fn as_u64(self) -> u64 {
        self.0 as u64
    }
}

impl fmt::Display for PrimeModulus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Exact primality by trial division through `floor(sqrt(value))` (§6.6).
///
/// The loop compares `divisor * divisor <= value` in `u64`, so no intermediate
/// product can overflow for `value <= 2^31 - 1`.
#[must_use]
pub fn is_prime_trial_division(value: u32) -> bool {
    if value < 2 {
        return false;
    }
    if value.is_multiple_of(2) {
        return value == 2;
    }
    if value.is_multiple_of(3) {
        return value == 3;
    }
    let target = u64::from(value);
    let mut divisor: u64 = 5;
    while divisor
        .checked_mul(divisor)
        .is_some_and(|square| square <= target)
    {
        if target.is_multiple_of(divisor) {
            return false;
        }
        let next = divisor + 2;
        if target.is_multiple_of(next) {
            return false;
        }
        divisor += 6;
    }
    true
}
