//! Track A instance parameters (spec §0.2, A.1).

use core::fmt;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::level::Level;

/// The largest `q` version 1 accepts (§0.2).
pub const MAX_Q: u32 = 65_535;

/// A validated Track A instance: the parameter `q` and the recursion level `ℓ*`
/// (§0.2, A.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OmegaInstance {
    q: u32,
    level: Level,
}

impl OmegaInstance {
    /// Construct an instance, rejecting anything outside §0.2.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] for `q` outside `1..=65535`.
    pub fn new(q: u32, level: Level) -> CoreResult<Self> {
        if !(1..=MAX_Q).contains(&q) {
            return Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                alloc::format!("q must be in 1..={MAX_Q}"),
            )
            .equation("§0.2")
            .value(alloc::format!("{q}")));
        }
        Ok(Self { q, level })
    }

    /// The parameter `q`.
    #[must_use]
    pub const fn q(self) -> u32 {
        self.q
    }

    /// The recursion level `ℓ*`.
    #[must_use]
    pub const fn level(self) -> Level {
        self.level
    }

    /// `2^(ℓ*-1)`, the coefficient of `log2(q+2)` in the A21 constraint.
    #[must_use]
    pub const fn constraint_scale(self) -> u64 {
        1u64 << (self.level.get() - 1)
    }
}

impl fmt::Display for OmegaInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "q={}, l*={}", self.q, self.level)
    }
}

extern crate alloc;
