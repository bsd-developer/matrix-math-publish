//! Checked recursion level (spec §0.2, §5.3, A.1).

use crate::codes::ErrorCode;
use crate::error::{CoreError, CoreResult};
use alloc::format;
use core::fmt;

/// The smallest recursion level version 1 accepts (§0.2).
pub const MIN_LEVEL: u8 = 2;
/// The largest recursion level version 1 accepts (§0.2).
///
/// `ℓ* ≥ 5` is later work and is rejected as unsupported rather than partially
/// interpreted (§0.2).
pub const MAX_LEVEL: u8 = 4;

/// A validated recursion level in `2..=4`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Level(u8);

impl Level {
    /// Construct a level, rejecting anything outside `2..=4`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] outside the supported range.
    pub fn new(value: u8) -> CoreResult<Self> {
        if (MIN_LEVEL..=MAX_LEVEL).contains(&value) {
            Ok(Self(value))
        } else {
            Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                format!("recursion level must be in {MIN_LEVEL}..={MAX_LEVEL}"),
            )
            .equation("§0.2")
            .value(format!("{value}")))
        }
    }

    /// The underlying integer.
    #[must_use]
    pub const fn get(self) -> u8 {
        self.0
    }

    /// `2^ℓ`, the sum a level-`ℓ` shape's coordinates must reach (A.1).
    ///
    /// This is exact for every supported level, and the constructor already
    /// bounds the exponent, so no overflow is reachable.
    #[must_use]
    pub const fn shape_sum(self) -> u16 {
        1u16 << self.0
    }

    /// `2^(ℓ-1)`, the support-vector length used by `C_(ℓ,a)` (A.2).
    #[must_use]
    pub const fn support_len(self) -> u16 {
        1u16 << (self.0 - 1)
    }

    /// The child level `ℓ-1`, when the node has children.
    ///
    /// Positive level-2 nodes and zero-shape nodes are leaves (A.1), so a
    /// level-2 node has no child level.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] when called on a leaf level.
    pub fn child(self) -> CoreResult<Self> {
        if self.0 <= MIN_LEVEL {
            return Err(CoreError::new(
                ErrorCode::BadPath,
                "a level-2 node is a leaf and has no children",
            )
            .equation("A.1"));
        }
        Self::new(self.0 - 1)
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
