//! The six fixed coordinate regions (spec §5.1).
//!
//! Region numbering is normative. No library permutation order may be
//! substituted implicitly, so the table below is written out literally and
//! covered by a round-trip test rather than generated from a permutation
//! iterator whose order could change.

use crate::codes::ErrorCode;
use crate::error::{CoreError, CoreResult};
use alloc::format;
use core::fmt;

/// A tensor coordinate. Coordinates are ordered `X < Y < Z` (§5.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Coordinate {
    /// The first coordinate.
    X = 0,
    /// The second coordinate.
    Y = 1,
    /// The third coordinate.
    Z = 2,
}

impl Coordinate {
    /// All coordinates in canonical `X < Y < Z` order.
    pub const ALL: [Self; 3] = [Self::X, Self::Y, Self::Z];

    /// The zero-based index of this coordinate.
    #[must_use]
    pub const fn index(self) -> usize {
        self as usize
    }

    /// Construct from a zero-based index.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] for an index above 2.
    pub fn from_index(index: usize) -> CoreResult<Self> {
        match index {
            0 => Ok(Self::X),
            1 => Ok(Self::Y),
            2 => Ok(Self::Z),
            _ => Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                "coordinate index must be 0, 1, or 2",
            )
            .equation("§5.1")),
        }
    }

    /// The single-letter name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::X => "X",
            Self::Y => "Y",
            Self::Z => "Z",
        }
    }
}

/// The normative region table of §5.1: `region -> (π(X), π(Y), π(Z))`.
///
/// Index `r-1` holds region `r`.
const PERMUTATIONS: [[Coordinate; 3]; 6] = [
    [Coordinate::X, Coordinate::Y, Coordinate::Z],
    [Coordinate::X, Coordinate::Z, Coordinate::Y],
    [Coordinate::Y, Coordinate::X, Coordinate::Z],
    [Coordinate::Y, Coordinate::Z, Coordinate::X],
    [Coordinate::Z, Coordinate::X, Coordinate::Y],
    [Coordinate::Z, Coordinate::Y, Coordinate::X],
];

/// A validated region identifier in `1..=6` (§5.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Region(u8);

impl Region {
    /// The identity region, whose permutation is `(X,Y,Z)`.
    pub const IDENTITY: Self = Self(1);

    /// Construct a region, rejecting anything outside `1..=6`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] outside `1..=6`.
    pub fn new(value: u8) -> CoreResult<Self> {
        if (1..=6).contains(&value) {
            Ok(Self(value))
        } else {
            Err(
                CoreError::new(ErrorCode::UnsupportedInstance, "region must be in 1..=6")
                    .equation("§5.1")
                    .value(format!("{value}")),
            )
        }
    }

    /// All six regions in canonical numeric order.
    #[must_use]
    pub fn all() -> [Self; 6] {
        [Self(1), Self(2), Self(3), Self(4), Self(5), Self(6)]
    }

    /// The underlying identifier.
    #[must_use]
    pub const fn get(self) -> u8 {
        self.0
    }

    /// The image `π_r(coordinate)` under this region's permutation (§5.1).
    #[must_use]
    pub fn permute(self, coordinate: Coordinate) -> Coordinate {
        PERMUTATIONS[usize::from(self.0 - 1)][coordinate.index()]
    }

    /// The full permutation image `(π(X), π(Y), π(Z))`.
    #[must_use]
    pub fn permutation(self) -> [Coordinate; 3] {
        PERMUTATIONS[usize::from(self.0 - 1)]
    }

    /// The inverse permutation: the coordinate `c` with `permute(c) == image`.
    #[must_use]
    pub fn unpermute(self, image: Coordinate) -> Coordinate {
        let table = self.permutation();
        // Every permutation is a bijection on three elements, so the search
        // always succeeds; the fallback keeps the function total without a panic.
        for (index, mapped) in table.iter().enumerate() {
            if *mapped == image {
                return Coordinate::from_index(index).unwrap_or(Coordinate::X);
            }
        }
        Coordinate::X
    }
}

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
