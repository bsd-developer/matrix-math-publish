//! Level shapes, canonical shape ordering, and splits (spec §5.1, §5.3, A.1).

use crate::codes::ErrorCode;
use crate::error::{CoreError, CoreResult, overflow};
use crate::level::Level;
use crate::region::Coordinate;
use alloc::format;
use alloc::vec::Vec;
use core::fmt;

/// A validated level-`ℓ` shape `(x,y,z)` with `x+y+z = 2^ℓ` (A.1).
///
/// The invariant is established once, here, so downstream code never re-checks
/// the sum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Shape {
    level: Level,
    x: u16,
    y: u16,
    z: u16,
}

impl Shape {
    /// Construct a shape, verifying `x+y+z = 2^ℓ` with checked arithmetic (§5.3).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ArithmeticOverflow`] if the coordinate sum overflows
    /// `u16`, and [`ErrorCode::UnsupportedInstance`] if the sum is not `2^ℓ`.
    pub fn new(level: Level, x: u16, y: u16, z: u16) -> CoreResult<Self> {
        let partial = x.checked_add(y).ok_or_else(|| overflow("Shape::new"))?;
        let sum = partial
            .checked_add(z)
            .ok_or_else(|| overflow("Shape::new"))?;
        let expected = level.shape_sum();
        if sum != expected {
            return Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                format!("a level-{level} shape must sum to {expected}"),
            )
            .equation("A.1")
            .value(format!("({x},{y},{z})")));
        }
        Ok(Self { level, x, y, z })
    }

    /// The shape's level.
    #[must_use]
    pub const fn level(self) -> Level {
        self.level
    }

    /// The coordinate triple in canonical `X,Y,Z` order.
    #[must_use]
    pub const fn coords(self) -> [u16; 3] {
        [self.x, self.y, self.z]
    }

    /// One coordinate of the shape.
    #[must_use]
    pub const fn coord(self, coordinate: Coordinate) -> u16 {
        match coordinate {
            Coordinate::X => self.x,
            Coordinate::Y => self.y,
            Coordinate::Z => self.z,
        }
    }

    /// Whether all three coordinates are positive (A.1).
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.x > 0 && self.y > 0 && self.z > 0
    }

    /// Whether at least one coordinate is zero (A.1 "zero-shape").
    #[must_use]
    pub const fn is_zero_shape(self) -> bool {
        !self.is_positive()
    }

    /// The first zero coordinate in `X < Y < Z` order, if any (A.5 `W0`).
    #[must_use]
    pub fn first_zero_coord(self) -> Option<Coordinate> {
        Coordinate::ALL
            .into_iter()
            .find(|&coordinate| self.coord(coordinate) == 0)
    }

    /// The first nonzero coordinate in `X < Y < Z` order, if any (A.5 `W1`).
    #[must_use]
    pub fn first_nonzero_coord(self) -> Option<Coordinate> {
        Coordinate::ALL
            .into_iter()
            .find(|&coordinate| self.coord(coordinate) > 0)
    }

    /// Enumerate `S_ℓ` in canonical lexicographic `(x,y,z)` order (§5.1, A.1).
    ///
    /// `z` is determined by `x` and `y`, so the enumeration is a double loop and
    /// is already sorted: `x` ascending, then `y` ascending.
    #[must_use]
    pub fn enumerate(level: Level) -> Vec<Self> {
        let total = level.shape_sum();
        let mut out = Vec::new();
        for x in 0..=total {
            for y in 0..=(total - x) {
                let z = total - x - y;
                out.push(Self { level, x, y, z });
            }
        }
        out
    }

    /// The number of shapes in `S_ℓ`, namely `C(2^ℓ+2, 2)`.
    #[must_use]
    pub const fn count(level: Level) -> usize {
        let n = level.shape_sum() as usize;
        (n + 1) * (n + 2) / 2
    }

    /// Enumerate `Split(s)` in canonical lexicographic order (A.1).
    ///
    /// `Split(s) = { u ∈ S_(ℓ-1) : 0 ≤ u_W ≤ s_W for W ∈ {X,Y,Z} }`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] when this shape has no child level.
    pub fn splits(self) -> CoreResult<Vec<Self>> {
        let child_level = self.level.child()?;
        let target = child_level.shape_sum();
        let mut out = Vec::new();
        for x in 0..=self.x.min(target) {
            let remaining = target - x;
            let y_min = remaining.saturating_sub(self.z);
            for y in y_min..=remaining.min(self.y) {
                let z = remaining - y;
                if z <= self.z {
                    out.push(Self {
                        level: child_level,
                        x,
                        y,
                        z,
                    });
                }
            }
        }
        Ok(out)
    }

    /// The complementary split `s_T - u` (A.3, A.5).
    ///
    /// The parent shape and `u` determine it, so a decoder recomputes rather
    /// than trusting redundant certificate data (§5.2).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] when `u` is not a valid split of `self`.
    pub fn complement(self, split: Self) -> CoreResult<Self> {
        let child_level = self.level.child()?;
        if split.level != child_level {
            return Err(CoreError::new(
                ErrorCode::BadPath,
                "a split must live one level below its parent",
            )
            .equation("A.1"));
        }
        if split.x > self.x || split.y > self.y || split.z > self.z {
            return Err(CoreError::new(
                ErrorCode::BadPath,
                "a split must be coordinatewise below its parent shape",
            )
            .equation("A.1")
            .value(format!("{split} vs {self}")));
        }
        // Both shapes sum to their level totals and `2^ℓ - 2^(ℓ-1) = 2^(ℓ-1)`,
        // so the difference is again a valid child-level shape.
        Self::new(
            child_level,
            self.x - split.x,
            self.y - split.y,
            self.z - split.z,
        )
    }

    /// Canonical lexicographic comparison by `(x,y,z)` within a fixed level (§5.1).
    #[must_use]
    pub fn canonical_key(self) -> (u16, u16, u16) {
        (self.x, self.y, self.z)
    }
}

impl PartialOrd for Shape {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Shape {
    /// Orders by level first, then lexicographically by `(x,y,z)` (§5.1).
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.level
            .cmp(&other.level)
            .then_with(|| self.canonical_key().cmp(&other.canonical_key()))
    }
}

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({},{},{})", self.x, self.y, self.z)
    }
}
