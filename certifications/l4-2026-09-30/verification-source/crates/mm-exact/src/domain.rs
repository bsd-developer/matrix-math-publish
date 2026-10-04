//! Appendix A domains: shapes, splits, and support vectors (spec §5.1, A.1, A.2).
//!
//! These are the finite index sets every Track A quantity is indexed by. They are
//! enumerated in the canonical orders §5.1 fixes — shapes and splits
//! lexicographically, support vectors lexicographically, regions numerically —
//! because a certificate's dense arrays are positional and a different order
//! would silently reinterpret every value.

use alloc::vec::Vec;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::level::Level;
use mm_core::region::Coordinate;
use mm_core::shape::Shape;

/// A support vector `L ∈ {0,1,2}^(2^(ℓ-1))` from `C_(ℓ,a)` (A.2).
///
/// `C_(ℓ,a) = { L ∈ {0,1,2}^(2^(ℓ-1)) : Σ_p L_p = a }`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SupportVector(Vec<u8>);

impl SupportVector {
    /// Build from raw entries, rejecting anything outside `{0,1,2}` (A.2).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] for an entry above two.
    pub fn from_entries(entries: Vec<u8>) -> CoreResult<Self> {
        if entries.iter().any(|entry| *entry > 2) {
            return Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                "a support-vector entry must be 0, 1, or 2",
            )
            .equation("A.2"));
        }
        Ok(Self(entries))
    }

    /// The entries, in coordinate order.
    #[must_use]
    pub fn entries(&self) -> &[u8] {
        &self.0
    }

    /// The number of entries equal to one, which A.18 weights by `log2 q`.
    #[must_use]
    pub fn ones(&self) -> usize {
        self.0.iter().filter(|entry| **entry == 1).count()
    }

    /// The length `2^(ℓ-1)`.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the vector is empty, which cannot happen for a supported level.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The reversal `2⃗ - L` used by the zero-shape convention `β^∨` (A4).
    #[must_use]
    pub fn complement(&self) -> Self {
        Self(self.0.iter().map(|entry| 2 - entry).collect())
    }

    /// Concatenation, which A.5's `×` uses to combine two child support vectors.
    #[must_use]
    pub fn concat(&self, other: &Self) -> Self {
        let mut entries = self.0.clone();
        entries.extend_from_slice(&other.0);
        Self(entries)
    }
}

/// Enumerate `C_(ℓ,a)` in lexicographic order (§5.1, A.2).
///
/// # Errors
///
/// Returns [`ErrorCode::UnsupportedInstance`] when `a` exceeds `2 * 2^(ℓ-1)`,
/// which makes the set empty for a reason the caller should see.
pub fn support_vectors(level: Level, total: u16) -> CoreResult<Vec<SupportVector>> {
    let length = usize::from(level.support_len());
    let maximum = 2u32 * length as u32;
    if u32::from(total) > maximum {
        return Err(CoreError::new(
            ErrorCode::UnsupportedInstance,
            "a support-vector total exceeds twice the vector length",
        )
        .equation("A.2")
        .value(alloc_format(total)));
    }
    let mut out = Vec::new();
    let mut current = vec![0u8; length];
    build_support(0, length, total, &mut current, &mut out);
    Ok(out)
}

fn build_support(
    position: usize,
    length: usize,
    remaining: u16,
    current: &mut Vec<u8>,
    out: &mut Vec<SupportVector>,
) {
    if position == length {
        if remaining == 0 {
            out.push(SupportVector(current.clone()));
        }
        return;
    }
    // Lexicographic order: smallest entry first.
    let slots_left = (length - position - 1) as u16;
    for entry in 0u8..=2u8 {
        let entry16 = u16::from(entry);
        if entry16 > remaining {
            break;
        }
        if remaining - entry16 > 2 * slots_left {
            continue;
        }
        current[position] = entry;
        build_support(position + 1, length, remaining - entry16, current, out);
    }
    current[position] = 0;
}

/// The finite domain a maximum-entropy block ranges over (A.3, §7.4).
///
/// For the root this is `S_ℓ*`; for an interior node it is `Split(s_T)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShapeDomain {
    shapes: Vec<Shape>,
}

impl ShapeDomain {
    /// The whole level-`ℓ` shape set `S_ℓ` (A.1).
    #[must_use]
    pub fn full(level: Level) -> Self {
        Self {
            shapes: Shape::enumerate(level),
        }
    }

    /// `Split(s)` for a positive parent shape (A.1).
    ///
    /// # Errors
    ///
    /// Propagates split-enumeration failures.
    pub fn splits(parent: Shape) -> CoreResult<Self> {
        Ok(Self {
            shapes: parent.splits()?,
        })
    }

    /// The shapes, in canonical lexicographic order.
    #[must_use]
    pub fn shapes(&self) -> &[Shape] {
        &self.shapes
    }

    /// The number of shapes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.shapes.len()
    }

    /// Whether the domain is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.shapes.is_empty()
    }

    /// The distinct values a coordinate takes across the domain, ascending.
    ///
    /// These index the `λ_W` vectors of a maximum-entropy block (§7.4).
    #[must_use]
    pub fn coordinate_values(&self, coordinate: Coordinate) -> Vec<u16> {
        let mut values: Vec<u16> = self
            .shapes
            .iter()
            .map(|shape| shape.coord(coordinate))
            .collect();
        values.sort_unstable();
        values.dedup();
        values
    }

    /// The index of `value` within [`Self::coordinate_values`].
    #[must_use]
    pub fn coordinate_index(&self, coordinate: Coordinate, value: u16) -> Option<usize> {
        self.coordinate_values(coordinate)
            .iter()
            .position(|candidate| *candidate == value)
    }
}

fn alloc_format(value: u16) -> alloc::string::String {
    alloc::format!("{value}")
}

extern crate alloc;

/// A.2 membership tests, shared by the general and symmetric evaluators.
///
/// `0007_spec.md` §5.1 states the symmetric check as an *equality* with the
/// general one, not an implication. An acceptance rule that only one path
/// applies breaks that equality in the direction that matters: the symmetric
/// path would accept data the general path rejects, which is the failure §8
/// names as the thing the encoding's trust argument exists to exclude. So these
/// are one implementation called twice, rather than two implementations that
/// agree today.
///
/// The functions take slices and return undecorated errors. A location is the
/// caller's to supply, because the two paths do not share one: the general
/// evaluator names a `NodePath`, while a group at `ℓ*=4` covers up to 145,800
/// node positions and naming any single one of them would be arbitrary (§3.3).
pub mod a2 {
    use super::{CoreError, CoreResult, ErrorCode, Vec};
    use mm_rat::rational::Rat;

    /// The six region weights `A_T` of a branching node (A.2).
    ///
    /// # Errors
    ///
    /// [`ErrorCode::CountMismatch`] unless there are exactly six, and
    /// [`ErrorCode::BadSimplex`] unless they form a distribution.
    pub fn region_weights(weights: &[Rat]) -> CoreResult<()> {
        if weights.len() != 6 {
            return Err(
                CoreError::new(ErrorCode::CountMismatch, "A_T must have six entries")
                    .equation("A.2")
                    .value(format!("{} supplied", weights.len())),
            );
        }
        mm_rat::entropy::validate_simplex(weights)
    }

    /// A distribution over a domain of known size (A.2).
    ///
    /// # Errors
    ///
    /// [`ErrorCode::CountMismatch`] on a length disagreement, and
    /// [`ErrorCode::BadSimplex`] when the entries are not a distribution.
    pub fn distribution(values: &[Rat], expected: usize, what: &str) -> CoreResult<()> {
        if values.len() != expected {
            return Err(CoreError::new(ErrorCode::CountMismatch, what)
                .equation("A.2")
                .value(format!("{} supplied, {expected} required", values.len())));
        }
        mm_rat::entropy::validate_simplex(values)
    }

    /// The level-2 free variable `μ`, whose A.2 domain is the closed `[0, 1/2]`.
    ///
    /// # Errors
    ///
    /// [`ErrorCode::BadSimplex`] outside the interval.
    pub fn level_two_mu(mu: &Rat) -> CoreResult<()> {
        if mu.is_negative() || *mu > Rat::from_signeds(1, 2) {
            return Err(
                CoreError::new(ErrorCode::BadSimplex, "a level-2 mu must lie in [0, 1/2]")
                    .equation("A.2")
                    .value(format!("{mu}")),
            );
        }
        Ok(())
    }

    /// Every distribution of a branching group, given its split-domain size.
    ///
    /// # Errors
    ///
    /// Propagates [`region_weights`] and [`distribution`].
    pub fn branching(weights: &[Rat], alpha: &[Rat], splits: usize) -> CoreResult<()> {
        region_weights(weights)?;
        distribution(alpha, splits, "alpha must cover its split domain")
    }

    /// Assert nothing is left unvalidated when a payload kind is added.
    #[must_use]
    pub fn kinds() -> Vec<&'static str> {
        Vec::from(["branching", "zero_shape", "level_two"])
    }
}
