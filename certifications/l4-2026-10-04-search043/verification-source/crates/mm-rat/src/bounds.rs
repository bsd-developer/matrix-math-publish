//! Directional bound types and their propagation rules (spec §7.1, §7.2).
//!
//! `LowerBound<T>` is a value known to be **at most** the mathematical quantity;
//! `UpperBound<T>` is a value known to be **at least** it. The wrapper types
//! exist so that a sign error in propagation is a compile error rather than an
//! unsound certificate: you cannot add a lower bound to an upper bound, and you
//! cannot multiply by a possibly-negative factor without saying so.

use crate::rational::Rat;
use core::fmt;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};

/// A value known to be less than or equal to the mathematical quantity (§7.1).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LowerBound(Rat);

/// A value known to be greater than or equal to the mathematical quantity (§7.1).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UpperBound(Rat);

impl LowerBound {
    /// Assert that `value` is a valid lower bound for the intended quantity.
    ///
    /// The caller is responsible for the mathematical justification; every use
    /// inside the checker is paired with a Lean declaration named in
    /// `docs/traceability.md`.
    #[must_use]
    pub const fn assert(value: Rat) -> Self {
        Self(value)
    }

    /// An exact value, which bounds itself from below.
    #[must_use]
    pub const fn exact(value: Rat) -> Self {
        Self(value)
    }

    /// The underlying rational.
    #[must_use]
    pub const fn value(&self) -> &Rat {
        &self.0
    }

    /// Consume into the underlying rational.
    #[must_use]
    pub fn into_value(self) -> Rat {
        self.0
    }

    /// Lower bound of a sum is the sum of lower bounds (§7.2).
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self(&self.0 + &other.0)
    }

    /// Lower bound of `min(x, y)` is the minimum of lower bounds (§7.2).
    #[must_use]
    pub fn min(self, other: Self) -> Self {
        Self(self.0.min(other.0))
    }

    /// Lower bound of `a - b` is `lower(a) - upper(b)` (§7.2).
    #[must_use]
    pub fn sub_upper(&self, other: &UpperBound) -> Self {
        Self(&self.0 - &other.0)
    }

    /// Lower bound of `weight * x` for a validated nonnegative `weight` (§7.2).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ReversedLogDirection`] when `weight` is negative,
    /// because the monotonic shortcut is unsound for signed multipliers (§7.2).
    pub fn scale_nonnegative(&self, weight: &Rat) -> CoreResult<Self> {
        require_nonnegative(weight)?;
        Ok(Self(&self.0 * weight))
    }

    /// Lower bound of a product of two nonnegative lower bounds.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ReversedLogDirection`] when either bound is negative.
    pub fn mul_nonnegative(&self, other: &Self) -> CoreResult<Self> {
        require_nonnegative(&self.0)?;
        require_nonnegative(&other.0)?;
        Ok(Self(&self.0 * &other.0))
    }

    /// Sum a sequence of lower bounds (§7.2).
    #[must_use]
    pub fn sum<'a, I: IntoIterator<Item = &'a Self>>(items: I) -> Self {
        let mut total = Self(Rat::zero());
        for item in items {
            total = total.add(item);
        }
        total
    }

    /// Reinterpret as an upper bound. Only valid for an exact value.
    #[must_use]
    pub fn as_exact_upper(&self) -> UpperBound {
        UpperBound(self.0.clone())
    }
}

impl UpperBound {
    /// Assert that `value` is a valid upper bound for the intended quantity.
    #[must_use]
    pub const fn assert(value: Rat) -> Self {
        Self(value)
    }

    /// An exact value, which bounds itself from above.
    #[must_use]
    pub const fn exact(value: Rat) -> Self {
        Self(value)
    }

    /// The underlying rational.
    #[must_use]
    pub const fn value(&self) -> &Rat {
        &self.0
    }

    /// Consume into the underlying rational.
    #[must_use]
    pub fn into_value(self) -> Rat {
        self.0
    }

    /// Upper bound of a sum is the sum of upper bounds (§7.2).
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self(&self.0 + &other.0)
    }

    /// Upper bound of `max(x, y)`.
    #[must_use]
    pub fn max(self, other: Self) -> Self {
        Self(self.0.max(other.0))
    }

    /// Upper bound of `a - b` is `upper(a) - lower(b)` (§7.2).
    #[must_use]
    pub fn sub_lower(&self, other: &LowerBound) -> Self {
        Self(&self.0 - other.value())
    }

    /// Upper bound of a nonnegative weighted term (§7.2).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ReversedLogDirection`] when `weight` is negative.
    pub fn scale_nonnegative(&self, weight: &Rat) -> CoreResult<Self> {
        require_nonnegative(weight)?;
        Ok(Self(&self.0 * weight))
    }

    /// Sum a sequence of upper bounds (§7.2).
    #[must_use]
    pub fn sum<'a, I: IntoIterator<Item = &'a Self>>(items: I) -> Self {
        let mut total = Self(Rat::zero());
        for item in items {
            total = total.add(item);
        }
        total
    }

    /// Reinterpret as a lower bound. Only valid for an exact value.
    #[must_use]
    pub fn as_exact_lower(&self) -> LowerBound {
        LowerBound(self.0.clone())
    }
}

impl fmt::Display for LowerBound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ">={}", self.0)
    }
}

impl fmt::Display for UpperBound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<={}", self.0)
    }
}

/// A validated enclosure `[lo, hi]` with `lo <= hi` (§7.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interval {
    lo: LowerBound,
    hi: UpperBound,
}

impl Interval {
    /// Build an interval, validating `lo <= hi`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ReversedLogDirection`] when `lo > hi`, which always
    /// indicates a direction mistake upstream.
    pub fn new(lo: LowerBound, hi: UpperBound) -> CoreResult<Self> {
        if lo.value() > hi.value() {
            return Err(CoreError::new(
                ErrorCode::ReversedLogDirection,
                "an interval requires lo <= hi",
            )
            .equation("§7.1")
            .value(alloc::format!("[{}, {}]", lo.value(), hi.value())));
        }
        Ok(Self { lo, hi })
    }

    /// The exact-point interval `[value, value]`.
    #[must_use]
    pub fn exact(value: Rat) -> Self {
        Self {
            lo: LowerBound::exact(value.clone()),
            hi: UpperBound::exact(value),
        }
    }

    /// The lower endpoint.
    #[must_use]
    pub const fn lower(&self) -> &LowerBound {
        &self.lo
    }

    /// The upper endpoint.
    #[must_use]
    pub const fn upper(&self) -> &UpperBound {
        &self.hi
    }

    /// The exact width `hi - lo`, used by differential tests (§12.6).
    #[must_use]
    pub fn width(&self) -> Rat {
        self.hi.value() - self.lo.value()
    }

    /// Whether the interval contains `value`.
    #[must_use]
    pub fn contains(&self, value: &Rat) -> bool {
        self.lo.value() <= value && value <= self.hi.value()
    }

    /// Whether this interval lies entirely inside `other`.
    #[must_use]
    pub fn is_within(&self, other: &Self) -> bool {
        other.lo.value() <= self.lo.value() && self.hi.value() <= other.hi.value()
    }

    /// Interval sum.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self {
            lo: self.lo.add(&other.lo),
            hi: self.hi.add(&other.hi),
        }
    }

    /// Interval difference `self - other`.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        Self {
            lo: self.lo.sub_upper(&other.hi),
            hi: self.hi.sub_lower(&other.lo),
        }
    }

    /// Negation, which swaps and negates the endpoints.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self {
            lo: LowerBound::assert(-self.hi.value().clone()),
            hi: UpperBound::assert(-self.lo.value().clone()),
        }
    }

    /// General sign-aware interval multiplication (§14.7 step 1).
    ///
    /// Takes the extremes of the four endpoint products, so it is correct for
    /// intervals straddling zero. The monotonic shortcut in §7.2 is used only
    /// where nonnegativity has been validated.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        let a = self.lo.value() * other.lo.value();
        let b = self.lo.value() * other.hi.value();
        let c = self.hi.value() * other.lo.value();
        let d = self.hi.value() * other.hi.value();
        let lo = a.clone().min(b.clone()).min(c.clone()).min(d.clone());
        let hi = a.max(b).max(c).max(d);
        Self {
            lo: LowerBound::assert(lo),
            hi: UpperBound::assert(hi),
        }
    }

    /// Scale by an exact rational of either sign.
    ///
    /// Routing this through [`Self::mul`] computed four endpoint products of
    /// which two were duplicates — `mul` sees `lo == hi == factor`, so `lo*f`
    /// and `hi*f` were each evaluated twice — and then took a min and a max over
    /// four clones. The sign of the factor already decides the order, so two
    /// products and a sign test give the same interval.
    ///
    /// The endpoints are the same two rationals `mul` would have selected: for a
    /// nonnegative factor `lo·f ≤ hi·f`, for a negative factor the order
    /// reverses, and for zero both products are zero and either branch yields
    /// the exact zero interval. This is the scaling every entropy term performs
    /// (`log.scale(-p)`), so it runs once per nonzero probability.
    #[must_use]
    pub fn scale(&self, factor: &Rat) -> Self {
        let from_lo = self.lo.value() * factor;
        let from_hi = self.hi.value() * factor;
        if factor.is_negative() {
            Self {
                lo: LowerBound::assert(from_hi),
                hi: UpperBound::assert(from_lo),
            }
        } else {
            Self {
                lo: LowerBound::assert(from_lo),
                hi: UpperBound::assert(from_hi),
            }
        }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.lo.value(), self.hi.value())
    }
}

/// Reject a negative value where §7.2 requires a validated nonnegative factor.
fn require_nonnegative(value: &Rat) -> CoreResult<()> {
    if value.is_nonnegative() {
        Ok(())
    } else {
        Err(CoreError::new(
            ErrorCode::ReversedLogDirection,
            "the monotonic bound shortcut requires a validated nonnegative factor",
        )
        .equation("§7.2")
        .value(alloc::format!("{value}")))
    }
}
