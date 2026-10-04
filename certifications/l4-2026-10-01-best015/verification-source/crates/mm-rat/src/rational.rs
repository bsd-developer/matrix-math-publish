//! Canonical exact rationals (spec §5.3, §6.2).

use crate::grammar::{format_natural, parse_integer, parse_natural};
use alloc::format;
use alloc::string::String;
use core::cmp::Ordering;
use core::fmt;
use core::ops::{Add, Div, Mul, Neg, Sub};
use malachite::Rational;
use malachite::base::num::arithmetic::traits::{Abs, Ceiling, Floor, Pow, PowerOf2, Sign};
use malachite::base::num::basic::traits::{One, Zero};
use malachite::{Integer, Natural};
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};

/// An exact rational in lowest terms with a strictly positive denominator.
///
/// `malachite::Rational` already maintains that normal form; this newtype adds
/// the canonical §6.2 text encoding and the direction-aware helpers the checker
/// needs, and keeps the rest of the platform from depending on a specific
/// bignum crate's surface.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rat(Rational);

impl Rat {
    /// The additive identity.
    #[must_use]
    pub fn zero() -> Self {
        Self(Rational::ZERO)
    }

    /// The multiplicative identity.
    #[must_use]
    pub fn one() -> Self {
        Self(Rational::ONE)
    }

    /// Wrap an already-normalized rational.
    #[must_use]
    pub const fn from_rational(value: Rational) -> Self {
        Self(value)
    }

    /// Borrow the underlying rational.
    #[must_use]
    pub const fn as_rational(&self) -> &Rational {
        &self.0
    }

    /// Consume into the underlying rational.
    #[must_use]
    pub fn into_rational(self) -> Rational {
        self.0
    }

    /// Build from a signed numerator and denominator, reducing to lowest terms.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadRationalGrammar`] when the denominator is zero.
    pub fn from_ratio(numerator: Integer, denominator: Integer) -> CoreResult<Self> {
        if denominator == Integer::ZERO {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "a rational denominator must be nonzero",
            )
            .equation("§6.2"));
        }
        Ok(Self(Rational::from_integers(numerator, denominator)))
    }

    /// Build from small signed integers.
    #[must_use]
    pub fn from_signeds(numerator: i64, denominator: i64) -> Self {
        Self(Rational::from_signeds(numerator, denominator))
    }

    /// Build from a signed integer.
    #[must_use]
    pub fn from_integer(value: i64) -> Self {
        Self(Rational::from(value))
    }

    /// Decode the canonical `{"n":…,"d":…}` pair (§6.2).
    ///
    /// The pair must already be in lowest terms with a positive denominator, and
    /// zero must be spelled exactly `{"n":"0","d":"1"}`. A non-reduced or
    /// negatively-signed denominator is rejected rather than normalized, because
    /// normalizing on input would give one value two canonical byte sequences.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadRationalGrammar`] for any violation.
    pub fn decode_canonical(numerator_text: &str, denominator_text: &str) -> CoreResult<Self> {
        let numerator = parse_integer(numerator_text)?;
        let denominator = parse_natural(denominator_text)?;
        if denominator == Natural::ZERO {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "a rational denominator must be strictly positive",
            )
            .equation("§6.2")
            .value(format!("{numerator_text}/{denominator_text}")));
        }
        if numerator == Integer::ZERO && denominator != Natural::ONE {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "zero must be encoded exactly as {\"n\":\"0\",\"d\":\"1\"}",
            )
            .equation("§6.2")
            .value(format!("{numerator_text}/{denominator_text}")));
        }
        let value = Rational::from_integers(numerator, Integer::from(denominator.clone()));
        if value.denominator_ref() != &denominator {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "the numerator and denominator must be coprime",
            )
            .equation("§6.2")
            .value(format!("{numerator_text}/{denominator_text}")));
        }
        Ok(Self(value))
    }

    /// The canonical numerator text, carrying the sign (§6.2).
    #[must_use]
    pub fn numerator_text(&self) -> String {
        let magnitude = format_natural(self.0.numerator_ref());
        if self.0.sign() == Ordering::Less {
            format!("-{magnitude}")
        } else {
            magnitude
        }
    }

    /// The canonical denominator text, always positive (§6.2).
    #[must_use]
    pub fn denominator_text(&self) -> String {
        format_natural(self.0.denominator_ref())
    }

    /// The canonical JSON object form `{"d":"…","n":"…"}` with sorted keys (§6.3).
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        format!(
            "{{\"d\":\"{}\",\"n\":\"{}\"}}",
            self.denominator_text(),
            self.numerator_text()
        )
    }

    /// Whether the value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0 == Rational::ZERO
    }

    /// Whether the value is strictly positive.
    #[must_use]
    pub fn is_positive(&self) -> bool {
        self.0.sign() == Ordering::Greater
    }

    /// Whether the value is strictly negative.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.0.sign() == Ordering::Less
    }

    /// Whether the value is nonnegative.
    #[must_use]
    pub fn is_nonnegative(&self) -> bool {
        !self.is_negative()
    }

    /// The absolute value.
    #[must_use]
    pub fn abs(&self) -> Self {
        Self((&self.0).abs())
    }

    /// Raise to an integer power, including negative exponents.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadRationalGrammar`] when a negative exponent is
    /// applied to zero.
    pub fn pow(&self, exponent: i64) -> CoreResult<Self> {
        if exponent < 0 && self.is_zero() {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "zero has no negative power",
            ));
        }
        Ok(Self((&self.0).pow(exponent)))
    }

    /// The multiplicative inverse.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadRationalGrammar`] for zero.
    pub fn recip(&self) -> CoreResult<Self> {
        if self.is_zero() {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "zero has no reciprocal",
            ));
        }
        Ok(Self(Rational::ONE / &self.0))
    }

    /// Exact division.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadRationalGrammar`] when `divisor` is zero.
    pub fn checked_div(&self, divisor: &Self) -> CoreResult<Self> {
        if divisor.is_zero() {
            return Err(CoreError::new(
                ErrorCode::BadRationalGrammar,
                "division by zero is never evaluated",
            )
            .equation("§7.6"));
        }
        Ok(Self(&self.0 / &divisor.0))
    }

    /// The larger of two values.
    #[must_use]
    pub fn max(self, other: Self) -> Self {
        if self.0 >= other.0 { self } else { other }
    }

    /// The smaller of two values.
    #[must_use]
    pub fn min(self, other: Self) -> Self {
        if self.0 <= other.0 { self } else { other }
    }

    /// The least dyadic rational `k / 2^bits` that is at least this value.
    ///
    /// An exact directed bound can run to hundreds of thousands of digits, which
    /// is useless in a certificate: the identity is the digest, but a consumer
    /// still has to parse the claim and a reader still has to read it. Rounding
    /// **up** keeps the value one the checker accepts; rounding to nearest would
    /// not.
    ///
    /// # Errors
    ///
    /// Propagates construction failures.
    pub fn ceil_dyadic(&self, bits: u32) -> CoreResult<Self> {
        let scale = Natural::power_of_2(u64::from(bits));
        let scaled = self.0.clone() * Rational::from(scale.clone());
        Self::from_ratio(scaled.ceiling(), Integer::from(scale))
    }

    /// The largest `k / 2^bits` at most this value.
    ///
    /// The downward companion of [`Self::ceil_dyadic`]. A lower bound rounded
    /// down is still a lower bound, which is what makes outward rounding of a
    /// directed enclosure sound in one line per operation.
    ///
    /// # Errors
    ///
    /// Propagates construction failures.
    pub fn floor_dyadic(&self, bits: u32) -> CoreResult<Self> {
        let scale = Natural::power_of_2(u64::from(bits));
        let scaled = self.0.clone() * Rational::from(scale.clone());
        Self::from_ratio(scaled.floor(), Integer::from(scale))
    }

    /// A decimal approximation for human-facing output only.
    ///
    /// This is never used by an authoritative check; it exists so reports can
    /// print `omega <= 2.371...` alongside the exact value.
    #[must_use]
    pub fn to_decimal_string(&self, places: usize) -> String {
        let negative = self.is_negative();
        let magnitude = self.abs();
        let scale = Rational::from(10u32).pow(places as u64);
        let scaled = magnitude.0 * scale;
        let integral = scaled.floor();
        let mut digits = format!("{integral}");
        while digits.len() <= places {
            digits.insert(0, '0');
        }
        let split = digits.len() - places;
        let (whole, fraction) = digits.split_at(split);
        let sign = if negative { "-" } else { "" };
        if places == 0 {
            format!("{sign}{whole}")
        } else {
            format!("{sign}{whole}.{fraction}")
        }
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rat {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<Rational> for Rat {
    fn from(value: Rational) -> Self {
        Self(value)
    }
}

impl From<i64> for Rat {
    fn from(value: i64) -> Self {
        Self(Rational::from(value))
    }
}

impl From<u64> for Rat {
    fn from(value: u64) -> Self {
        Self(Rational::from(value))
    }
}

impl From<&Integer> for Rat {
    fn from(value: &Integer) -> Self {
        Self(Rational::from(value))
    }
}

macro_rules! binary_op {
    ($trait:ident, $method:ident, $op:tt) => {
        impl $trait for &Rat {
            type Output = Rat;
            fn $method(self, other: Self) -> Rat {
                Rat(&self.0 $op &other.0)
            }
        }
        impl $trait for Rat {
            type Output = Rat;
            fn $method(self, other: Self) -> Rat {
                Rat(self.0 $op other.0)
            }
        }
    };
}

binary_op!(Add, add, +);
binary_op!(Sub, sub, -);
binary_op!(Mul, mul, *);

impl Div for &Rat {
    type Output = Rat;
    /// Total division that maps division by zero to zero.
    ///
    /// The authoritative checker never calls this: it uses
    /// [`Rat::checked_div`] so that a zero denominator is a structured
    /// rejection rather than a silent value (§7.6).
    fn div(self, other: Self) -> Rat {
        if other.is_zero() {
            Rat::zero()
        } else {
            Rat(&self.0 / &other.0)
        }
    }
}

impl Neg for Rat {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Neg for &Rat {
    type Output = Rat;
    fn neg(self) -> Rat {
        Rat(-&self.0)
    }
}

/// Sum an iterator of rationals exactly.
pub fn sum<'a, I: IntoIterator<Item = &'a Rat>>(values: I) -> Rat {
    let mut total = Rat::zero();
    for value in values {
        total = &total + value;
    }
    total
}
