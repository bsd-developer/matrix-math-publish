//! Proved-shape directed base-two logarithm bounds (spec §7.3).
//!
//! This is the Rust *diagnostic* implementation. The authoritative definitions
//! and their correctness proofs live in `lean/MatrixMath/Numeric/Log2Bounds.lean`
//! (§4.1: independence over DRY). Both implementations follow the same normative
//! construction so that `just test-diff` can compare them per equation (§12.6).
//!
//! Construction, transcribed from §7.3:
//!
//! ```text
//! x = m * 2^e exactly with m in [1,2)
//! z = (m-1)/(m+1)
//! log2(m) = (2/ln 2) * artanh(z)
//! artanh(z) = sum_{k>=0} z^(2k+1)/(2k+1)
//! tail after N retained terms <= z^(2N+1) / ((2N+1)(1-z^2))
//! ln 2 = 2 * artanh(1/3)
//! ```
//!
//! Every series is evaluated in exact rational arithmetic; nothing here uses a
//! floating-point value, and the iteration count is derived from the requested
//! precision rather than supplied by a certificate (§7.3).
//!
//! `docs/specs/0002_spec.md` §3 fixes how a precision becomes a series length:
//! the least `n` whose proved tail is at most `2^-(precision+3)`, capped at
//! [`SERIES_LENGTH_CAP`]. [`series_length`] is that rule; [`artanh_enclosure`]
//! fuses it into the accumulation loop, and `series_length_matches_fused_loop`
//! in `tests/numerics.rs` asserts the two agree.

use crate::bounds::{Interval, LowerBound, UpperBound};
use crate::rational::Rat;
use alloc::format;
use core::sync::atomic::{AtomicU64, Ordering};
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};

/// Directed logarithm evaluations performed since the last reset.
///
/// Diagnostic only. `docs/specs/0004_spec.md` §4.1 makes the count a producer
/// input to the precision rule, so it has to be a real count rather than an
/// estimate from the node count — but it is read, never branched on, and no
/// checker verdict can depend on it.
static EVALUATIONS: AtomicU64 = AtomicU64::new(0);

/// The number of [`log2_enclosure`] calls since [`reset_evaluations`].
#[must_use]
pub fn evaluations() -> u64 {
    EVALUATIONS.load(Ordering::Relaxed)
}

/// Zero the evaluation counter.
pub fn reset_evaluations() {
    EVALUATIONS.store(0, Ordering::Relaxed);
}

/// Charge evaluations an implementation elided but a checker still performs.
///
/// `0004_spec.md` §4.1 requires the reported figure to bound **the Lean checker**
/// as well as this evaluator, and P5 derives the declared precision from it, so a
/// smaller number is not a better number — it is a weaker guarantee. When this
/// crate's caller hoists a value out of a loop that a checker evaluates each time
/// round, the saving is real in wall clock and must not reach the count.
pub fn charge_elided_evaluations(count: u64) {
    EVALUATIONS.fetch_add(count, Ordering::Relaxed);
}

/// The smallest precision the schema accepts, in binary fractional bits (§6.5).
pub const MIN_PRECISION_BITS: u32 = 32;
/// The largest precision the schema accepts, in binary fractional bits (§6.5).
pub const MAX_PRECISION_BITS: u32 = 4_096;
/// The series-length selection cap (`0002_spec.md` §2.3).
///
/// The largest length the supported precision range can demand is 1,290, at
/// `z = 1/3` and `precision = 4096`. Reaching the cap is a failure, not a
/// result: [`series_length`] and [`artanh_enclosure`] return
/// [`ErrorCode::ResourceLimit`] rather than a length that misses the threshold.
pub const SERIES_LENGTH_CAP: u32 = 8_192;

/// A validated target precision in `32..=4096` binary fractional bits (§6.5, §7.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Precision(u32);

impl Precision {
    /// Construct a precision, rejecting anything outside `32..=4096`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::UnsupportedInstance`] outside the accepted range.
    pub fn new(bits: u32) -> CoreResult<Self> {
        if (MIN_PRECISION_BITS..=MAX_PRECISION_BITS).contains(&bits) {
            Ok(Self(bits))
        } else {
            Err(CoreError::new(
                ErrorCode::UnsupportedInstance,
                format!(
                    "log precision must be in {MIN_PRECISION_BITS}..={MAX_PRECISION_BITS} bits"
                ),
            )
            .equation("§6.5")
            .value(format!("{bits}")))
        }
    }

    /// The requested number of binary fractional bits.
    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    /// The target enclosure width `2^-precision` of one composed `log2`
    /// evaluation (§7.3).
    ///
    /// # Errors
    ///
    /// Propagates a power failure, which the range check makes unreachable.
    pub fn tolerance(self) -> CoreResult<Rat> {
        Rat::from_integer(2).pow(-i64::from(self.0))
    }

    /// The per-series selection threshold `2^-(precision+3)`
    /// (`0002_spec.md` L2).
    ///
    /// The three spare bits are the composition one `log2` evaluation performs
    /// around its two series: a doubling, a reciprocal, and a product.
    ///
    /// # Errors
    ///
    /// Propagates a power failure, which the range check makes unreachable.
    pub fn series_target(self) -> CoreResult<Rat> {
        Rat::from_integer(2).pow(-i64::from(self.0) - 3)
    }
}

/// The §7.3 tail after `n` retained `artanh` terms (`0002_spec.md` L1).
///
/// `power` must be `z^(2n+1)` and `one_minus_z2` must be `1 - z^2`; both are
/// carried by the caller's loop so that neither is recomputed per term.
///
/// # Errors
///
/// Propagates a division failure; `z < 1` makes `1 - z^2` strictly positive, so
/// the divisor is nonzero whenever the caller respects the domain.
fn series_tail(power: &Rat, terms: u32, one_minus_z2: &Rat) -> CoreResult<Rat> {
    let denominator = &Rat::from_integer(i64::from(2 * terms + 1)) * one_minus_z2;
    power.checked_div(&denominator)
}

/// The least `n <= SERIES_LENGTH_CAP` with `seriesTail(z, n) <= target`
/// (`0002_spec.md` L3).
///
/// This is the definition. [`artanh_enclosure`] fuses the same test into its
/// accumulation loop so that terms are not computed twice, and a test asserts
/// the fused count equals this one on the committed vectors.
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] when `z` is outside `[0,1)`, and
/// [`ErrorCode::ResourceLimit`] when the cap is reached without meeting
/// `target`.
pub fn series_length_for_target(z: &Rat, target: &Rat) -> CoreResult<u32> {
    if z.is_negative() || z >= &Rat::one() {
        return Err(CoreError::new(
            ErrorCode::BadRationalGrammar,
            "the artanh series requires 0 <= z < 1",
        )
        .equation("§7.3")
        .value(format!("{z}")));
    }
    let z_squared = z * z;
    let one_minus_z2 = &Rat::one() - &z_squared;
    let mut power = z.clone();
    for terms in 0..=SERIES_LENGTH_CAP {
        if &series_tail(&power, terms, &one_minus_z2)? <= target {
            return Ok(terms);
        }
        power = &power * &z_squared;
    }
    Err(CoreError::new(
        ErrorCode::ResourceLimit,
        "the artanh series did not reach the requested tolerance within the length cap",
    )
    .equation("§7.3")
    .value(format!("{SERIES_LENGTH_CAP}")))
}

/// The series length one series at `precision` retains (`0002_spec.md` L3).
///
/// # Errors
///
/// Propagates the domain and cap failures of [`series_length_for_target`].
pub fn series_length(z: &Rat, precision: Precision) -> CoreResult<u32> {
    series_length_for_target(z, &precision.series_target()?)
}

/// The exact decomposition `x = mantissa * 2^exponent` with `mantissa` in `[1,2)`
/// (§7.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Normalized {
    /// The mantissa `m`, satisfying `1 <= m < 2`.
    pub mantissa: Rat,
    /// The binary exponent `e`.
    pub exponent: i64,
}

/// Normalize a strictly positive rational as `m * 2^e` with `m` in `[1,2)`.
///
/// The loop is exact and terminates because each step halves or doubles the
/// value toward the unit interval.
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] for a nonpositive input; §7.3
/// requires domain errors to be rejections and never to invoke `log 0`.
pub fn normalize(value: &Rat) -> CoreResult<Normalized> {
    if !value.is_positive() {
        return Err(CoreError::new(
            ErrorCode::BadRationalGrammar,
            "log2 is defined only for strictly positive rationals",
        )
        .equation("§7.3")
        .value(format!("{value}")));
    }
    let two = Rat::from_integer(2);
    let one = Rat::one();
    let mut mantissa = value.clone();
    let mut exponent: i64 = 0;
    while mantissa >= two {
        mantissa = mantissa.checked_div(&two)?;
        exponent += 1;
    }
    while mantissa < one {
        mantissa = &mantissa * &two;
        exponent -= 1;
    }
    Ok(Normalized { mantissa, exponent })
}

/// An `artanh` enclosure together with the series length that produced it.
#[derive(Clone, Debug)]
pub struct ArtanhEnclosure {
    /// The proved enclosure of `artanh(z)`.
    pub interval: Interval,
    /// The number of retained series terms `N`.
    pub terms: u32,
}

/// Enclose `artanh(z)` for `0 <= z < 1` to within the requested tolerance (§7.3).
///
/// Retains the least `N` whose proved tail bound `z^(2N+1)/((2N+1)(1-z^2))` is at
/// most `tolerance`. All retained terms are nonnegative, so the partial sum is a
/// lower bound and partial sum plus tail is an upper bound.
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] when `z` is outside `[0,1)`.
pub fn artanh_enclosure(z: &Rat, tolerance: &Rat) -> CoreResult<ArtanhEnclosure> {
    if z.is_negative() || z >= &Rat::one() {
        return Err(CoreError::new(
            ErrorCode::BadRationalGrammar,
            "the artanh series requires 0 <= z < 1",
        )
        .equation("§7.3")
        .value(format!("{z}")));
    }
    if z.is_zero() {
        return Ok(ArtanhEnclosure {
            interval: Interval::exact(Rat::zero()),
            terms: 0,
        });
    }

    let z_squared = z * z;
    let one_minus_z2 = &Rat::one() - &z_squared;
    // `z < 1` gives `1 - z^2 > 0`, so this division is safe.
    let mut partial = Rat::zero();
    // `power` tracks `z^(2*terms+1)`, which is the tail's leading exponent.
    let mut power = z.clone();

    // The tail is tested *before* the first term is accumulated, so a `z` whose
    // tail already meets the target retains zero terms and agrees with
    // `series_length` (`0002_spec.md` §3.2). A loop that accumulates first
    // returns 1 for every nonzero `z` and diverges from the Lean checker.
    for terms in 0..=SERIES_LENGTH_CAP {
        let tail = series_tail(&power, terms, &one_minus_z2)?;
        if &tail <= tolerance {
            let lo = LowerBound::assert(partial.clone());
            let hi = UpperBound::assert(&partial + &tail);
            return Ok(ArtanhEnclosure {
                interval: Interval::new(lo, hi)?,
                terms,
            });
        }
        let denominator = Rat::from_integer(i64::from(2 * terms + 1));
        partial = &partial + &power.checked_div(&denominator)?;
        power = &power * &z_squared;
    }
    Err(CoreError::new(
        ErrorCode::ResourceLimit,
        "the artanh series did not reach the requested tolerance within the length cap",
    )
    .equation("§7.3")
    .value(format!("{SERIES_LENGTH_CAP}")))
}

/// Enclose `ln 2 = 2 * artanh(1/3)` (§7.3).
///
/// # Errors
///
/// Propagates series failures.
pub fn ln2_enclosure(tolerance: &Rat) -> CoreResult<Interval> {
    let third = Rat::from_signeds(1, 3);
    let enclosure = artanh_enclosure(&third, tolerance)?;
    Ok(enclosure.interval.scale(&Rat::from_integer(2)))
}

/// Enclose `1 / ln 2`, which reverses the endpoints (§7.3).
///
/// # Errors
///
/// Propagates series failures; the enclosure is strictly positive, so the
/// reciprocal is always defined.
pub fn inv_ln2_enclosure(tolerance: &Rat) -> CoreResult<Interval> {
    let ln2 = ln2_enclosure(tolerance)?;
    let lo = ln2.upper().value().recip()?;
    let hi = ln2.lower().value().recip()?;
    Interval::new(LowerBound::assert(lo), UpperBound::assert(hi))
}

/// Enclose `log2(x)` for a strictly positive rational `x` (§7.3).
///
/// The returned interval always contains the true value; the endpoints are the
/// directed bounds §7.2 propagates.
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] for a nonpositive `x`.
pub fn log2_enclosure(x: &Rat, precision: Precision) -> CoreResult<Interval> {
    log2_enclosure_with(x, &Log2Constants::new(precision)?)
}

/// The parts of a `log2` evaluation that depend only on the precision.
///
/// `1/ln 2` is a series of the same length as the one it multiplies, and it was
/// recomputed on every call: at `ℓ*=4` that is roughly a million evaluations of
/// `artanh(1/3)` to produce the same rational a million times.
///
/// This is a value rather than a global cache because `mm-rat` is `no_std`, and
/// because a shared mutable cache would put an ordering dependency between
/// evaluations that §7.2's direction discipline should not have. Passing it
/// keeps every evaluation a pure function of its arguments, which is also what
/// makes evaluating blocks in parallel safe later.
#[derive(Clone, Debug)]
pub struct Log2Constants {
    inner_tolerance: Rat,
    inv_ln2: Interval,
    /// Fractional bits of the outward-rounding grid, when it is enabled.
    ///
    /// `precision + 32`. The composed width of one evaluation is currently about
    /// `0.7 · 2^-precision`, and the single rounding per evaluation adds under
    /// `2^-(precision+32)`, so the total stays below `2^-precision` and P1's
    /// `tol(precision) = 2^-precision` continues to hold unamended. At `ℓ*=4`'s
    /// 535,272 evaluations the accumulated cost is `2.0 × 10^-23` bits, four
    /// orders below the `2^-64` grid `Ω` is reported on — so the certified value
    /// does not move.
    rounding_bits: u32,
}

impl Log2Constants {
    /// Evaluate the shared constants once for a precision.
    ///
    /// # Errors
    ///
    /// Propagates series failures.
    pub fn new(precision: Precision) -> CoreResult<Self> {
        // Each series meets `2^-(precision+3)`; the three spare bits pay for the
        // doubling, the reciprocal, and the product (`0002_spec.md` L2).
        let inner_tolerance = precision.series_target()?;
        let inv_ln2 = inv_ln2_enclosure(&inner_tolerance)?;
        Ok(Self {
            inner_tolerance,
            inv_ln2,
            rounding_bits: precision.bits().saturating_add(32),
        })
    }
}

/// Enclose `log2(x)` reusing constants already evaluated for this precision.
///
/// Identical arithmetic to [`log2_enclosure`] on identical inputs: the constants
/// are the same rationals it would have recomputed, so the result is the same
/// enclosure and the evaluation is still counted.
///
/// # Errors
///
/// Returns [`ErrorCode::BadRationalGrammar`] for a nonpositive `x`.
pub fn log2_enclosure_with(x: &Rat, constants: &Log2Constants) -> CoreResult<Interval> {
    EVALUATIONS.fetch_add(1, Ordering::Relaxed);
    let normalized = normalize(x)?;
    let exponent = Rat::from_integer(normalized.exponent);

    // Exact powers of two need no series at all.
    if normalized.mantissa == Rat::one() {
        return Ok(Interval::exact(exponent));
    }

    let z =
        (&normalized.mantissa - &Rat::one()).checked_div(&(&normalized.mantissa + &Rat::one()))?;
    let artanh = artanh_enclosure(&z, &constants.inner_tolerance)?;

    // log2(m) = 2 * artanh(z) * (1/ln 2); every factor is nonnegative here.
    let doubled = artanh.interval.scale(&Rat::from_integer(2));
    let log2_mantissa = doubled.mul(&constants.inv_ln2);
    round_outward(
        log2_mantissa.add(&Interval::exact(exponent)),
        constants.rounding_bits,
    )
}

/// Widen an enclosure onto the `2^-bits` grid, each endpoint in its own
/// direction (`0001_spec.md` §7.2).
///
/// This is the whole of the B1 change. Every directed endpoint of a series is a
/// rational whose denominator is `den(z)^(2N-1) · lcm(odd)`, and those are
/// pairwise coprime across evaluations — so an accumulator's bit length grows
/// linearly in the number of terms summed, and summation cost grows as `n^2.7`.
/// `lower(E_total)` at `ℓ*=3` runs to 3,647,463 digits for that reason. Snapping
/// each endpoint to a shared `2^-bits` grid makes every subsequent addition a
/// shift-and-add on roughly `bits + log n` bit integers.
///
/// Soundness is one line: `floor(x) ≤ x` and `ceil(x) ≥ x`, so a rounded lower
/// bound is still a lower bound and a rounded upper bound is still an upper
/// bound, and every §7.2 propagation rule composes from those two facts. Every
/// rounding moves the A21 verdict toward *rejection* — `E_total` and `M_total`
/// shrink, the requirement grows — so this can never accept a certificate the
/// unrounded checker rejects.
fn round_outward(interval: Interval, bits: u32) -> CoreResult<Interval> {
    let lo = interval.lower().value().floor_dyadic(bits)?;
    let hi = interval.upper().value().ceil_dyadic(bits)?;
    Interval::new(LowerBound::assert(lo), UpperBound::assert(hi))
}

/// A value known to be at most `log2(x)` (§7.3).
///
/// # Errors
///
/// Propagates domain and series failures.
pub fn log2_lower(x: &Rat, precision: Precision) -> CoreResult<LowerBound> {
    Ok(log2_enclosure(x, precision)?.lower().clone())
}

/// A value known to be at least `log2(x)` (§7.3).
///
/// # Errors
///
/// Propagates domain and series failures.
pub fn log2_upper(x: &Rat, precision: Precision) -> CoreResult<UpperBound> {
    Ok(log2_enclosure(x, precision)?.upper().clone())
}
