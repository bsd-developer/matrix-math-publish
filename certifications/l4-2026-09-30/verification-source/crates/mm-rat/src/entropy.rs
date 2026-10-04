//! Directed entropy bounds and the guarded conditional mixture (spec §7.3, §7.4, §7.6).
//!
//! Entropies are base two (Appendix A). `H(rho) = -sum rho(x) log2 rho(x)` over
//! the support of `rho`, with the explicit convention `0 * log 0 = 0` (§7.3).
//!
//! Direction matters: for positive `p`, the term `-p * log2(p)` multiplies a
//! logarithm by the **negative** factor `-p`, which reverses the bound direction
//! (§7.3). Encoding that once, here, is why the checker cannot silently use a
//! lower bound where it needs an upper one.

use crate::bounds::{Interval, LowerBound, UpperBound};
use crate::log2::{Log2Constants, Precision, log2_enclosure, log2_enclosure_with};
use crate::rational::Rat;
use alloc::format;
use alloc::vec::Vec;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};

/// Validate that `values` form a probability distribution: every entry is
/// nonnegative and the exact sum is one (A.2).
///
/// # Errors
///
/// Returns [`ErrorCode::BadSimplex`] for a negative entry or a sum other than one.
pub fn validate_simplex(values: &[Rat]) -> CoreResult<()> {
    let mut total = Rat::zero();
    for (index, value) in values.iter().enumerate() {
        if value.is_negative() {
            return Err(CoreError::new(
                ErrorCode::BadSimplex,
                "a distribution entry must be nonnegative",
            )
            .equation("A.2")
            .value(format!("index {index} = {value}")));
        }
        total = &total + value;
    }
    if total != Rat::one() {
        return Err(CoreError::new(
            ErrorCode::BadSimplex,
            "a distribution must sum to exactly one",
        )
        .equation("A.2")
        .value(format!("sum = {total}")));
    }
    Ok(())
}

/// Validate that every entry is strictly positive as well as summing to one.
///
/// This is the §7.4 item 1 requirement on the maximum-entropy witness `y`.
///
/// # Errors
///
/// Returns [`ErrorCode::NonpositiveY`] for a nonpositive entry, or
/// [`ErrorCode::BadSimplex`] when the sum is not one.
pub fn validate_positive_simplex(values: &[Rat]) -> CoreResult<()> {
    for (index, value) in values.iter().enumerate() {
        if !value.is_positive() {
            return Err(CoreError::new(
                ErrorCode::NonpositiveY,
                "every maximum-entropy witness entry must be strictly positive",
            )
            .equation("§7.4")
            .value(format!("index {index} = {value}")));
        }
    }
    validate_simplex(values)
}

/// The enclosure of one entropy term `-p * log2(p)` (§7.3).
///
/// Returns the exact zero interval for `p = 0` under the `0 * log 0 = 0`
/// convention, and rejects a negative `p`.
///
/// # Errors
///
/// Returns [`ErrorCode::BadSimplex`] for a negative probability.
pub fn term_enclosure(p: &Rat, precision: Precision) -> CoreResult<Interval> {
    if p.is_negative() {
        return Err(CoreError::new(
            ErrorCode::BadSimplex,
            "an entropy term requires a nonnegative probability",
        )
        .equation("§7.3")
        .value(format!("{p}")));
    }
    if p.is_zero() {
        // The 0 * log 0 = 0 convention; `log 0` is never invoked (§7.3).
        return Ok(Interval::exact(Rat::zero()));
    }
    let log = log2_enclosure(p, precision)?;
    // Multiplying by the negative factor `-p` reverses the direction.
    Ok(log.scale(&-p.clone()))
}

/// The enclosure of `H(rho)` for a validated distribution (A.3).
///
/// # Errors
///
/// Propagates term failures.
pub fn entropy_enclosure(distribution: &[Rat], precision: Precision) -> CoreResult<Interval> {
    // The shared constants are evaluated once for the whole distribution rather
    // than once per term. At `ℓ*=4` a distribution runs to hundreds of entries.
    let constants = Log2Constants::new(precision)?;
    let mut terms = Vec::with_capacity(distribution.len());
    for p in distribution {
        terms.push(term_enclosure_with(p, &constants)?);
    }
    Ok(sum_pairwise(terms))
}

/// Add a list of enclosures by halving rather than left to right.
///
/// Addition in `ℚ` is associative and commutative, so every bracketing yields
/// the *same reduced rational* — this changes the cost, never the value, and
/// `Interval::add` adds the two directed endpoints independently so the
/// direction discipline of §7.2 is untouched.
///
/// The cost is the point. Each directed endpoint here is a series value whose
/// denominator is `den(z)^(2N-1) · lcm(odd)`, and those are pairwise coprime
/// across terms, so a sequential accumulator's denominator grows by a fresh
/// factor on every add — Θ(n²) in the term count. Halving keeps the operands
/// balanced. Measured at 2.6× for 32 terms and 4.5× for 512, growing with n.
fn sum_pairwise(mut terms: Vec<Interval>) -> Interval {
    while terms.len() > 1 {
        let mut folded = Vec::with_capacity(terms.len().div_ceil(2));
        let mut chunks = terms.chunks_exact(2);
        for pair in chunks.by_ref() {
            folded.push(pair[0].add(&pair[1]));
        }
        if let Some(odd) = chunks.remainder().first() {
            folded.push(odd.clone());
        }
        terms = folded;
    }
    terms
        .into_iter()
        .next()
        .unwrap_or_else(|| Interval::exact(Rat::zero()))
}

/// [`term_enclosure`] with the precision's constants already evaluated.
///
/// # Errors
///
/// Returns [`ErrorCode::BadSimplex`] for a negative probability.
pub fn term_enclosure_with(p: &Rat, constants: &Log2Constants) -> CoreResult<Interval> {
    if p.is_negative() {
        return Err(CoreError::new(
            ErrorCode::BadSimplex,
            "an entropy term requires a nonnegative probability",
        )
        .equation("§7.3")
        .value(format!("{p}")));
    }
    if p.is_zero() {
        // The 0 * log 0 = 0 convention; `log 0` is never invoked (§7.3).
        return Ok(Interval::exact(Rat::zero()));
    }
    let log = log2_enclosure_with(p, constants)?;
    // Multiplying by the negative factor `-p` reverses the direction.
    Ok(log.scale(&-p.clone()))
}

/// A value known to be at most `H(rho)` (§7.2).
///
/// # Errors
///
/// Propagates term failures.
pub fn entropy_lower(distribution: &[Rat], precision: Precision) -> CoreResult<LowerBound> {
    Ok(entropy_enclosure(distribution, precision)?.lower().clone())
}

/// A value known to be at least `H(rho)` (§7.2).
///
/// # Errors
///
/// Propagates term failures.
pub fn entropy_upper(distribution: &[Rat], precision: Precision) -> CoreResult<UpperBound> {
    Ok(entropy_enclosure(distribution, precision)?.upper().clone())
}

/// The guarded conditional mixture term of §7.6.
///
/// Appendix A uses the convention `0 * undefined := 0`. Division by zero is
/// never evaluated: when `weight` is zero the function returns the exact zero
/// interval without normalizing the numerator distribution.
///
/// # Errors
///
/// Returns [`ErrorCode::BadSimplex`] for a negative weight, and propagates
/// normalization failures otherwise.
pub fn weighted_conditional_entropy(
    weight: &Rat,
    numerator_distribution: &[Rat],
    precision: Precision,
) -> CoreResult<Interval> {
    if weight.is_negative() {
        return Err(CoreError::new(
            ErrorCode::BadSimplex,
            "a conditional mixture weight must be nonnegative",
        )
        .equation("§7.6")
        .value(format!("{weight}")));
    }
    if weight.is_zero() {
        return Ok(Interval::exact(Rat::zero()));
    }
    let mut mass = Rat::zero();
    for value in numerator_distribution {
        mass = &mass + value;
    }
    if mass.is_zero() {
        return Err(CoreError::new(
            ErrorCode::BadSimplex,
            "a nonzero weight requires a nonzero numerator distribution",
        )
        .equation("§7.6"));
    }
    let normalized: Vec<Rat> = numerator_distribution
        .iter()
        .map(|value| value.checked_div(&mass))
        .collect::<CoreResult<Vec<Rat>>>()?;
    validate_simplex(&normalized)?;
    Ok(entropy_enclosure(&normalized, precision)?.scale(weight))
}

/// The §7.4 maximum-entropy upper bound `entropyUpper(y) + 2*epsilon` (A22).
///
/// The executable checker returns this rational value as an upper bound for
/// `H_D^max(rho)`. It never treats the irrational real `H(y)` as an exact
/// rational.
///
/// # Errors
///
/// Returns [`ErrorCode::NegativeEpsilon`] for a negative `epsilon`, and
/// propagates entropy failures.
pub fn max_entropy_upper(
    witness: &[Rat],
    epsilon: &Rat,
    precision: Precision,
) -> CoreResult<UpperBound> {
    if epsilon.is_negative() {
        return Err(CoreError::new(
            ErrorCode::NegativeEpsilon,
            "the maximum-entropy slack epsilon must be nonnegative",
        )
        .equation("§7.4")
        .value(format!("{epsilon}")));
    }
    let base = entropy_upper(witness, precision)?;
    let slack = &Rat::from_integer(2) * epsilon;
    Ok(UpperBound::assert(base.value() + &slack))
}
