//! Maximum-entropy certificate blocks (spec §7.4, A.11).
//!
//! A block certifies an upper bound for `H_D^max(ρ)` — the maximum entropy over
//! distributions on the shape domain `D` matching `ρ`'s three marginals — by
//! exhibiting a strictly positive witness `y` with the same marginals whose
//! logarithm is within `ε` of an additive function
//! `g(a) = λ₀ + λ_X(a_X) + λ_Y(a_Y) + λ_Z(a_Z)`.
//!
//! The checker then returns `entropyUpper(y) + 2ε` (§7.4). It never treats the
//! irrational real `H(y)` as an exact rational.
//!
//! Every one of the four §7.4 conditions is validated here, and nothing is
//! trusted from redundant certificate fields (§6.5).

use crate::domain::ShapeDomain;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::region::Coordinate;
use mm_rat::Rat;
use mm_rat::bounds::UpperBound;
use mm_rat::entropy::entropy_upper;
use mm_rat::log2::{Precision, log2_enclosure};

/// The exact rational data of one maximum-entropy block (§7.4).
#[derive(Clone, Debug)]
pub struct MaxEntropyBlock {
    /// The strictly positive witness `y ∈ Δ(D)`, in canonical domain order.
    pub y: Vec<Rat>,
    /// The additive constant `λ₀`.
    pub lambda0: Rat,
    /// `λ_X`, indexed by the ascending distinct X coordinates of `D`.
    pub lambda_x: Vec<Rat>,
    /// `λ_Y`, indexed likewise.
    pub lambda_y: Vec<Rat>,
    /// `λ_Z`, indexed likewise.
    pub lambda_z: Vec<Rat>,
    /// The slack `ε ≥ 0`.
    pub epsilon: Rat,
}

impl MaxEntropyBlock {
    /// The additive function `g(a) = λ₀ + λ_X(a_X) + λ_Y(a_Y) + λ_Z(a_Z)` (A.11).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::CountMismatch`] when a `λ` vector is too short for
    /// the domain.
    pub fn g(&self, domain: &ShapeDomain, index: usize) -> CoreResult<Rat> {
        let shape = domain.shapes().get(index).ok_or_else(|| {
            CoreError::new(ErrorCode::CountMismatch, "shape index out of range").equation("A.11")
        })?;
        let mut total = self.lambda0.clone();
        for (coordinate, lambdas) in [
            (Coordinate::X, &self.lambda_x),
            (Coordinate::Y, &self.lambda_y),
            (Coordinate::Z, &self.lambda_z),
        ] {
            let value = shape.coord(coordinate);
            let position = domain.coordinate_index(coordinate, value).ok_or_else(|| {
                CoreError::new(
                    ErrorCode::CountMismatch,
                    "coordinate value not in the domain",
                )
                .equation("A.11")
            })?;
            let lambda = lambdas.get(position).ok_or_else(|| {
                CoreError::new(
                    ErrorCode::CountMismatch,
                    "a lambda vector is shorter than its coordinate range",
                )
                .equation("§7.4")
                .value(coordinate.name())
            })?;
            total = &total + lambda;
        }
        Ok(total)
    }

    /// The marginal of a distribution on `D` in one coordinate (A.3).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::CountMismatch`] on a length mismatch.
    pub fn marginal(
        domain: &ShapeDomain,
        values: &[Rat],
        coordinate: Coordinate,
    ) -> CoreResult<Vec<Rat>> {
        if values.len() != domain.len() {
            return Err(CoreError::new(
                ErrorCode::CountMismatch,
                "a distribution length disagrees with its domain",
            )
            .equation("A.3")
            .value(alloc::format!("{} vs {}", values.len(), domain.len())));
        }
        let range = domain.coordinate_values(coordinate);
        let mut out = alloc::vec![Rat::zero(); range.len()];
        for (index, shape) in domain.shapes().iter().enumerate() {
            let position = domain
                .coordinate_index(coordinate, shape.coord(coordinate))
                .ok_or_else(|| {
                    CoreError::new(
                        ErrorCode::CountMismatch,
                        "coordinate value not in the domain",
                    )
                    .equation("A.3")
                })?;
            if let (Some(slot), Some(value)) = (out.get_mut(position), values.get(index)) {
                *slot = &*slot + value;
            }
        }
        Ok(out)
    }

    /// Validate the block against `ρ` and return the certified upper bound for
    /// `H_D^max(ρ)` (§7.4).
    ///
    /// The four §7.4 conditions are checked in order, so the first failure is
    /// deterministic (§5.4):
    ///
    /// 1. `y ∈ Δ(D)` with `y(a) > 0` everywhere;
    /// 2. `y_W = ρ_W` exactly for `W ∈ {X,Y,Z}`;
    /// 3. `ε ≥ 0`; and
    /// 4. `|log2 y(a) - g(a)| ≤ ε` for every `a`, proved through the complete
    ///    interval enclosure of `log2 y(a)`.
    ///
    /// # Errors
    ///
    /// Returns the stable code for whichever condition fails first.
    pub fn certify(
        &self,
        domain: &ShapeDomain,
        rho: &[Rat],
        precision: Precision,
    ) -> CoreResult<UpperBound> {
        // 1. y is a strictly positive distribution on D.
        if self.y.len() != domain.len() {
            return Err(CoreError::new(
                ErrorCode::CountMismatch,
                "the witness length disagrees with its domain",
            )
            .equation("§7.4")
            .value(alloc::format!("{} vs {}", self.y.len(), domain.len())));
        }
        mm_rat::entropy::validate_positive_simplex(&self.y)?;

        // 2. All three marginals agree with rho, exactly.
        mm_rat::entropy::validate_simplex(rho)?;
        for coordinate in Coordinate::ALL {
            let witness_marginal = Self::marginal(domain, &self.y, coordinate)?;
            let target_marginal = Self::marginal(domain, rho, coordinate)?;
            if witness_marginal != target_marginal {
                return Err(CoreError::new(
                    ErrorCode::WrongMarginal,
                    "a maximum-entropy witness marginal disagrees with rho",
                )
                .equation("§7.4")
                .value(coordinate.name()));
            }
        }

        // 3. epsilon is nonnegative.
        if self.epsilon.is_negative() {
            return Err(CoreError::new(
                ErrorCode::NegativeEpsilon,
                "the maximum-entropy slack epsilon must be nonnegative",
            )
            .equation("§7.4")
            .value(alloc::format!("{}", self.epsilon)));
        }

        // 4. The complete enclosure of log2 y(a) lies inside [g(a)-eps, g(a)+eps].
        for index in 0..domain.len() {
            let value = self.y.get(index).ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "witness index out of range")
                    .equation("§7.4")
            })?;
            let enclosure = log2_enclosure(value, precision)?;
            let g = self.g(domain, index)?;
            let lower = &g - &self.epsilon;
            let upper = &g + &self.epsilon;
            if enclosure.lower().value() < &lower || enclosure.upper().value() > &upper {
                return Err(CoreError::new(
                    ErrorCode::InsufficientResidualBound,
                    "the log2 enclosure of a witness entry escapes [g-eps, g+eps]",
                )
                .equation("§7.4")
                .value(alloc::format!("index {index}"))
                .value(alloc::format!("enclosure {enclosure}"))
                .value(alloc::format!("[{lower}, {upper}]")));
            }
        }

        // The certified bound: entropyUpper(y) + 2 eps (§7.4).
        let base = entropy_upper(&self.y, precision)?;
        let slack = &Rat::from_integer(2) * &self.epsilon;
        Ok(UpperBound::assert(base.value() + &slack))
    }
}

extern crate alloc;
