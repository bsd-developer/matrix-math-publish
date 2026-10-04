//! Group-level evaluation of a symmetric certificate (`docs/specs/0007_spec.md` §5).
//!
//! The general evaluator visits one node per position: 5,779 at `ℓ* = 3` and
//! 1,552,339 at `ℓ* = 4`. This one visits one entry per level-shape group: 60 and
//! 213. `docs/experiments/omega-l4.md` records that exact evaluation is
//! *superlinear* in the number of blocks, so the saving is larger than the ratio
//! of counts.
//!
//! §5.7 is why the aggregation is exact rather than approximate. Every quantity
//! is a rational; the §7.3 directed bounds are functions of a rational and the
//! certificate's `log_precision_bits`, which both paths share; and multiplication
//! and addition in `ℚ` are exact. So
//!
//! ```text
//! Σ_(T ∈ group) m_T · hLower(x, prec) = ( Σ_(T ∈ group) m_T ) · hLower(x, prec)
//! ```
//!
//! is distributivity, not an approximation. Aggregating masses before applying a
//! bound therefore preserves equality, which is what makes §5.1's theorem an
//! equality rather than an inequality.
//!
//! This module must not introduce a rounding, truncation, or precision-selection
//! step the general evaluator does not perform, and must not choose a series
//! length from anything but the certificate's declared precision. Either would
//! replace the equality with a two-sided error term that no test recovers.

use crate::domain::ShapeDomain;
use crate::domain::a2;
use crate::domain::{SupportVector, support_vectors};
use crate::evaluate::OmegaBounds;
use crate::evaluate::{full_support, weighted_conditional_entropy_upper};
use crate::maxent::MaxEntropyBlock;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::level::Level;
use mm_core::region::{Coordinate, Region};
use mm_core::shape::Shape;
use mm_rat::bounds::{LowerBound, UpperBound};
use mm_rat::entropy::{entropy_lower, entropy_upper};
use mm_rat::log2::{Precision, log2_lower, log2_upper};
use mm_rat::rational::Rat;
use mm_schema::symmetric::{GroupKey, GroupPayload, SymmetricCertificate, block_keys, groups};
use std::collections::BTreeMap;

/// Group masses in [`groups`] order (`0007_spec.md` §5.2).
///
/// ```text
/// M(ℓ*, s) = α_G(s)                                              (S1)
/// M(ℓ-1, u) = Σ_(s ∈ S_ℓ : u ∈ Split(s))
///               M(ℓ, s) · (α_(ℓ,s)(u) + α_(ℓ,s)(s-u))            (S2)
/// ```
///
/// S1 is A2 summed over the six regions: `Σ_r A_G^(r) α_G^(r)(s) = α_G(s)`
/// because `α_G^(r)` does not depend on `r` and `A_G ∈ Δ([6])`. S2 is A3 summed
/// over the six regions and over the nodes of the group, by the same two facts.
///
/// The `α(u) + α(s-u)` pairing is §5.3: `u ↦ s-u` reverses the lexicographic
/// order of `Split(s)`, so the weight vector is `α` plus its own reverse.
///
/// # Errors
///
/// Returns [`ErrorCode::CountMismatch`] when a group's `α` is not the length its
/// domain requires, and propagates shape failures.
pub fn group_masses(certificate: &SymmetricCertificate) -> CoreResult<Vec<Rat>> {
    let keys = groups(certificate.level);
    let mut masses = vec![Rat::zero(); keys.len()];

    let index_of = |key: GroupKey| -> CoreResult<usize> {
        keys.iter()
            .position(|candidate| candidate.level == key.level && candidate.shape == key.shape)
            .ok_or_else(|| {
                CoreError::new(
                    ErrorCode::CountMismatch,
                    "a level-shape pair is not in the group enumeration",
                )
                .equation("§3.2")
            })
    };

    // S1: the root's alpha over S_{l*} seeds the top level.
    let GroupPayload::Branching {
        alpha: root_alpha, ..
    } = &certificate.root
    else {
        return Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "the root must be a branching group",
        )
        .equation("§3.3"));
    };
    let mut top = Shape::enumerate(certificate.level);
    top.sort_by_key(|shape: &Shape| shape.canonical_key());
    if root_alpha.len() != top.len() {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the root alpha does not cover S_{l*}",
        )
        .equation("§3.3"));
    }
    for (shape, value) in top.iter().zip(root_alpha.iter()) {
        masses[index_of(GroupKey {
            level: certificate.level,
            shape: *shape,
        })?] = value.clone();
    }

    // S2: push mass down, level by level. Only positive shapes at level >= 3
    // branch; zero-shape and positive level-2 groups are leaves.
    let mut current = certificate.level.get();
    while current >= 3 {
        let this = Level::new(current)?;
        let child_level = this.child()?;
        let mut shapes = Shape::enumerate(this);
        shapes.sort_by_key(|shape: &Shape| shape.canonical_key());
        for shape in shapes {
            if shape.is_zero_shape() {
                continue;
            }
            let parent_index = index_of(GroupKey { level: this, shape })?;
            let parent_mass = masses[parent_index].clone();
            let GroupPayload::Branching { alpha, .. } = &certificate.groups[parent_index] else {
                return Err(CoreError::new(
                    ErrorCode::SchemaMismatch,
                    "a positive group above level two must be branching",
                )
                .equation("§3.3"));
            };
            let splits = shape.splits()?;
            if alpha.len() != splits.len() {
                return Err(CoreError::new(
                    ErrorCode::CountMismatch,
                    "a group alpha does not cover its split domain",
                )
                .equation("§3.3"));
            }
            // §5.3: the complement of the m-th split is the m-th from the end,
            // so the weight vector is alpha plus its own reverse. Deriving the
            // companion any other way is the defect omega-l3.md records.
            for (position, split) in splits.iter().enumerate() {
                let complement = alpha.get(alpha.len() - 1 - position).ok_or_else(|| {
                    CoreError::new(ErrorCode::CountMismatch, "alpha is shorter than its domain")
                        .equation("§5.3")
                })?;
                let weight = &(&alpha[position] + complement) * &parent_mass;
                let child = index_of(GroupKey {
                    level: child_level,
                    shape: *split,
                })?;
                masses[child] = &masses[child] + &weight;
            }
        }
        current -= 1;
    }
    Ok(masses)
}

/// The `β` of every group, over the full support space, indexed by [`groups`]
/// order then by coordinate (`0007_spec.md` §5.4, §5.5).
///
/// Region independence is identity 3: when `β^(r)` does not depend on `r`, the
/// A6 region mixture `Σ_r A_T^(r) β^(r)` is that same value, because
/// `A_T ∈ Δ([6])`. So this table carries one `β` per group where the general
/// evaluator carries one per node, and no region loop appears at all.
///
/// The recursion runs bottom-up: level-two groups are leaves and are read
/// directly from their free variables; a positive group above level two mixes
/// its children's `β` under A5, which concatenates support vectors and
/// multiplies probabilities.
///
/// # Errors
///
/// Propagates domain failures and returns [`ErrorCode::CountMismatch`] when a
/// group's free variables do not match its A.2 domain.
pub fn group_beta_table(certificate: &SymmetricCertificate) -> CoreResult<Vec<[Vec<Rat>; 3]>> {
    let keys = groups(certificate.level);
    let mut table: Vec<[Vec<Rat>; 3]> = vec![[Vec::new(), Vec::new(), Vec::new()]; keys.len()];
    let index_of = |level: Level, shape: Shape| -> CoreResult<usize> {
        keys.iter()
            .position(|candidate| candidate.level == level && candidate.shape == shape)
            .ok_or_else(|| {
                CoreError::new(
                    ErrorCode::CountMismatch,
                    "a group is missing from the enumeration",
                )
                .equation("§3.2")
            })
    };

    for current in 2..=certificate.level.get() {
        let this = Level::new(current)?;
        let support = full_support(this);
        let mut shapes = Shape::enumerate(this);
        shapes.sort_by_key(|shape: &Shape| shape.canonical_key());
        for shape in shapes {
            let position = index_of(this, shape)?;
            let payload = &certificate.groups[position];
            let mut values = [Vec::new(), Vec::new(), Vec::new()];
            match payload {
                GroupPayload::ZeroShape { beta } => {
                    for coordinate in Coordinate::ALL {
                        values[coordinate.index()] =
                            leaf_zero_shape_beta(shape, coordinate, beta, support)?;
                    }
                }
                GroupPayload::LevelTwo { mu } => {
                    for coordinate in Coordinate::ALL {
                        values[coordinate.index()] =
                            leaf_level_two_beta(shape, coordinate, mu, support)?;
                    }
                }
                GroupPayload::Branching { alpha, .. } => {
                    // A5 through the group's single alpha. No region mixture:
                    // identity 3 collapses it.
                    for coordinate in Coordinate::ALL {
                        values[coordinate.index()] =
                            group_split_mixture_at(&keys, &table, this, shape, alpha, coordinate)?;
                    }
                }
            }
            table[position] = values;
        }
    }
    Ok(table)
}

fn dense_from_sparse(
    sparse: Vec<(SupportVector, Rat)>,
    support: &[SupportVector],
) -> CoreResult<Vec<Rat>> {
    let mut out = vec![Rat::zero(); support.len()];
    for (vector, value) in sparse {
        let position = support
            .iter()
            .position(|candidate| *candidate == vector)
            .ok_or_else(|| {
                CoreError::new(
                    ErrorCode::CountMismatch,
                    "a support vector is missing from the full support space",
                )
                .equation("A.5")
            })?;
        out[position] = &out[position] + &value;
    }
    Ok(out)
}

/// A7 for a positive level-two group.
fn leaf_level_two_beta(
    shape: Shape,
    coordinate: Coordinate,
    mu: &Rat,
    support: &[SupportVector],
) -> CoreResult<Vec<Rat>> {
    let vectors = support_vectors(shape.level(), shape.coord(coordinate))?;
    let mut sparse = Vec::with_capacity(vectors.len());
    if shape.coord(coordinate) == 2 {
        let one_minus = &Rat::one() - &(&Rat::from_integer(2) * mu);
        for vector in vectors {
            let value = match vector.entries() {
                [0, 2] | [2, 0] => mu.clone(),
                [1, 1] => one_minus.clone(),
                _ => Rat::zero(),
            };
            sparse.push((vector, value));
        }
    } else {
        for vector in vectors {
            let value = match vector.entries() {
                [0, 1] | [1, 0] => Rat::from_signeds(1, 2),
                _ => Rat::zero(),
            };
            sparse.push((vector, value));
        }
    }
    dense_from_sparse(sparse, support)
}

/// A4 for a zero-shape group.
fn leaf_zero_shape_beta(
    shape: Shape,
    coordinate: Coordinate,
    beta: &[Rat],
    support: &[SupportVector],
) -> CoreResult<Vec<Rat>> {
    let zero_coord = shape.first_zero_coord().ok_or_else(|| {
        CoreError::new(
            ErrorCode::BadPath,
            "a zero-shape group has a zero coordinate",
        )
        .equation("A.5")
    })?;
    let free_coord = shape.first_nonzero_coord().ok_or_else(|| {
        CoreError::new(
            ErrorCode::BadPath,
            "a zero-shape group with no positive coordinate cannot occur",
        )
        .equation("A.5")
    })?;
    let vectors = support_vectors(shape.level(), shape.coord(coordinate))?;
    let free_vectors = support_vectors(shape.level(), shape.coord(free_coord))?;
    let sparse: Vec<(SupportVector, Rat)> = if coordinate == zero_coord {
        vectors
            .into_iter()
            .map(|vector| {
                let value = if vector.entries().iter().all(|entry| *entry == 0) {
                    Rat::one()
                } else {
                    Rat::zero()
                };
                (vector, value)
            })
            .collect()
    } else if coordinate == free_coord {
        free_vectors.into_iter().zip(beta.iter().cloned()).collect()
    } else {
        // A4: β_(T,W2) is the complement reflection of the free β.
        vectors
            .into_iter()
            .map(|vector| {
                let source = vector.complement();
                let value = free_vectors
                    .iter()
                    .position(|candidate| *candidate == source)
                    .and_then(|index| beta.get(index))
                    .cloned()
                    .unwrap_or_else(Rat::zero);
                (vector, value)
            })
            .collect()
    };
    dense_from_sparse(sparse, support)
}

/// A18/A19 local matrix sizes for one group, already scaled by its mass
/// (`0007_spec.md` §5.6).
///
/// The general evaluator computes this per leaf and sums over 1,080,288
/// zero-shape leaves and 437,400 positive level-two leaves at `ℓ* = 4`. The
/// group form is the same function of the same free variables, scaled by the
/// aggregated mass — §5.7's distributivity, exact in `ℚ`.
fn group_local_sizes(
    shape: Shape,
    payload: &GroupPayload,
    mass: &Rat,
    q: &Rat,
    precision: Precision,
) -> CoreResult<[LowerBound; 3]> {
    let log_q = log2_lower(q, precision)?;
    let zero = LowerBound::assert(Rat::zero());
    match payload {
        GroupPayload::ZeroShape { beta } => {
            // A18: only the first zero coordinate carries a local size.
            let w0 = shape.first_zero_coord().ok_or_else(|| {
                CoreError::new(
                    ErrorCode::BadPath,
                    "a zero-shape group has a zero coordinate",
                )
                .equation("A.9")
            })?;
            let w1 = shape.first_nonzero_coord().ok_or_else(|| {
                CoreError::new(
                    ErrorCode::BadPath,
                    "a zero-shape group has a positive coordinate",
                )
                .equation("A.9")
            })?;
            let vectors = support_vectors(shape.level(), shape.coord(w1))?;
            if vectors.len() != beta.len() {
                return Err(CoreError::new(
                    ErrorCode::CountMismatch,
                    "a zero-shape group beta does not cover its support",
                )
                .equation("A.2"));
            }
            let entropy = entropy_lower(beta, precision)?;
            let mut ones_weight = Rat::zero();
            for (vector, value) in vectors.iter().zip(beta.iter()) {
                let count = Rat::from(vector.ones() as u64);
                ones_weight = &ones_weight + &(value * &count);
            }
            let weighted = log_q.scale_nonnegative(&ones_weight)?;
            let inner = entropy.add(&weighted);
            let mut out = [zero.clone(), zero.clone(), zero];
            out[w0.index()] = inner.scale_nonnegative(mass)?;
            Ok(out)
        }
        GroupPayload::LevelTwo { mu } => {
            // A19: the coordinate whose shape entry is 2 gets 2*mu*log2 q, the
            // other two get (1-2mu)*log2 q.
            let two_mu = &Rat::from_integer(2) * mu;
            let rest = &Rat::one() - &two_mu;
            if rest.is_negative() {
                return Err(CoreError::new(
                    ErrorCode::BadSimplex,
                    "1 - 2*mu must be nonnegative, which A.2's domain guarantees",
                )
                .equation("A.19"));
            }
            let mut out = [zero.clone(), zero.clone(), zero];
            for coordinate in Coordinate::ALL {
                let weight = if shape.coord(coordinate) == 2 {
                    &two_mu * mass
                } else {
                    &rest * mass
                };
                out[coordinate.index()] = log_q.scale_nonnegative(&weight)?;
            }
            Ok(out)
        }
        GroupPayload::Branching { .. } => Err(CoreError::new(
            ErrorCode::BadPath,
            "local matrix sizes are defined only at leaf groups",
        )
        .equation("A.9")),
    }
}

/// `lower(M_total)` over groups (A18–A20, `0007_spec.md` §5.6).
///
/// # Errors
///
/// Propagates domain and bound failures.
pub fn group_m_total(
    certificate: &SymmetricCertificate,
    masses: &[Rat],
    q: u32,
    precision: Precision,
) -> CoreResult<LowerBound> {
    let keys = groups(certificate.level);
    let q = Rat::from(u64::from(q));
    let mut totals = [
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
    ];
    for (index, key) in keys.iter().enumerate() {
        let payload = &certificate.groups[index];
        if matches!(payload, GroupPayload::Branching { .. }) {
            continue;
        }
        let sizes = group_local_sizes(key.shape, payload, &masses[index], &q, precision)?;
        for coordinate in Coordinate::ALL {
            totals[coordinate.index()] = totals[coordinate.index()].add(&sizes[coordinate.index()]);
        }
    }
    // §7.2: the lower bound of a minimum is the minimum of the lower bounds.
    let [x, y, z] = totals;
    Ok(x.min(y).min(z))
}

/// `lower(E_2)` over groups (A16, A17, `0007_spec.md` §5.6).
///
/// # Errors
///
/// Propagates bound failures.
pub fn group_e_level_two(
    certificate: &SymmetricCertificate,
    masses: &[Rat],
    precision: Precision,
) -> CoreResult<LowerBound> {
    let keys = groups(certificate.level);
    let mut totals = [
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
    ];
    for (index, key) in keys.iter().enumerate() {
        let GroupPayload::LevelTwo { mu } = &certificate.groups[index] else {
            continue;
        };
        let mass = &masses[index];
        let two_mu = &Rat::from_integer(2) * mu;
        let rest = &Rat::one() - &two_mu;
        let distribution = [mu.clone(), mu.clone(), rest];
        let entropy = entropy_lower(&distribution, precision)?;
        let one = LowerBound::assert(Rat::one());
        let mut per = [
            one.clone().scale_nonnegative(mass)?,
            one.clone().scale_nonnegative(mass)?,
            one.scale_nonnegative(mass)?,
        ];
        for coordinate in Coordinate::ALL {
            if key.shape.coord(coordinate) == 2 {
                per[coordinate.index()] = entropy.scale_nonnegative(mass)?;
            }
        }
        for coordinate in Coordinate::ALL {
            totals[coordinate.index()] = totals[coordinate.index()].add(&per[coordinate.index()]);
        }
    }
    let [x, y, z] = totals;
    Ok(x.min(y).min(z))
}

/// The parts of A14 that the region does not change.
///
/// `region` reaches `group_e_interior_one` in exactly two ways: a scalar weight
/// `A_T^(r)`, and the axis permutation `region.permute(..)`. Neither changes the
/// group's own `α` or the mixture stored for it, so the entropies of those are
/// one value evaluated six times.
///
/// The axis-indexed entries are worse than sixfold in the other direction: the
/// six regions permute onto three coordinates, and the `(axis, is_y)` loop
/// visits twelve slots, so each distinct `h_beta` was computed four times. Those
/// are also the largest arguments in the evaluation — roughly 350 bits at
/// `ℓ*=4` — so they dominate what the hoist saves.
///
/// At `ℓ*=4` this is 1,005,504 log2 evaluations against 558,789, a factor of
/// 1.80; at `ℓ*=3` it is 1.62.
struct GroupInvariants {
    domain: ShapeDomain,
    h_alpha: LowerBound,
    h_max: UpperBound,
    h_marginal: [LowerBound; 3],
    h_beta: [LowerBound; 3],
}

impl GroupInvariants {
    /// Evaluate once per group, before the region loop.
    fn build(
        keys: &[GroupKey],
        beta: &[[Vec<Rat>; 3]],
        level: Level,
        shape: Shape,
        alpha: &[Rat],
        block: &MaxEntropyBlock,
        precision: Precision,
    ) -> CoreResult<Self> {
        let domain = ShapeDomain::splits(shape)?;
        // The mixture for this group is what `group_beta_table` already stored:
        // the same keys, level, shape and alpha, and the table is complete
        // before any E_l is evaluated.
        let self_index = keys
            .iter()
            .position(|key| key.level == level && key.shape == shape)
            .ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "this group is missing").equation("§3.2")
            })?;
        // Each hoisted value is charged for the evaluations a checker performs
        // and this does not. The multiplicities come from the region loop:
        // `h_alpha` and `h_max` are evaluated once per region, so six times; the
        // six regions permute onto three coordinates, so a checker reaches each
        // `h_marginal` twice over the six regions, and each `h_beta` four times
        // over the twelve `(region, axis)` slots.
        //
        // The charge cannot be a constant: `entropy_lower` performs one directed
        // evaluation per nonzero entry, so the cost of one call is a property of
        // the vector. It is measured here rather than assumed.
        let before = mm_rat::log2::evaluations();
        let h_alpha = entropy_lower(alpha, precision)?;
        let h_max = block.certify(&domain, alpha, precision)?;
        let once = mm_rat::log2::evaluations() - before;
        mm_rat::log2::charge_elided_evaluations(5 * once);

        let mut h_marginal = [
            LowerBound::assert(Rat::zero()),
            LowerBound::assert(Rat::zero()),
            LowerBound::assert(Rat::zero()),
        ];
        let mut h_beta = h_marginal.clone();
        for axis in Coordinate::ALL {
            let before = mm_rat::log2::evaluations();
            let marginal = MaxEntropyBlock::marginal(&domain, alpha, axis)?;
            h_marginal[axis.index()] = entropy_lower(&marginal, precision)?;
            let marginal_cost = mm_rat::log2::evaluations() - before;

            let before = mm_rat::log2::evaluations();
            h_beta[axis.index()] = entropy_lower(&beta[self_index][axis.index()], precision)?;
            let beta_cost = mm_rat::log2::evaluations() - before;

            mm_rat::log2::charge_elided_evaluations(marginal_cost + 3 * beta_cost);
        }
        Ok(Self {
            domain,
            h_alpha,
            h_max,
            h_marginal,
            h_beta,
        })
    }
}

/// One group's contribution to `E_ℓ` in one region (A12–A14, `0007_spec.md` §5.4).
///
/// **A15 does not collapse over regions**, and §5.4 is explicit that merging this
/// with identity 3 is a mistake. A14 places `m_T A_T^(r)` inside each of the
/// three quantities and A15 sums the six regional minima with no further weight.
/// What symmetry buys is weaker: the region-`r` quantity depends on `r` only
/// through the permutation `π_r`, because the child data it reads is
/// region-independent.
///
/// `Q_Y` takes the **ordered** pair `(π_r(Y), π_r(Z))`, because A8 and A12 sum
/// over `u_Y` while selecting on `u_Z`. Deriving the companion coordinate from
/// `cY` alone is the defect `docs/experiments/omega-l3.md` records as caught at
/// `ℓ* = 3` by float-versus-exact disagreement, and this must not reintroduce it.
#[allow(
    clippy::too_many_arguments,
    reason = "mirrors the general e_interior_node"
)]
fn group_e_interior_one(
    keys: &[GroupKey],
    beta: &[[Vec<Rat>; 3]],
    level: Level,
    shape: Shape,
    alpha: &[Rat],
    region_weights: &[Rat],
    mass: &Rat,
    region: Region,
    invariants: &GroupInvariants,
    precision: Precision,
) -> CoreResult<[LowerBound; 3]> {
    let splits = shape.splits()?;
    let domain = &invariants.domain;
    let region_index = usize::from(region.get() - 1);
    let region_weight = region_weights
        .get(region_index)
        .cloned()
        .unwrap_or_else(Rat::zero);

    let axis_x = region.permute(Coordinate::X);
    let axis_y = region.permute(Coordinate::Y);
    let axis_z = region.permute(Coordinate::Z);

    // A14 multiplies every term by m_T A_T^(r); under symmetry m_T is the
    // aggregated group mass, which §5.7 shows is exact.
    let scale = mass * &region_weight;
    let zero = LowerBound::assert(Rat::zero());
    let mut out = [zero.clone(), zero.clone(), zero];
    if scale.is_zero() {
        return Ok(out);
    }

    let child_level = level.child()?;
    let child_index = |shape: Shape| -> CoreResult<usize> {
        keys.iter()
            .position(|key| key.level == child_level && key.shape == shape)
            .ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "a child group is missing")
                    .equation("§3.2")
            })
    };

    // A14 first term: H((α)_X) - P_(Split(s))(α).
    out[axis_x.index()] = invariants.h_marginal[axis_x.index()]
        .add(&invariants.h_alpha)
        .sub_upper(&invariants.h_max)
        .scale_nonnegative(&scale)?;

    let child_width = full_support(child_level).len();
    let paired_weight = |split_index: usize, split: &Shape| -> CoreResult<Rat> {
        // §5.3: the complement of the m-th split is the m-th from the end, so
        // its index is the mirror — no scan, and no silent fallback to the
        // split itself (`0008_spec.md` §6.2 R6).
        let complement = shape.complement(*split)?;
        let complement_index = splits.len().checked_sub(1 + split_index).ok_or_else(|| {
            CoreError::new(ErrorCode::BadPath, "split index exceeds the split list").equation("A.5")
        })?;
        debug_assert_eq!(
            splits.get(complement_index),
            Some(&complement),
            "canonical split order must be complement-reversed (§5.3)"
        );
        if splits.get(complement_index) != Some(&complement) {
            return Err(CoreError::new(
                ErrorCode::BadPath,
                "the split list is not complement-reversed",
            )
            .equation("A.5"));
        }
        Ok(&alpha.get(split_index).cloned().unwrap_or_else(Rat::zero)
            + &alpha
                .get(complement_index)
                .cloned()
                .unwrap_or_else(Rat::zero))
    };

    for (axis, is_y) in [(axis_y, true), (axis_z, false)] {
        let h_beta = &invariants.h_beta[axis.index()];

        let mut eta = UpperBound::assert(Rat::zero());
        for (split_index, split) in splits.iter().enumerate() {
            let unconditional = if is_y {
                split.coord(axis_z) == 0
            } else {
                split.coord(axis_x) == 0 || split.coord(axis_y) == 0
            };
            if !unconditional {
                continue;
            }
            let weight = paired_weight(split_index, split)?;
            if weight.is_zero() {
                continue;
            }
            let child_beta = &beta[child_index(*split)?][axis.index()];
            let entropy = entropy_upper(child_beta, precision)?;
            eta = eta.add(&entropy.scale_nonnegative(&weight)?);
        }
        let group_axis = if is_y { axis_y } else { axis_z };
        for value in domain.coordinate_values(group_axis) {
            let mut weight_total = Rat::zero();
            let mut numerator = vec![Rat::zero(); child_width];
            for (split_index, split) in splits.iter().enumerate() {
                // The ordered pair: Y selects on Z, Z selects on X and Y.
                let selected = if is_y {
                    split.coord(axis_y) == value && split.coord(axis_z) > 0
                } else {
                    split.coord(axis_x) > 0
                        && split.coord(axis_y) > 0
                        && split.coord(axis_z) == value
                };
                if !selected {
                    continue;
                }
                let weight = paired_weight(split_index, split)?;
                if weight.is_zero() {
                    continue;
                }
                weight_total = &weight_total + &weight;
                let child_beta = &beta[child_index(*split)?][axis.index()];
                for (slot, entry) in numerator.iter_mut().zip(child_beta.iter()) {
                    *slot = &*slot + &(&weight * entry);
                }
            }
            eta = eta.add(&weighted_conditional_entropy_upper(
                &weight_total,
                &numerator,
                precision,
            )?);
        }
        out[axis.index()] = h_beta.sub_upper(&eta).scale_nonnegative(&scale)?;
    }
    Ok(out)
}

/// A5 for a group, given the whole table (the mixture reused by A12/A13).
fn group_split_mixture_at(
    keys: &[GroupKey],
    beta: &[[Vec<Rat>; 3]],
    level: Level,
    shape: Shape,
    alpha: &[Rat],
    coordinate: Coordinate,
) -> CoreResult<Vec<Rat>> {
    let support = full_support(level);
    let child_level = level.child()?;
    let child_support = full_support(child_level);
    let splits = shape.splits()?;
    let index_of = |shape: Shape| -> CoreResult<usize> {
        keys.iter()
            .position(|key| key.level == child_level && key.shape == shape)
            .ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "a child group is missing")
                    .equation("§3.2")
            })
    };
    let mut position_of: BTreeMap<Vec<u8>, usize> = BTreeMap::new();
    for (index, vector) in support.iter().enumerate() {
        position_of.insert(vector.entries().to_vec(), index);
    }
    let mut out = vec![Rat::zero(); support.len()];
    for (split_index, split) in splits.iter().enumerate() {
        let weight = alpha.get(split_index).cloned().unwrap_or_else(Rat::zero);
        if weight.is_zero() {
            continue;
        }
        let complement = shape.complement(*split)?;
        let left = &beta[index_of(*split)?][coordinate.index()];
        let right = &beta[index_of(complement)?][coordinate.index()];
        for (li, lv) in left.iter().enumerate() {
            if lv.is_zero() {
                continue;
            }
            let Some(lvec) = child_support.get(li) else {
                continue;
            };
            for (ri, rv) in right.iter().enumerate() {
                if rv.is_zero() {
                    continue;
                }
                let Some(rvec) = child_support.get(ri) else {
                    continue;
                };
                let mut joined = lvec.entries().to_vec();
                joined.extend_from_slice(rvec.entries());
                if let Some(target) = position_of.get(&joined) {
                    out[*target] = &out[*target] + &(&weight * &(lv * rv));
                }
            }
        }
    }
    Ok(out)
}

/// `lower(E_ℓ)` over groups: S3 of `0007_spec.md` §5.4.
///
/// ```text
/// E_ℓ = Σ_(r=1..6) min { Σ_s M(ℓ,s) A^(r) Q_X(ℓ, s, π_r(X)),
///                        Σ_s M(ℓ,s) A^(r) Q_Y(ℓ, s, π_r(Y), π_r(Z)),
///                        Σ_s M(ℓ,s) A^(r) Q_Z(ℓ, s, π_r(Z)) }
/// ```
///
/// The sum over shapes is **inside** the minimum and the minimum is per region,
/// which is the same shape the general evaluator has: it accumulates per-region
/// sums across every node of the level before taking any minimum.
///
/// # Errors
///
/// Propagates domain, block, and bound failures.
pub fn group_e_level(
    certificate: &SymmetricCertificate,
    masses: &[Rat],
    beta: &[[Vec<Rat>; 3]],
    blocks: &[MaxEntropyBlock],
    level: Level,
    precision: Precision,
) -> CoreResult<LowerBound> {
    let keys = groups(certificate.level);
    let block_of = block_keys(certificate.level);
    let mut sums = vec![
        [
            LowerBound::assert(Rat::zero()),
            LowerBound::assert(Rat::zero()),
            LowerBound::assert(Rat::zero()),
        ];
        6
    ];
    for (index, key) in keys.iter().enumerate() {
        if key.level != level || key.shape.is_zero_shape() || level.get() < 3 {
            continue;
        }
        let GroupPayload::Branching {
            alpha,
            region_weights,
        } = &certificate.groups[index]
        else {
            continue;
        };
        let block_index = block_of
            .iter()
            .position(|candidate| {
                candidate.is_some_and(|c| c.level == key.level && c.shape == key.shape)
            })
            .ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "a group block is missing")
                    .equation("§3.4")
            })?;
        let block = &blocks[block_index];
        // A14 scales every term by m_T A_T^(r), and A_T is a distribution, so a
        // group contributes nothing exactly when its mass is zero. The general
        // path returns before consulting the block in that case
        // (`evaluate.rs`: "a zero-weight region contributes nothing and its
        // block is not consulted"), and its `e_level` still pops the block, so a
        // malformed block on a zero-mass node is *accepted* there.
        //
        // Hoisting the invariants moved `block.certify` ahead of the per-region
        // `scale.is_zero()` guard that used to cover this, which would have made
        // the symmetric path reject what the general path accepts. §5.1 relates
        // them by an equality, so that is a defect and not a stricter check.
        if masses[index].is_zero() {
            continue;
        }
        // Once per group, not once per region: see `GroupInvariants`.
        let invariants =
            GroupInvariants::build(&keys, beta, level, key.shape, alpha, block, precision)?;
        for region in Region::all() {
            let contributions = group_e_interior_one(
                &keys,
                beta,
                level,
                key.shape,
                alpha,
                region_weights,
                &masses[index],
                region,
                &invariants,
                precision,
            )?;
            let region_index = usize::from(region.get() - 1);
            for coordinate in Coordinate::ALL {
                sums[region_index][coordinate.index()] =
                    sums[region_index][coordinate.index()].add(&contributions[coordinate.index()]);
            }
        }
    }
    let mut total = LowerBound::assert(Rat::zero());
    for region_sums in sums {
        let [x, y, z] = region_sums;
        total = total.add(&x.min(y).min(z));
    }
    Ok(total)
}

/// `lower(E_G)` over groups: A8–A11 with the root's single `α`.
///
/// The root is not a group (§3.3): its payload is `certificate.root` and its
/// block is `blocks[0]`, shared by all six regions because a symmetric point
/// gives them identical blocks. A11 still sums six regional terms weighted by
/// `A_G^(r)`, and each depends on the region through `π_r` alone.
///
/// # Errors
///
/// Propagates domain, block, and bound failures.
pub fn group_e_root(
    certificate: &SymmetricCertificate,
    beta: &[[Vec<Rat>; 3]],
    blocks: &[MaxEntropyBlock],
    precision: Precision,
) -> CoreResult<LowerBound> {
    let keys = groups(certificate.level);
    let level = certificate.level;
    let support = full_support(level);
    let GroupPayload::Branching {
        alpha,
        region_weights,
    } = &certificate.root
    else {
        return Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "the root must be a branching group",
        )
        .equation("§3.3"));
    };
    let block = blocks.first().ok_or_else(|| {
        CoreError::new(ErrorCode::CountMismatch, "the root block is missing").equation("§3.4")
    })?;
    let domain = ShapeDomain::full(level);
    let mut top = Shape::enumerate(level);
    top.sort_by_key(|shape: &Shape| shape.canonical_key());
    let child_index = |shape: Shape| -> CoreResult<usize> {
        keys.iter()
            .position(|key| key.level == level && key.shape == shape)
            .ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "a root child group is missing")
                    .equation("§3.2")
            })
    };

    // The root is roughly half of all entropy work at every level, and none of
    // the A3 hoist reached it. Three quantities here do not depend on the
    // region: `H(alpha)` and the block's `H^max` outright, and the mixture,
    // which sums over *all* shapes and so varies only with the coordinate. The
    // six regions permute onto three coordinates, so the mixture's entropy was
    // twelve evaluations of three distinct values.
    //
    // Not hoisted: `eta`. Its Y branch selects on the ordered pair
    // `(pi_r(Y), pi_r(Z))` and is genuinely six-way distinct -- that ordering is
    // the defect `docs/experiments/omega-l3.md` records as caught, and a
    // symmetric-looking "both branches are 2x redundant" refactor would put it
    // back.
    let visited: Vec<Region> = Region::all()
        .into_iter()
        .filter(|region| {
            region_weights
                .get(usize::from(region.get() - 1))
                .is_some_and(|weight| !weight.is_zero())
        })
        .collect();

    let before = mm_rat::log2::evaluations();
    let h_alpha = entropy_lower(alpha, precision)?;
    let h_max = block.certify(&domain, alpha, precision)?;
    let cost_alpha = mm_rat::log2::evaluations() - before;

    let mut h_marginal = [
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
    ];
    let mut h_mixture = h_marginal.clone();
    let mut cost_marginal = [0u64; 3];
    let mut cost_mixture = [0u64; 3];
    // Only the coordinates the visited regions actually reach. Computing all
    // three unconditionally would evaluate mixtures nothing reads, which is not
    // just wasted work: it would put evaluations into the count that no checker
    // performs, and the reported figure has to bound a checker, not exceed it.
    let mut needs_marginal = [false; 3];
    let mut needs_mixture = [false; 3];
    for region in &visited {
        needs_marginal[region.permute(Coordinate::X).index()] = true;
        needs_mixture[region.permute(Coordinate::Y).index()] = true;
        needs_mixture[region.permute(Coordinate::Z).index()] = true;
    }
    for axis in Coordinate::ALL {
        if needs_marginal[axis.index()] {
            let before = mm_rat::log2::evaluations();
            let marginal_x = MaxEntropyBlock::marginal(&domain, alpha, axis)?;
            h_marginal[axis.index()] = entropy_lower(&marginal_x, precision)?;
            cost_marginal[axis.index()] = mm_rat::log2::evaluations() - before;
        }
        if !needs_mixture[axis.index()] {
            continue;
        }
        let before = mm_rat::log2::evaluations();
        let mut mixture = vec![Rat::zero(); support.len()];
        for (shape, w) in top.iter().zip(alpha.iter()) {
            if w.is_zero() {
                continue;
            }
            let child_beta = &beta[child_index(*shape)?][axis.index()];
            for (slot, entry) in mixture.iter_mut().zip(child_beta.iter()) {
                *slot = &*slot + &(w * entry);
            }
        }
        h_mixture[axis.index()] = entropy_lower(&mixture, precision)?;
        cost_mixture[axis.index()] = mm_rat::log2::evaluations() - before;
    }

    // What a checker without the hoist performs, minus what was performed here.
    // Counted from the regions actually visited rather than assumed to be six,
    // because a zero-weight region consults nothing.
    let mut needed = 0u64;
    for region in &visited {
        needed += cost_alpha;
        needed += cost_marginal[region.permute(Coordinate::X).index()];
        needed += cost_mixture[region.permute(Coordinate::Y).index()];
        needed += cost_mixture[region.permute(Coordinate::Z).index()];
    }
    let performed =
        cost_alpha + cost_marginal.iter().sum::<u64>() + cost_mixture.iter().sum::<u64>();
    mm_rat::log2::charge_elided_evaluations(needed.saturating_sub(performed));

    let mut total = LowerBound::assert(Rat::zero());
    for region in Region::all() {
        let region_index = usize::from(region.get() - 1);
        let weight = region_weights
            .get(region_index)
            .cloned()
            .unwrap_or_else(Rat::zero);
        if weight.is_zero() {
            // A11 weights by A_G^(r); a zero weight consults no block.
            continue;
        }
        let axis_x = region.permute(Coordinate::X);
        let axis_y = region.permute(Coordinate::Y);
        let axis_z = region.permute(Coordinate::Z);

        // Term 1: H((alpha)_X) + H(alpha) - H^max_D(alpha).
        let term1 = h_marginal[axis_x.index()].add(&h_alpha).sub_upper(&h_max);

        let mut term_bounds = Vec::with_capacity(2);
        for (axis, is_y) in [(axis_y, true), (axis_z, false)] {
            let h_mixture = &h_mixture[axis.index()];

            let mut eta = UpperBound::assert(Rat::zero());
            for (shape, w) in top.iter().zip(alpha.iter()) {
                let unconditional = if is_y {
                    shape.coord(axis_z) == 0
                } else {
                    shape.coord(axis_x) == 0 || shape.coord(axis_y) == 0
                };
                if unconditional && !w.is_zero() {
                    let child_beta = &beta[child_index(*shape)?][axis.index()];
                    let entropy = entropy_upper(child_beta, precision)?;
                    eta = eta.add(&entropy.scale_nonnegative(w)?);
                }
            }
            let group_axis = if is_y { axis_y } else { axis_z };
            for value in domain.coordinate_values(group_axis) {
                let mut weight_total = Rat::zero();
                let mut numerator = vec![Rat::zero(); support.len()];
                for (shape, w) in top.iter().zip(alpha.iter()) {
                    let selected = if is_y {
                        shape.coord(axis_y) == value && shape.coord(axis_z) > 0
                    } else {
                        shape.coord(axis_x) > 0
                            && shape.coord(axis_y) > 0
                            && shape.coord(axis_z) == value
                    };
                    if !selected || w.is_zero() {
                        continue;
                    }
                    weight_total = &weight_total + w;
                    let child_beta = &beta[child_index(*shape)?][axis.index()];
                    for (slot, entry) in numerator.iter_mut().zip(child_beta.iter()) {
                        *slot = &*slot + &(w * entry);
                    }
                }
                eta = eta.add(&weighted_conditional_entropy_upper(
                    &weight_total,
                    &numerator,
                    precision,
                )?);
            }
            term_bounds.push(h_mixture.sub_upper(&eta));
        }
        let mut result = term1;
        for bound in term_bounds {
            result = result.min(bound);
        }
        total = total.add(&result.scale_nonnegative(&weight)?);
    }
    Ok(total)
}

/// The full A20 directed bounds from a symmetric certificate, **without
/// expanding it** (`0007_spec.md` §4).
///
/// Validate every group's free variables against its A.2 domain (§3.3).
///
/// The general evaluator does this in `TrackATree::validate_domains` before any
/// arithmetic. Without the same pass here the two checkers disagree about what
/// is *acceptable*, and §5.1 states their relationship as an equality: a
/// symmetric certificate whose region weights sum to six was accepted with
/// `omega_min = 0` where the general path returned `bad_simplex`. A checker that
/// accepts `ω ≤ 0` is not a weaker checker, it is a broken one.
///
/// The kind is derived from the group's position, so a payload whose variant
/// disagrees with what its position implies is `bad_path` here rather than being
/// absorbed by a `continue` somewhere downstream (§3.3, §5.2).
///
/// Errors name the group's `(ℓ,s)` and not a node path. A group at `ℓ*=4` covers
/// up to 145,800 node positions and naming one of them would be arbitrary.
fn validate_group_domains(certificate: &SymmetricCertificate) -> CoreResult<()> {
    let keys = mm_schema::symmetric::groups(certificate.level);
    if certificate.groups.len() != keys.len() {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the group count disagrees with the instance",
        )
        .equation("§3.3")
        .value(format!(
            "{} supplied, {} required",
            certificate.groups.len(),
            keys.len()
        )));
    }

    let mut top = Shape::enumerate(certificate.level);
    top.sort_by_key(|shape: &Shape| shape.canonical_key());
    let GroupPayload::Branching {
        region_weights,
        alpha,
    } = &certificate.root
    else {
        return Err(
            CoreError::new(ErrorCode::BadPath, "the root must be branching").equation("§3.3"),
        );
    };
    a2::branching(region_weights, alpha, top.len()).map_err(|error| error.value("root"))?;

    for (key, payload) in keys.iter().zip(certificate.groups.iter()) {
        let where_ = format!("group l={} s={:?}", key.level.get(), key.shape);
        let decorate = |error: CoreError| error.value(where_.clone());
        match (key.shape.is_zero_shape(), key.level.get(), payload) {
            (true, _, GroupPayload::ZeroShape { beta }) => {
                let coordinate = key.shape.first_nonzero_coord().ok_or_else(|| {
                    decorate(
                        CoreError::new(ErrorCode::BadPath, "a zero-shape group is all zero")
                            .equation("A.9"),
                    )
                })?;
                let vectors = support_vectors(key.shape.level(), key.shape.coord(coordinate))?;
                a2::distribution(beta, vectors.len(), "beta must cover its support domain")
                    .map_err(decorate)?;
            }
            (false, 2, GroupPayload::LevelTwo { mu }) => {
                a2::level_two_mu(mu).map_err(decorate)?;
            }
            (
                false,
                _,
                GroupPayload::Branching {
                    region_weights,
                    alpha,
                },
            ) => {
                let splits = key.shape.splits()?;
                a2::branching(region_weights, alpha, splits.len()).map_err(decorate)?;
            }
            _ => {
                return Err(decorate(
                    CoreError::new(
                        ErrorCode::BadPath,
                        "a group payload disagrees with the kind its position implies",
                    )
                    .equation("§3.3"),
                ));
            }
        }
    }
    Ok(())
}

/// §4 is explicit that `expand` must not be a precondition of checking: at
/// `ℓ* = 4` the expansion is the 1,552,339-node object the encoding exists to
/// avoid. Nothing in this path materializes it.
///
/// # Errors
///
/// Returns [`ErrorCode::CountMismatch`] when the group or block arrays disagree
/// with the instance, and propagates evaluation failures.
pub fn group_evaluate_bounds(
    certificate: &SymmetricCertificate,
    precision: Precision,
) -> CoreResult<OmegaBounds> {
    validate_group_domains(certificate)?;
    let required_blocks = mm_schema::symmetric::block_count(certificate.level);
    if certificate.blocks.len() != required_blocks {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the group block count disagrees with the instance",
        )
        .equation("§3.4")
        .value(format!(
            "{} supplied, {required_blocks} required",
            certificate.blocks.len()
        )));
    }
    let blocks: Vec<MaxEntropyBlock> = certificate
        .blocks
        .iter()
        .map(|block| MaxEntropyBlock {
            y: block.y.clone(),
            lambda0: block.lambda0.clone(),
            lambda_x: block.lambda_x.clone(),
            lambda_y: block.lambda_y.clone(),
            lambda_z: block.lambda_z.clone(),
            epsilon: block.epsilon.clone(),
        })
        .collect();

    let masses = group_masses(certificate)?;
    let beta = group_beta_table(certificate)?;

    let e_root = group_e_root(certificate, &beta, &blocks, precision)?;
    let e_two = group_e_level_two(certificate, &masses, precision)?;
    let mut e_interior = LowerBound::assert(Rat::zero());
    for current in 3..=certificate.level.get() {
        let this = Level::new(current)?;
        e_interior = e_interior.add(&group_e_level(
            certificate,
            &masses,
            &beta,
            &blocks,
            this,
            precision,
        )?);
    }
    let e_total = e_root.add(&e_two).add(&e_interior);
    let m_total = group_m_total(certificate, &masses, certificate.q, precision)?;

    let q_plus_two = Rat::from(u64::from(certificate.q) + 2);
    let scale = Rat::from(1u64 << (certificate.level.get() - 1));
    let requirement = log2_upper(&q_plus_two, precision)?.scale_nonnegative(&scale)?;

    Ok(OmegaBounds {
        e_root,
        e_two,
        e_interior,
        e_total,
        m_total,
        requirement,
    })
}
