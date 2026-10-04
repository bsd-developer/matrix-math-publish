//! The exact directed Track A evaluator (spec §7.2, A.6, A.8–A.10).
//!
//! Every quantity is evaluated as a **directed** bound in the conservative
//! direction §7.2 fixes, so an accepted certificate implies the real A21
//! inequality even though `log2` and `H` are irrational.
//!
//! The final check is
//!
//! ```text
//! lower(E_total) + lower(M_total) * Ω >= 2^(ℓ*-1) * upper(log2(q+2))
//! ```
//!
//! with `Ω >= 0` validated first, because the term `lower(M_total) * Ω` uses the
//! §7.2 monotonic shortcut and that is unsound for a signed multiplier.

use crate::domain::{ShapeDomain, SupportVector};
use crate::maxent::MaxEntropyBlock;
use crate::tree::{NodeVariables, TrackATree, TreeNode};
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::level::Level;
use mm_core::path::NodeKind;
use mm_core::region::{Coordinate, Region};
use mm_rat::Rat;
use mm_rat::bounds::{LowerBound, UpperBound};
use mm_rat::entropy::{entropy_lower, entropy_upper};
use mm_rat::log2::{Precision, log2_lower, log2_upper};

extern crate alloc;
use alloc::format;
use alloc::vec::Vec;

/// Every vector in `{0,1,2}^(2^(ℓ-1))`, in lexicographic order.
///
/// The mixtures of A.6 combine `β` distributions whose totals differ, so they
/// live on this whole set rather than on any single `C_(ℓ,a)`.
///
/// Memoized per support length (`0008_spec.md` §6.2 R2): the enumeration is a
/// pure function of the level, and `split_mixture` alone asked for it twice
/// per invocation — at `ℓ*=4` a 6,561-element sort rebuilt on the order of
/// `10^5` times. The cache holds deterministic domain data only.
#[must_use]
pub fn full_support(level: Level) -> &'static [SupportVector] {
    static CACHE: [std::sync::OnceLock<Vec<SupportVector>>; 17] =
        [const { std::sync::OnceLock::new() }; 17];
    let length = usize::from(level.support_len());
    match CACHE.get(length) {
        Some(slot) => slot.get_or_init(|| build_full_support(length)),
        // Unreachable under §0.2's `2 <= l* <= 4`, whose largest support
        // length is 8; kept total rather than panicking.
        None => Box::leak(Box::new(build_full_support(length))),
    }
}

fn build_full_support(length: usize) -> Vec<SupportVector> {
    let mut out: Vec<Vec<u8>> = alloc::vec![Vec::new()];
    for _ in 0..length {
        let mut next = Vec::with_capacity(out.len() * 3);
        for prefix in &out {
            for entry in 0u8..=2 {
                let mut extended = prefix.clone();
                extended.push(entry);
                next.push(extended);
            }
        }
        out = next;
    }
    out.sort();
    out.into_iter()
        .filter_map(|entries| SupportVector::from_entries(entries).ok())
        .collect()
}

/// The certified upper bound for `H_D^max` at one occurrence, plus the exact
/// `ρ` it certifies (§7.4).
#[derive(Clone, Debug)]
pub struct MaxEntropyUse {
    /// The certified upper bound.
    pub bound: UpperBound,
}

/// The directed evaluation of one instance (A.20, A.21).
#[derive(Clone, Debug)]
pub struct OmegaClaim {
    /// A lower bound for `E_total`.
    pub e_total: LowerBound,
    /// A lower bound for `M_total`.
    pub m_total: LowerBound,
    /// The right-hand side `2^(ℓ*-1) * upper(log2(q+2))`.
    pub requirement: UpperBound,
    /// The claimed `Ω`.
    pub omega: Rat,
}

impl OmegaClaim {
    /// The human-readable claim used in reports and manifests.
    #[must_use]
    pub fn statement(&self) -> alloc::string::String {
        format!("omega <= {}", self.omega)
    }
}

/// Evaluate the directed local matrix sizes of one leaf (A18, A19).
///
/// Returns a lower bound per coordinate, in `X, Y, Z` order.
///
/// # Errors
///
/// Propagates domain and bound failures.
pub fn local_sizes(
    tree: &TrackATree,
    node: &TreeNode,
    mass: &Rat,
    precision: Precision,
) -> CoreResult<[LowerBound; 3]> {
    let q = Rat::from(u64::from(tree.instance().q()));
    let log_q = log2_lower(&q, precision)?;
    let shape = node.shape.ok_or_else(|| {
        CoreError::new(ErrorCode::BadPath, "a leaf must have a shape").equation("A.9")
    })?;
    let zero = LowerBound::assert(Rat::zero());
    match &node.variables {
        NodeVariables::ZeroShape { .. } => {
            // A18: only the first zero coordinate carries a local size.
            let w0 = shape.first_zero_coord().ok_or_else(|| {
                CoreError::new(
                    ErrorCode::BadPath,
                    "a zero-shape node has a zero coordinate",
                )
                .equation("A.9")
            })?;
            let w1 = shape.first_nonzero_coord().ok_or_else(|| {
                CoreError::new(
                    ErrorCode::BadPath,
                    "a zero-shape node has a positive coordinate",
                )
                .equation("A.9")
            })?;
            let beta = tree.beta(node, w1)?;
            let values: Vec<Rat> = beta.iter().map(|(_, value)| value.clone()).collect();
            let entropy = entropy_lower(&values, precision)?;
            // Σ_L β(L) |{p : L_p = 1}| is exact rational; it weights log2 q.
            let mut ones_weight = Rat::zero();
            for (vector, value) in &beta {
                let count = Rat::from(vector.ones() as u64);
                ones_weight = &ones_weight + &(value * &count);
            }
            let weighted = log_q.scale_nonnegative(&ones_weight)?;
            let inner = entropy.add(&weighted);
            let scaled = inner.scale_nonnegative(mass)?;
            let mut out = [zero.clone(), zero.clone(), zero];
            out[w0.index()] = scaled;
            Ok(out)
        }
        NodeVariables::PositiveLevelTwo { mu } => {
            // A19: the coordinate whose shape entry is 2 gets 2*mu*log2 q; the
            // other two get (1-2mu)*log2 q.
            let two_mu = &Rat::from_integer(2) * mu;
            let rest = &Rat::one() - &two_mu;
            if rest.is_negative() {
                return Err(CoreError::new(
                    ErrorCode::BadSimplex,
                    "1 - 2*mu must be nonnegative, which A.2's domain guarantees",
                )
                .equation("A.19")
                .value(node.path.clone()));
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
        _ => Err(CoreError::new(
            ErrorCode::BadPath,
            "local matrix sizes are defined only at leaves",
        )
        .equation("A.9")
        .value(node.path.clone())),
    }
}

/// Evaluate the directed level-2 retained exponents of one node (A16).
///
/// # Errors
///
/// Propagates bound failures.
pub fn level_two_exponents(
    node: &TreeNode,
    mass: &Rat,
    precision: Precision,
) -> CoreResult<[LowerBound; 3]> {
    let NodeVariables::PositiveLevelTwo { mu } = &node.variables else {
        return Err(CoreError::new(
            ErrorCode::BadPath,
            "A16 applies only to positive level-2 nodes",
        )
        .equation("A.8"));
    };
    let shape = node.shape.ok_or_else(|| {
        CoreError::new(ErrorCode::BadPath, "a level-2 node must have a shape").equation("A.8")
    })?;
    let two_mu = &Rat::from_integer(2) * mu;
    let rest = &Rat::one() - &two_mu;
    // H(mu, mu, 1-2mu) as a directed lower bound.
    let distribution = [mu.clone(), mu.clone(), rest];
    let entropy = entropy_lower(&distribution, precision)?;
    let one = LowerBound::assert(Rat::one());
    let mut out = [
        one.clone().scale_nonnegative(mass)?,
        one.clone().scale_nonnegative(mass)?,
        one.scale_nonnegative(mass)?,
    ];
    for coordinate in Coordinate::ALL {
        if shape.coord(coordinate) == 2 {
            out[coordinate.index()] = entropy.scale_nonnegative(mass)?;
        }
    }
    Ok(out)
}

/// Assemble the final feasibility check (A20, A21, §7.2).
///
/// # Errors
///
/// Returns [`ErrorCode::NegativeOmega`] when `Ω < 0`, and
/// [`ErrorCode::FeasibilityViolated`] when the directed inequality fails.
pub fn check_feasibility(
    tree: &TrackATree,
    e_total: LowerBound,
    m_total: LowerBound,
    omega: &Rat,
    precision: Precision,
) -> CoreResult<OmegaClaim> {
    // §7.2: validate Ω ≥ 0 before multiplying by a lower bound for M_total.
    if omega.is_negative() {
        return Err(CoreError::new(
            ErrorCode::NegativeOmega,
            "a claimed omega must be nonnegative before the monotonic shortcut is used",
        )
        .equation("§7.2")
        .value(format!("{omega}")));
    }
    let instance = tree.instance();
    let q_plus_two = Rat::from(u64::from(instance.q()) + 2);
    let log_term = log2_upper(&q_plus_two, precision)?;
    let scale = Rat::from(instance.constraint_scale());
    let requirement = log_term.scale_nonnegative(&scale)?;

    let contribution = m_total.scale_nonnegative(omega)?;
    let left = e_total.add(&contribution);

    if left.value() < requirement.value() {
        return Err(CoreError::new(
            ErrorCode::FeasibilityViolated,
            "the directed A21 inequality does not hold",
        )
        .equation("A21")
        .value(format!("lower(E)+lower(M)*omega = {}", left.value()))
        .value(format!("requirement = {}", requirement.value())));
    }
    Ok(OmegaClaim {
        e_total,
        m_total,
        requirement,
        omega: omega.clone(),
    })
}

/// Sum the directed local sizes over every leaf and take the coordinate minimum
/// (A20).
///
/// # Errors
///
/// Propagates evaluation failures.
pub fn m_total(tree: &TrackATree, precision: Precision) -> CoreResult<LowerBound> {
    let mut totals = [
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
    ];
    for (position, node) in tree.nodes().iter().enumerate() {
        if node.kind.has_children() {
            continue;
        }
        let mass = tree
            .masses()
            .get(position)
            .cloned()
            .unwrap_or_else(Rat::zero);
        let sizes = local_sizes(tree, node, &mass, precision)?;
        for coordinate in Coordinate::ALL {
            totals[coordinate.index()] = totals[coordinate.index()].add(&sizes[coordinate.index()]);
        }
    }
    // §7.2: the lower bound of a minimum is the minimum of the lower bounds.
    let [x, y, z] = totals;
    Ok(x.min(y).min(z))
}

/// Sum the directed level-2 exponents and take the coordinate minimum (A17).
///
/// # Errors
///
/// Propagates evaluation failures.
pub fn e_level_two(tree: &TrackATree, precision: Precision) -> CoreResult<LowerBound> {
    let mut totals = [
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
    ];
    for (position, node) in tree.nodes().iter().enumerate() {
        if node.kind != NodeKind::PositiveLevelTwo {
            continue;
        }
        let mass = tree
            .masses()
            .get(position)
            .cloned()
            .unwrap_or_else(Rat::zero);
        let exponents = level_two_exponents(node, &mass, precision)?;
        for coordinate in Coordinate::ALL {
            totals[coordinate.index()] =
                totals[coordinate.index()].add(&exponents[coordinate.index()]);
        }
    }
    let [x, y, z] = totals;
    Ok(x.min(y).min(z))
}

/// The regions in canonical numeric order (§5.1).
#[must_use]
pub fn regions() -> [Region; 6] {
    Region::all()
}

/// The `β` of a level-2 leaf, spread over the whole support space.
///
/// A.6's mixtures combine `β` distributions whose totals differ, so they must
/// share an index set; that set is `{0,1,2}^(2^(ℓ-1))`.
///
/// # Errors
///
/// Propagates `β` construction failures.
fn beta_on_full_support(
    tree: &TrackATree,
    node: &TreeNode,
    coordinate: Coordinate,
    support: &[SupportVector],
) -> CoreResult<Vec<Rat>> {
    let sparse = tree.beta(node, coordinate)?;
    let mut out = alloc::vec![Rat::zero(); support.len()];
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
        if let Some(slot) = out.get_mut(position) {
            *slot = &*slot + &value;
        }
    }
    Ok(out)
}

/// Accumulate `weight * distribution` into `target`.
fn accumulate(target: &mut [Rat], weight: &Rat, distribution: &[Rat]) {
    for (slot, value) in target.iter_mut().zip(distribution.iter()) {
        *slot = &*slot + &(weight * value);
    }
}

/// The §7.6 guarded conditional mixture, as a directed **upper** bound on its
/// weighted entropy.
///
/// `weightedConditionalEntropy(weight, numerator) = 0` when `weight = 0`;
/// division by zero is never evaluated.
///
/// # Errors
///
/// Propagates bound failures.
pub(crate) fn weighted_conditional_entropy_upper(
    weight: &Rat,
    numerator: &[Rat],
    precision: Precision,
) -> CoreResult<UpperBound> {
    if weight.is_zero() {
        return Ok(UpperBound::assert(Rat::zero()));
    }
    let normalized: Vec<Rat> = numerator
        .iter()
        .map(|value| value.checked_div(weight))
        .collect::<CoreResult<Vec<Rat>>>()?;
    let entropy = entropy_upper(&normalized, precision)?;
    entropy.scale_nonnegative(weight)
}

/// The root children in canonical order for one region, paired with their
/// `α` weights (A.1, A.2).
///
/// # Errors
///
/// Propagates domain failures.
fn root_children(tree: &TrackATree, region: Region) -> CoreResult<Vec<(&TreeNode, Rat)>> {
    let root = tree.nodes().first().ok_or_else(|| {
        CoreError::new(ErrorCode::BadPath, "the tree has no root").equation("§5.2")
    })?;
    let NodeVariables::Root { alpha, .. } = &root.variables else {
        return Err(
            CoreError::new(ErrorCode::BadPath, "node zero must be the root").equation("§5.2"),
        );
    };
    let domain = tree.alpha_domain(root)?;
    let distribution = alpha.get(usize::from(region.get() - 1)).ok_or_else(|| {
        CoreError::new(ErrorCode::CountMismatch, "alpha is missing a region entry").equation("A.2")
    })?;
    let mut out = Vec::with_capacity(domain.len());
    // Scan the root's own children, never the whole tree: at `ℓ*=4` the old
    // whole-tree `.find` walked 1,552,339 nodes per shape per region
    // (`0008_spec.md` §6.2 R3; the same lesson `child_of` already carries).
    let children = tree.children_of(root.index);
    for (index, shape) in domain.shapes().iter().enumerate() {
        let child = children
            .iter()
            .filter_map(|child_index| tree.nodes().get(usize::try_from(*child_index).ok()?))
            .find(|node| {
                node.parent == Some(root.index)
                    && node.region == Some(region)
                    && node.shape == Some(*shape)
            })
            .ok_or_else(|| {
                CoreError::new(ErrorCode::BadPath, "a root child is missing from the tree")
                    .equation("§5.2")
            })?;
        let weight = distribution.get(index).cloned().unwrap_or_else(Rat::zero);
        out.push((child, weight));
    }
    Ok(out)
}

/// The retained exponent contribution of the root for one region (A8-A11).
///
/// `Y` and `Z` below mean `π_r(Y)` and `π_r(Z)`: A.6 says the construction for
/// region `r` is the region-1 construction after relabelling the coordinates by
/// `π_r` and using child region `r`.
///
/// # Errors
///
/// Propagates domain, bound, and maximum-entropy failures.
fn e_root_region(
    tree: &TrackATree,
    region: Region,
    block: &MaxEntropyBlock,
    beta: &[[Vec<Rat>; 3]],
    precision: Precision,
) -> CoreResult<LowerBound> {
    let level = tree.instance().level();
    let support = full_support(level);
    let children = root_children(tree, region)?;
    let root = tree.nodes().first().ok_or_else(|| {
        CoreError::new(ErrorCode::BadPath, "the tree has no root").equation("§5.2")
    })?;
    let domain = tree.alpha_domain(root)?;
    let NodeVariables::Root { alpha, .. } = &root.variables else {
        return Err(
            CoreError::new(ErrorCode::BadPath, "node zero must be the root").equation("§5.2"),
        );
    };
    let region_alpha = alpha.get(usize::from(region.get() - 1)).ok_or_else(|| {
        CoreError::new(ErrorCode::CountMismatch, "alpha is missing a region entry").equation("A.2")
    })?;

    // The relabelled coordinates for this region (§5.1).
    let axis_x = region.permute(Coordinate::X);
    let axis_y = region.permute(Coordinate::Y);
    let axis_z = region.permute(Coordinate::Z);

    // --- Term 1: H((alpha)_X) - P_D(alpha) = H((alpha)_X) - H^max_D + H(alpha).
    let marginal_x = MaxEntropyBlock::marginal(&domain, region_alpha, axis_x)?;
    let h_marginal = entropy_lower(&marginal_x, precision)?;
    let h_alpha = entropy_lower(region_alpha, precision)?;
    let h_max = block.certify(&domain, region_alpha, precision)?;
    let term1 = h_marginal.add(&h_alpha).sub_upper(&h_max);

    // --- Terms 2 and 3: H(betabar_W) - eta_W for W in {Y, Z}.
    let mut term_bounds = Vec::with_capacity(2);
    for (axis, is_y) in [(axis_y, true), (axis_z, false)] {
        // betabar_(G,W,*,*,*) = sum_s alpha(s) beta_(G[s,r],W).
        let mut mixture = alloc::vec![Rat::zero(); support.len()];
        for (child, weight) in &children {
            if weight.is_zero() {
                continue;
            }
            let child_beta = beta_of(tree, beta, child, axis);
            accumulate(&mut mixture, weight, &child_beta);
        }
        let h_mixture = entropy_lower(&mixture, precision)?;

        // eta_W: the unconditional part plus the conditional mixtures (A8, A9).
        let mut eta = UpperBound::assert(Rat::zero());
        for (child, weight) in &children {
            let shape = child.shape.ok_or_else(|| {
                CoreError::new(ErrorCode::BadPath, "a root child must have a shape").equation("A.6")
            })?;
            let unconditional = if is_y {
                // A8: shapes with s_{pi(Z)} = 0.
                shape.coord(axis_z) == 0
            } else {
                // A9: shapes with s_{pi(X)} = 0 or s_{pi(Y)} = 0.
                shape.coord(axis_x) == 0 || shape.coord(axis_y) == 0
            };
            if unconditional && !weight.is_zero() {
                let child_beta = beta_of(tree, beta, child, axis);
                let entropy = entropy_upper(&child_beta, precision)?;
                eta = eta.add(&entropy.scale_nonnegative(weight)?);
            }
        }
        // The conditional families, indexed by the coordinate value.
        let group_axis = if is_y { axis_y } else { axis_z };
        for value in domain.coordinate_values(group_axis) {
            let mut weight_total = Rat::zero();
            let mut numerator = alloc::vec![Rat::zero(); support.len()];
            for (child, weight) in &children {
                let shape = child.shape.ok_or_else(|| {
                    CoreError::new(ErrorCode::BadPath, "a root child must have a shape")
                        .equation("A.6")
                })?;
                let selected = if is_y {
                    // A8: s_{pi(Y)} = j and s_{pi(Z)} > 0.
                    shape.coord(axis_y) == value && shape.coord(axis_z) > 0
                } else {
                    // A9: s_{pi(X)} > 0, s_{pi(Y)} > 0, s_{pi(Z)} = k.
                    shape.coord(axis_x) > 0
                        && shape.coord(axis_y) > 0
                        && shape.coord(axis_z) == value
                };
                if !selected || weight.is_zero() {
                    continue;
                }
                weight_total = &weight_total + weight;
                let child_beta = beta_of(tree, beta, child, axis);
                accumulate(&mut numerator, weight, &child_beta);
            }
            // §7.6: a zero weight contributes exactly zero and never divides.
            let contribution =
                weighted_conditional_entropy_upper(&weight_total, &numerator, precision)?;
            eta = eta.add(&contribution);
        }
        term_bounds.push(h_mixture.sub_upper(&eta));
    }

    let mut result = term1;
    for bound in term_bounds {
        result = result.min(bound);
    }
    Ok(result)
}

/// The root retained exponent `E_G = Σ_r A_G^(r) E_G^(r)` (A10, A11).
///
/// One maximum-entropy block is consumed per region, in canonical region order,
/// matching §6.5's requirement of one block per occurrence of `H_D^max`.
///
/// # Errors
///
/// Returns [`ErrorCode::CountMismatch`] when the block count is wrong, and
/// propagates evaluation failures.
pub fn e_root(
    tree: &TrackATree,
    blocks: &[MaxEntropyBlock],
    beta: &[[Vec<Rat>; 3]],
    precision: Precision,
) -> CoreResult<LowerBound> {
    if blocks.len() != 6 {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the root needs one maximum-entropy block per region",
        )
        .equation("§6.5")
        .value(format!("{} blocks", blocks.len())));
    }
    let root = tree.nodes().first().ok_or_else(|| {
        CoreError::new(ErrorCode::BadPath, "the tree has no root").equation("§5.2")
    })?;
    let NodeVariables::Root { region_weights, .. } = &root.variables else {
        return Err(
            CoreError::new(ErrorCode::BadPath, "node zero must be the root").equation("§5.2"),
        );
    };
    let mut total = LowerBound::assert(Rat::zero());
    for region in regions() {
        let index = usize::from(region.get() - 1);
        let block = blocks.get(index).ok_or_else(|| {
            CoreError::new(ErrorCode::CountMismatch, "a region block is missing").equation("§6.5")
        })?;
        let weight = region_weights.get(index).ok_or_else(|| {
            CoreError::new(ErrorCode::CountMismatch, "A_G is missing a region entry")
                .equation("A.2")
        })?;
        if weight.is_zero() {
            // A11 weights by A_G^(r); a zero weight contributes nothing and the
            // region's block is not consulted.
            continue;
        }
        let contribution = e_root_region(tree, region, block, beta, precision)?;
        total = total.add(&contribution.scale_nonnegative(weight)?);
    }
    Ok(total)
}

/// The complete directed evaluation of an instance (A20, A21).
///
/// `E_total = E_G + E_2 + Σ_(ℓ=3..ℓ*) E_ℓ`, and
/// `M_total = min_W Σ_(T ∈ Leaves) M_(T,W)`.
///
/// # Errors
///
/// Returns [`ErrorCode::CountMismatch`] when the block count disagrees with the
/// instance, and propagates evaluation failures.
pub fn evaluate(
    tree: &TrackATree,
    blocks: &[MaxEntropyBlock],
    omega: &Rat,
    precision: Precision,
) -> CoreResult<OmegaClaim> {
    let bounds = evaluate_bounds(tree, blocks, precision)?;
    check_feasibility(tree, bounds.e_total, bounds.m_total, omega, precision)
}

/// The directed bounds of A20, without the A21 comparison.
///
/// The producer needs these to *choose* `Ω`; `evaluate` needs them to *check* a
/// claimed one. Separating them means the producer never has to guess a value
/// and then discover the answer by rejection.
#[derive(Clone, Debug)]
pub struct OmegaBounds {
    /// A lower bound for `E_G` (A11).
    pub e_root: LowerBound,
    /// A lower bound for `E_2` (A17).
    pub e_two: LowerBound,
    /// A lower bound for `Σ_(ℓ=3..ℓ*) E_ℓ` (A15).
    pub e_interior: LowerBound,
    /// A lower bound for `E_total`.
    pub e_total: LowerBound,
    /// A lower bound for `M_total`.
    pub m_total: LowerBound,
    /// The right-hand side `2^(ℓ*-1) * upper(log2(q+2))`.
    pub requirement: UpperBound,
}

impl OmegaBounds {
    /// The least `Ω ≥ 0` the directed check accepts, or `None` when no
    /// nonnegative `Ω` does.
    ///
    /// A21 rearranges to `Ω ≥ (requirement - lower(E_total)) / lower(M_total)`,
    /// which is a formula rather than a search whenever `lower(M_total) > 0`.
    /// §7.2's `Ω ≥ 0` restriction is applied here too, so the value returned is
    /// one the version 1 checker actually accepts.
    #[must_use]
    pub fn minimal_omega(&self) -> Option<Rat> {
        let deficit = self.requirement.value() - self.e_total.value();
        if !deficit.is_positive() {
            return Some(Rat::zero());
        }
        let m = self.m_total.value();
        if !m.is_positive() {
            return None;
        }
        deficit.checked_div(m).ok()
    }
}

/// Evaluate `E_total`, `M_total`, and the A21 requirement (A20).
///
/// # Errors
///
/// Returns [`ErrorCode::CountMismatch`] when the block count disagrees with the
/// instance, and propagates evaluation failures.
pub fn evaluate_bounds(
    tree: &TrackATree,
    blocks: &[MaxEntropyBlock],
    precision: Precision,
) -> CoreResult<OmegaBounds> {
    // §6.5: the block count is derived from the instance, never trusted.
    let required = required_block_count(tree);
    if blocks.len() != required {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the maximum-entropy block count disagrees with the instance",
        )
        .equation("§6.5")
        .value(format!("{} supplied, {required} required", blocks.len())));
    }

    // A.5 and A.6 are computed once for the whole tree; A.6's mixtures at the
    // root read the same table.
    let beta = beta_table(tree)?;
    let root_blocks: Vec<MaxEntropyBlock> = blocks.iter().take(6).cloned().collect();
    let e_g = e_root(tree, &root_blocks, &beta, precision)?;
    let e_2 = e_level_two(tree, precision)?;

    let mut interior = LowerBound::assert(Rat::zero());
    let top = tree.instance().level().get();
    if top >= 3 {
        let mut queue: alloc::collections::VecDeque<MaxEntropyBlock> =
            blocks.iter().skip(6).cloned().collect();
        // A20 sums the interior levels from 3 up to ℓ*.
        for value in 3..=top {
            let level = mm_core::level::Level::new(value)?;
            interior = interior.add(&e_level(tree, level, &mut queue, &beta, precision)?);
        }
        if !queue.is_empty() {
            return Err(CoreError::new(
                ErrorCode::CountMismatch,
                "the certificate supplies more maximum-entropy blocks than the instance needs",
            )
            .equation("§6.5")
            .value(format!("{} unused", queue.len())));
        }
    }

    let e_total = e_g.add(&e_2).add(&interior);
    let m_total = m_total(tree, precision)?;
    let instance = tree.instance();
    let q_plus_two = Rat::from(u64::from(instance.q()) + 2);
    let requirement = log2_upper(&q_plus_two, precision)?
        .scale_nonnegative(&Rat::from(instance.constraint_scale()))?;
    Ok(OmegaBounds {
        e_root: e_g,
        e_two: e_2,
        e_interior: interior,
        e_total,
        m_total,
        requirement,
    })
}

/// The child of `parent` with a given shape and region.
fn child_of<'a>(
    tree: &'a TrackATree,
    parent: &TreeNode,
    shape: mm_core::shape::Shape,
    region: Region,
) -> CoreResult<&'a TreeNode> {
    // Only this parent's children, not every node. A.5 calls this once per
    // split per region per coordinate: 258,570 times at l*=4, and scanning
    // 1,552,339 nodes each time is the dominant term in the general evaluator.
    tree.children_of(parent.index)
        .iter()
        .filter_map(|position| tree.nodes().get(*position as usize))
        .find(|node| node.region == Some(region) && node.shape == Some(shape))
        .ok_or_else(|| {
            CoreError::new(ErrorCode::BadPath, "a child named by a split is missing")
                .equation("A.5")
                .value(parent.path.clone())
        })
}

/// A node's preorder position, used to index the `β` table.
///
/// `TrackATree::new` checks that a node's index is its position, so this is the
/// index itself. It was a linear scan, which made every caller O(N).
fn position_of_node(tree: &TrackATree, node: &TreeNode) -> Option<usize> {
    let position = usize::try_from(node.index).ok()?;
    tree.nodes().get(position).map(|_| position)
}

/// The region-`r` split mixture `β_(T,W)^(r)` of A.5.
///
/// `β_(T,W)^(r) = Σ_(u ∈ Split(s_T)) α_T^(r)(u) (β_(T[u,r],W) × β_(T[s_T-u,r],W))`,
/// where `×` concatenates the two child support vectors and multiplies their
/// probabilities.
fn split_mixture(
    tree: &TrackATree,
    node: &TreeNode,
    region_alpha: &[Rat],
    region: Region,
    coordinate: Coordinate,
    beta: &[[Vec<Rat>; 3]],
) -> CoreResult<Vec<Rat>> {
    let shape = node.shape.ok_or_else(|| {
        CoreError::new(ErrorCode::BadPath, "an interior node must have a shape").equation("A.5")
    })?;
    let level = shape.level();
    let support = full_support(level);
    let child_support = full_support(level.child()?);
    let splits = shape.splits()?;

    // Lexicographic order on support vectors *is* base-3 positional order, so
    // the concatenated vector's index is arithmetic:
    // `supportIndex(L1 ++ L2) = supportIndex(L1) * |child| + supportIndex(L2)`
    // (`0007_spec.md` §5.5, where the identity is proved). This replaces the
    // per-call `BTreeMap` over the full support and the per-pair concatenation
    // that dominated the general `ℓ*=4` evaluation (`0008_spec.md` §6.2 R1).
    let width = child_support.len();
    debug_assert_eq!(
        support.len(),
        width * width,
        "the parent support must be the square of the child support (§5.5)"
    );

    let mut out = alloc::vec![Rat::zero(); support.len()];
    for (split_index, split) in splits.iter().enumerate() {
        let weight = region_alpha
            .get(split_index)
            .cloned()
            .unwrap_or_else(Rat::zero);
        if weight.is_zero() {
            continue;
        }
        let complement = shape.complement(*split)?;
        let left = child_of(tree, node, *split, region)?;
        let right = child_of(tree, node, complement, region)?;
        let left_beta = beta_of(tree, beta, left, coordinate);
        let right_beta = beta_of(tree, beta, right, coordinate);
        for (li, lv) in left_beta.iter().enumerate() {
            if lv.is_zero() || li >= width {
                continue;
            }
            for (ri, rv) in right_beta.iter().enumerate() {
                if rv.is_zero() || ri >= width {
                    continue;
                }
                if let Some(slot) = out.get_mut(li * width + ri) {
                    *slot = &*slot + &(&weight * &(lv * rv));
                }
            }
        }
    }
    Ok(out)
}

/// The `β` of a node from the precomputed table.
fn beta_of(
    tree: &TrackATree,
    beta: &[[Vec<Rat>; 3]],
    node: &TreeNode,
    coordinate: Coordinate,
) -> Vec<Rat> {
    position_of_node(tree, node)
        .and_then(|position| beta.get(position))
        .map(|entry| entry[coordinate.index()].clone())
        .unwrap_or_default()
}

/// Every node's `β_(T,W)` on the full support space of its own level (A.4–A.7).
///
/// Indexed by preorder position, then by coordinate. A leaf's `β` comes from A.4
/// or A.7; a positive interior node's is the A.5 split mixture followed by the
/// A.6 region mixture. Preorder puts a parent before its children, so a reverse
/// pass visits every child first.
///
/// # Errors
///
/// Propagates domain and child-lookup failures.
pub fn beta_table(tree: &TrackATree) -> CoreResult<Vec<[Vec<Rat>; 3]>> {
    let nodes = tree.nodes();
    let mut table: Vec<[Vec<Rat>; 3]> =
        alloc::vec![[Vec::new(), Vec::new(), Vec::new()]; nodes.len()];

    for position in (0..nodes.len()).rev() {
        let Some(node) = nodes.get(position) else {
            continue;
        };
        match node.kind {
            // The root carries no β of its own; A.6 mixes its children directly.
            NodeKind::Root => {}
            NodeKind::ZeroShape | NodeKind::PositiveLevelTwo => {
                let level = node.shape.map(|shape| shape.level()).ok_or_else(|| {
                    CoreError::new(ErrorCode::BadPath, "a leaf must have a shape").equation("A.5")
                })?;
                let support = full_support(level);
                for coordinate in Coordinate::ALL {
                    let values = beta_on_full_support(tree, node, coordinate, support)?;
                    if let Some(slot) = table.get_mut(position) {
                        slot[coordinate.index()] = values;
                    }
                }
            }
            NodeKind::PositiveInterior => {
                let NodeVariables::Interior {
                    region_weights,
                    alpha,
                } = &node.variables
                else {
                    return Err(CoreError::new(
                        ErrorCode::BadPath,
                        "a positive interior node must carry A_T and alpha",
                    )
                    .equation("A.2"));
                };
                let level = node.shape.map(|shape| shape.level()).ok_or_else(|| {
                    CoreError::new(ErrorCode::BadPath, "an interior node must have a shape")
                        .equation("A.5")
                })?;
                let width = full_support(level).len();
                for coordinate in Coordinate::ALL {
                    let mut mixed = alloc::vec![Rat::zero(); width];
                    for region in Region::all() {
                        let region_index = usize::from(region.get() - 1);
                        let weight = region_weights
                            .get(region_index)
                            .cloned()
                            .unwrap_or_else(Rat::zero);
                        if weight.is_zero() {
                            continue;
                        }
                        let region_alpha = alpha.get(region_index).ok_or_else(|| {
                            CoreError::new(
                                ErrorCode::CountMismatch,
                                "alpha is missing a region entry",
                            )
                            .equation("A.2")
                        })?;
                        let per_region =
                            split_mixture(tree, node, region_alpha, region, coordinate, &table)?;
                        // A.6: β_(T,W) = Σ_r A_T^(r) β_(T,W)^(r).
                        accumulate(&mut mixed, &weight, &per_region);
                    }
                    if let Some(slot) = table.get_mut(position) {
                        slot[coordinate.index()] = mixed;
                    }
                }
            }
        }
    }
    Ok(table)
}

/// The retained exponents of one positive interior node in one region
/// (A12, A13, A14).
///
/// `X`, `Y`, `Z` below mean `π_r(X)`, `π_r(Y)`, `π_r(Z)`: A.7 says the region-`r`
/// construction is the region-1 construction after relabelling by `π_r`, with
/// the resulting quantities assigned to those same axes.
///
/// # Errors
///
/// Propagates domain, block, and bound failures.
fn e_interior_node(
    tree: &TrackATree,
    node: &TreeNode,
    mass: &Rat,
    region: Region,
    block: &MaxEntropyBlock,
    beta: &[[Vec<Rat>; 3]],
    precision: Precision,
) -> CoreResult<[LowerBound; 3]> {
    let shape = node.shape.ok_or_else(|| {
        CoreError::new(ErrorCode::BadPath, "an interior node must have a shape").equation("A.7")
    })?;
    let splits = shape.splits()?;
    let domain = ShapeDomain::splits(shape)?;
    let NodeVariables::Interior {
        region_weights,
        alpha,
    } = &node.variables
    else {
        return Err(CoreError::new(
            ErrorCode::BadPath,
            "A14 applies only to positive interior nodes",
        )
        .equation("A.7"));
    };
    let region_index = usize::from(region.get() - 1);
    let region_weight = region_weights
        .get(region_index)
        .cloned()
        .unwrap_or_else(Rat::zero);
    let region_alpha = alpha.get(region_index).ok_or_else(|| {
        CoreError::new(ErrorCode::CountMismatch, "alpha is missing a region entry").equation("A.2")
    })?;

    let axis_x = region.permute(Coordinate::X);
    let axis_y = region.permute(Coordinate::Y);
    let axis_z = region.permute(Coordinate::Z);

    // A14 multiplies every term by m_T * A_T^(r).
    let scale = mass * &region_weight;
    let zero = LowerBound::assert(Rat::zero());
    let mut out = [zero.clone(), zero.clone(), zero];
    if scale.is_zero() {
        // A zero-weight region contributes nothing and its block is not consulted.
        return Ok(out);
    }

    // A14 first term: H((α_T^(r))_X) - P_(Split(s_T))(α_T^(r)).
    let marginal = MaxEntropyBlock::marginal(&domain, region_alpha, axis_x)?;
    let h_marginal = entropy_lower(&marginal, precision)?;
    let h_alpha = entropy_lower(region_alpha, precision)?;
    let h_max = block.certify(&domain, region_alpha, precision)?;
    out[axis_x.index()] = h_marginal
        .add(&h_alpha)
        .sub_upper(&h_max)
        .scale_nonnegative(&scale)?;

    // A12 and A13: H(β_(T,W)^(r)) - η_(T,W)^(r) for W in {Y, Z}.
    let child_width = full_support(shape.level().child()?).len();
    for (axis, is_y) in [(axis_y, true), (axis_z, false)] {
        let per_region = split_mixture(tree, node, region_alpha, region, axis, beta)?;
        let h_beta = entropy_lower(&per_region, precision)?;

        // The A12/A13 weight of a split is α(u) + α(s_T - u). The complement's
        // position needs no scan: `u ↦ s - u` reverses the canonical split
        // order (`0007_spec.md` §5.3), so it is the mirrored index. The old
        // `.position(...).unwrap_or(split_index)` silently substituted the
        // split for a missing complement — a coercion AGENTS.md forbids —
        // and is replaced by a structured rejection (`0008_spec.md` §6.2 R6).
        let paired_weight = |split_index: usize,
                             split: &mm_core::shape::Shape|
         -> CoreResult<Rat> {
            let complement = shape.complement(*split)?;
            let complement_index = splits.len().checked_sub(1 + split_index).ok_or_else(|| {
                CoreError::new(ErrorCode::BadPath, "split index exceeds the split list")
                    .equation("A.5")
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
            Ok(&region_alpha
                .get(split_index)
                .cloned()
                .unwrap_or_else(Rat::zero)
                + &region_alpha
                    .get(complement_index)
                    .cloned()
                    .unwrap_or_else(Rat::zero))
        };

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
            let child = child_of(tree, node, *split, region)?;
            let child_beta = beta_of(tree, beta, child, axis);
            let entropy = entropy_upper(&child_beta, precision)?;
            eta = eta.add(&entropy.scale_nonnegative(&weight)?);
        }
        let group_axis = if is_y { axis_y } else { axis_z };
        for value in domain.coordinate_values(group_axis) {
            let mut weight_total = Rat::zero();
            let mut numerator = alloc::vec![Rat::zero(); child_width];
            for (split_index, split) in splits.iter().enumerate() {
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
                let child = child_of(tree, node, *split, region)?;
                let child_beta = beta_of(tree, beta, child, axis);
                accumulate(&mut numerator, &weight, &child_beta);
            }
            // §7.6: a zero weight contributes exactly zero and never divides.
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

/// The retained exponent of one interior level (A15).
///
/// `E_ℓ = Σ_r min { Σ_T E_(T,X)^(r), Σ_T E_(T,Y)^(r), Σ_T E_(T,Z)^(r) }`, where
/// `T` ranges over the positive nodes at that level, **including distinct paths**
/// (§5.2).
///
/// Blocks are consumed node-major then region, matching the §5.2 node ordering
/// every other dense certificate array uses.
///
/// # Errors
///
/// Propagates evaluation failures, and returns [`ErrorCode::CountMismatch`] when
/// the certificate supplies too few blocks.
pub fn e_level(
    tree: &TrackATree,
    level: Level,
    blocks: &mut alloc::collections::VecDeque<MaxEntropyBlock>,
    beta: &[[Vec<Rat>; 3]],
    precision: Precision,
) -> CoreResult<LowerBound> {
    let mut sums: [[LowerBound; 3]; 6] = core::array::from_fn(|_| {
        [
            LowerBound::assert(Rat::zero()),
            LowerBound::assert(Rat::zero()),
            LowerBound::assert(Rat::zero()),
        ]
    });
    for (position, node) in tree.nodes().iter().enumerate() {
        if node.kind != NodeKind::PositiveInterior
            || node.shape.map(|shape| shape.level()) != Some(level)
        {
            continue;
        }
        let mass = tree
            .masses()
            .get(position)
            .cloned()
            .unwrap_or_else(Rat::zero);
        for region in Region::all() {
            let block = blocks.pop_front().ok_or_else(|| {
                CoreError::new(
                    ErrorCode::CountMismatch,
                    "the certificate supplies too few maximum-entropy blocks",
                )
                .equation("§6.5")
                .value(node.path.clone())
            })?;
            let contributions =
                e_interior_node(tree, node, &mass, region, &block, beta, precision)?;
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

/// The number of maximum-entropy blocks an instance requires (§6.5).
///
/// One per region at the root, plus one per positive interior node per region.
/// Recomputed from the tree rather than trusted from the certificate.
#[must_use]
pub fn required_block_count(tree: &TrackATree) -> usize {
    let interior = tree
        .nodes()
        .iter()
        .filter(|node| node.kind == NodeKind::PositiveInterior)
        .count();
    6 + 6 * interior
}
