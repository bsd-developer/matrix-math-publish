//! The symmetric omega certificate encoding (`docs/specs/0007_spec.md` §2–§4).
//!
//! A point is **symmetric** when the free variables of a node depend only on its
//! level and shape, and `α_T^(r)` does not depend on the region. This module
//! encodes such a point once per level-shape pair — a **group** — instead of once
//! per node.
//!
//! The reduction is the reason the encoding exists. At `ℓ* = 4` the general
//! encoding carries 8,882,281 rationals across 1,552,339 nodes; the symmetric one
//! carries 26,319 across 213 groups, a factor of 337. `docs/experiments/omega-l4.md`
//! records that exact evaluation is *superlinear* in block count, so this is not a
//! throughput optimization: it is what makes an `ℓ* = 4` certificate checkable.
//!
//! [`expand`] is the meaning-preserving map to the general encoding, and E1 of
//! §4 is the whole semantic contract:
//!
//! ```text
//! Meaning(c) := Meaning(expand(c))
//! ```
//!
//! A symmetric certificate makes no claim about anything but its own expansion —
//! not about a float point, not about an optimizer run, and not about a general
//! certificate it may have been derived from.

use crate::certificate::read_rational;
use crate::omega::{
    BlockPayload, NodePayload, OmegaCertificate, read_block, read_rational_array, write_rational,
    write_rational_array,
};
use crate::reader::CanonicalReader;
use crate::writer::CanonicalWriter;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::level::Level;
use mm_core::shape::Shape;
use mm_core::{CERTIFICATE_SCHEMA, SOURCE_S1_SHA256, SOURCE_S2_SHA256, SPEC_VERSION};
use mm_rat::rational::Rat;
use std::io::BufRead;
use std::io::Write;

/// The number of regions every branching node fans out over (§5.2).
const REGIONS: usize = 6;

/// A level-shape pair: the unit the symmetric encoding stores once (§2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GroupKey {
    /// The level of every node in the group.
    pub level: Level,
    /// The shape shared by every node in the group.
    pub shape: Shape,
}

/// The free variables of one group, or of the root (§3.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GroupPayload {
    /// A positive group at `ℓ ≥ 3`, or the root: one `α` rather than six.
    Branching {
        /// `A_T`, six entries in region order.
        region_weights: Vec<Rat>,
        /// `α`, a single distribution shared by every region.
        alpha: Vec<Rat>,
    },
    /// A zero-shape group: the free `β` over `C_(ℓ, s_W1)`.
    ZeroShape {
        /// The distribution.
        beta: Vec<Rat>,
    },
    /// A positive level-2 group: `μ ∈ [0,1/2]`.
    LevelTwo {
        /// The single free parameter.
        mu: Rat,
    },
}

/// An omega certificate under the symmetric encoding (§3.1).
#[derive(Clone, Debug)]
pub struct SymmetricCertificate {
    /// The parameter `q`.
    pub q: u32,
    /// The recursion level `ℓ*`.
    pub level: Level,
    /// The claimed nonnegative rational `Ω`.
    pub omega: Rat,
    /// Target precision in binary fractional bits, in `[32,4096]` (§6.5).
    pub log_precision_bits: u32,
    /// The root's free variables. The root is not a group (§3.3).
    pub root: GroupPayload,
    /// Group free variables, positional over [`groups`] order.
    pub groups: Vec<GroupPayload>,
    /// Group maximum-entropy blocks, in §3.4 order.
    pub blocks: Vec<BlockPayload>,
}

/// Enumerate `Groups(ℓ*)`: every level-shape pair reachable in the canonical
/// tree, by **decreasing level, then lexicographic shape** (§3.2).
///
/// Decreasing level is the order the canonical preorder first meets each group,
/// because the root's children carry level `ℓ*`.
///
/// The membership is derived from the instance, never read from the certificate.
/// The identity `|Groups(ℓ*)| = Σ_(ℓ=2..ℓ*) |S_ℓ|` holds — 15, 60 and 213 at the
/// supported levels — but an implementation that assumed it instead of walking
/// would desynchronize silently if A.1 ever changed.
#[must_use]
pub fn groups(level: Level) -> Vec<GroupKey> {
    let mut out = Vec::new();
    let mut current = level.get();
    while current >= 2 {
        if let Ok(this) = Level::new(current) {
            let mut shapes = Shape::enumerate(this);
            shapes.sort_by_key(|shape| shape.canonical_key());
            out.extend(
                shapes
                    .into_iter()
                    .map(|shape| GroupKey { level: this, shape }),
            );
        }
        current -= 1;
    }
    out
}

/// The position of `(ℓ,s)` in [`groups`] order, or `None` if unreachable.
#[must_use]
pub fn group_index(level: Level, key: GroupKey) -> Option<usize> {
    groups(level)
        .iter()
        .position(|candidate| candidate.level == key.level && candidate.shape == key.shape)
}

/// Positive shapes at a level, lexicographically: the block order's inner key.
fn positive_shapes(level: Level) -> Vec<Shape> {
    let mut shapes: Vec<Shape> = Shape::enumerate(level)
        .into_iter()
        .filter(|shape| !shape.is_zero_shape())
        .collect();
    shapes.sort_by_key(|shape| shape.canonical_key());
    shapes
}

/// The `(ℓ,s)` keys of the group blocks, in §3.4 order.
///
/// The root's block first, then for each level from three to `ℓ*` **ascending**
/// each positive shape lexicographically. Ascending level matches A20's
/// level-by-level sum of `E_ℓ`, so the group array and the block array run in
/// opposite directions in level — the same asymmetry the general encoding
/// already has between `nodes` and `max_entropy_blocks`.
#[must_use]
pub fn block_keys(level: Level) -> Vec<Option<GroupKey>> {
    let mut out: Vec<Option<GroupKey>> = vec![None];
    for current in 3..=level.get() {
        if let Ok(this) = Level::new(current) {
            out.extend(
                positive_shapes(this)
                    .into_iter()
                    .map(|shape| Some(GroupKey { level: this, shape })),
            );
        }
    }
    out
}

/// The block count the instance requires: `1 + Σ_(ℓ=3..ℓ*) |S_ℓ^+|` (§3.4).
#[must_use]
pub fn block_count(level: Level) -> usize {
    block_keys(level).len()
}

/// One position in the canonical preorder (§5.2).
#[derive(Clone, Copy, Debug)]
struct Slot {
    level: Level,
    shape: Option<Shape>,
}

/// The canonical preorder of §5.2: a node, then for each region in turn each
/// child shape in `Split` order, recursively.
///
/// Iterative rather than recursive: `ℓ* = 4` has 1,552,339 positions, which is
/// past a comfortable stack depth.
fn preorder(root: Level) -> CoreResult<Vec<Slot>> {
    let mut out = Vec::new();
    // (level, shape) with `None` shape marking the root; pushed in reverse so
    // the stack pops in canonical order.
    let mut stack = vec![Slot {
        level: root,
        shape: None,
    }];
    while let Some(slot) = stack.pop() {
        out.push(slot);
        let (children, child_level) = match slot.shape {
            None => (Shape::enumerate(root), root),
            Some(shape) if !shape.is_zero_shape() && slot.level.get() >= 3 => {
                (shape.splits()?, slot.level.child()?)
            }
            Some(_) => continue,
        };
        let mut ordered = children;
        ordered.sort_by_key(|shape: &Shape| shape.canonical_key());
        for region in (0..REGIONS).rev() {
            let _ = region;
            for shape in ordered.iter().rev() {
                stack.push(Slot {
                    level: child_level,
                    shape: Some(*shape),
                });
            }
        }
    }
    Ok(out)
}

fn missing_group(key: GroupKey) -> CoreError {
    CoreError::new(
        ErrorCode::CountMismatch,
        "no group entry for a level-shape pair the tree reaches",
    )
    .equation("§3.2")
    .value(format!("level {} shape {}", key.level.get(), key.shape))
}

/// Expand a symmetric certificate into the general encoding it means (§4).
///
/// This materializes every node and every block, which at `ℓ* = 4` is the
/// 1,552,339-node object the encoding exists to avoid. §4 is explicit that
/// `expand` MUST NOT be a precondition of checking; it is here for conversion,
/// for the equality proof, and for the fixtures.
///
/// # Errors
///
/// Returns [`ErrorCode::CountMismatch`] when the group or block array does not
/// cover what the instance requires, and propagates shape and level failures.
pub fn expand(certificate: &SymmetricCertificate) -> CoreResult<OmegaCertificate> {
    let keys = groups(certificate.level);
    if certificate.groups.len() != keys.len() {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "group count disagrees with the instance",
        )
        .equation("§3.2")
        .value(format!(
            "{} supplied, {} required",
            certificate.groups.len(),
            keys.len()
        )));
    }
    let block_index_of = block_keys(certificate.level);
    if certificate.blocks.len() != block_index_of.len() {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "group block count disagrees with the instance",
        )
        .equation("§3.4")
        .value(format!(
            "{} supplied, {} required",
            certificate.blocks.len(),
            block_index_of.len()
        )));
    }

    let position = |key: GroupKey| -> CoreResult<usize> {
        keys.iter()
            .position(|candidate| candidate.level == key.level && candidate.shape == key.shape)
            .ok_or_else(|| missing_group(key))
    };
    let block_position = |key: GroupKey| -> CoreResult<usize> {
        block_index_of
            .iter()
            .position(|candidate| {
                candidate.is_some_and(|candidate| {
                    candidate.level == key.level && candidate.shape == key.shape
                })
            })
            .ok_or_else(|| missing_group(key))
    };

    let slots = preorder(certificate.level)?;
    let mut nodes = Vec::with_capacity(slots.len());
    for slot in &slots {
        let payload = match slot.shape {
            None => &certificate.root,
            Some(shape) => {
                &certificate.groups[position(GroupKey {
                    level: slot.level,
                    shape,
                })?]
            }
        };
        nodes.push(match payload {
            // §4: one `α` becomes six identical ones. The region independence of
            // the symmetric point is exactly what this replication expresses.
            GroupPayload::Branching {
                region_weights,
                alpha,
            } => NodePayload::Branching {
                region_weights: region_weights.clone(),
                alpha: vec![alpha.clone(); REGIONS],
            },
            GroupPayload::ZeroShape { beta } => NodePayload::ZeroShape { beta: beta.clone() },
            GroupPayload::LevelTwo { mu } => NodePayload::LevelTwo { mu: mu.clone() },
        });
    }

    // The general block order: the root's six, then for each level from three
    // ascending, each positive interior node at that level in preorder, six
    // apiece. The mapping is by `(ℓ,s)` lookup and never by an ordering
    // coincidence between the two arrays.
    let mut blocks = vec![certificate.blocks[0].clone(); REGIONS];
    for current in 3..=certificate.level.get() {
        let this = Level::new(current)?;
        for slot in &slots {
            let Some(shape) = slot.shape else { continue };
            if slot.level != this || shape.is_zero_shape() || slot.level.get() < 3 {
                continue;
            }
            let block =
                certificate.blocks[block_position(GroupKey { level: this, shape })?].clone();
            blocks.extend(vec![block; REGIONS]);
        }
    }

    Ok(OmegaCertificate {
        q: certificate.q,
        level: certificate.level,
        omega: certificate.omega.clone(),
        log_precision_bits: certificate.log_precision_bits,
        nodes,
        blocks,
    })
}

fn violated(detail: &str, key: GroupKey) -> CoreError {
    CoreError::new(ErrorCode::SymmetryViolated, detail.to_string())
        .equation("§6")
        .value(format!(
            "group level {} shape {}",
            key.level.get(),
            key.shape
        ))
}

/// Convert a general certificate to the symmetric encoding, or reject it (§6).
///
/// A general certificate is symmetric when every node of a level-shape pair
/// carries identical free variables, every `α` is identical across its six
/// regions, and every block attached to a group is identical. Anything else is
/// [`ErrorCode::SymmetryViolated`], naming the group that differs.
///
/// This is the R1 decision procedure of §9.1: it decides membership of the
/// subspace rather than projecting onto it. A certificate that is not symmetric
/// has no symmetric encoding, and silently averaging or picking a representative
/// would change the mathematical object.
///
/// # Errors
///
/// Returns [`ErrorCode::SymmetryViolated`] for a non-symmetric certificate, and
/// [`ErrorCode::CountMismatch`] when the node or block array does not match the
/// instance.
pub fn to_symmetric(certificate: &OmegaCertificate) -> CoreResult<SymmetricCertificate> {
    let slots = preorder(certificate.level)?;
    if certificate.nodes.len() != slots.len() {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "node count disagrees with the instance",
        )
        .equation("§5.2")
        .value(format!(
            "{} supplied, {} required",
            certificate.nodes.len(),
            slots.len()
        )));
    }
    let keys = groups(certificate.level);

    // The root: one `α` if and only if all six agree.
    let root = match &certificate.nodes[0] {
        NodePayload::Branching {
            region_weights,
            alpha,
        } => {
            let first = alpha.first().ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "the root has no alpha").equation("§3.3")
            })?;
            if alpha.iter().any(|row| row != first) {
                return Err(CoreError::new(
                    ErrorCode::SymmetryViolated,
                    "the root's alpha differs across regions",
                )
                .equation("§6"));
            }
            GroupPayload::Branching {
                region_weights: region_weights.clone(),
                alpha: first.clone(),
            }
        }
        _ => {
            return Err(CoreError::new(
                ErrorCode::SchemaMismatch,
                "the root must be a branching node",
            )
            .equation("§5.2"));
        }
    };

    // Every other node must agree with the first node of its group.
    let mut collected: Vec<Option<GroupPayload>> = vec![None; keys.len()];
    for (slot, node) in slots.iter().zip(certificate.nodes.iter()).skip(1) {
        let Some(shape) = slot.shape else { continue };
        let key = GroupKey {
            level: slot.level,
            shape,
        };
        let index = keys
            .iter()
            .position(|candidate| candidate.level == key.level && candidate.shape == key.shape)
            .ok_or_else(|| missing_group(key))?;
        let payload = match node {
            NodePayload::Branching {
                region_weights,
                alpha,
            } => {
                let first = alpha
                    .first()
                    .ok_or_else(|| violated("a branching node has no alpha", key))?;
                if alpha.iter().any(|row| row != first) {
                    return Err(violated("alpha differs across regions", key));
                }
                GroupPayload::Branching {
                    region_weights: region_weights.clone(),
                    alpha: first.clone(),
                }
            }
            NodePayload::ZeroShape { beta } => GroupPayload::ZeroShape { beta: beta.clone() },
            NodePayload::LevelTwo { mu } => GroupPayload::LevelTwo { mu: mu.clone() },
        };
        match &collected[index] {
            None => collected[index] = Some(payload),
            Some(existing) if *existing == payload => {}
            Some(_) => {
                return Err(violated(
                    "two nodes of the same level and shape carry different free variables",
                    key,
                ));
            }
        }
    }

    let mut group_payloads = Vec::with_capacity(keys.len());
    for (index, key) in keys.iter().enumerate() {
        group_payloads.push(
            collected[index]
                .clone()
                .ok_or_else(|| missing_group(*key))?,
        );
    }

    // Blocks: the root's six must agree, and each group's must agree.
    //
    // The walk follows the general block order that `expand` writes -- the
    // root's six, then for each level from three ascending, each positive
    // interior node in preorder, six apiece -- because that is the order the
    // array is actually in. Bounding the walk by the *group* count instead
    // examined 22 x 6 = 132 of 762 entries at l*=3 and 762 of 207,906 at l*=4,
    // and silently kept region 1's block as the representative for every group.
    // §6 forbids exactly that: a general certificate whose blocks differ across
    // a group is valid and simply has no symmetric encoding.
    //
    // The count comes from `slots`, which is already computed above. Calling
    // `expand` to learn it would materialize the 1,552,339-node object this
    // encoding exists to avoid, from inside the converter that exists to avoid
    // it (§12's risk row: never expand before rationalizing).
    let expected_blocks = block_keys(certificate.level);
    let mut blocks: Vec<Option<BlockPayload>> = vec![None; expected_blocks.len()];
    let mut order: Vec<Option<GroupKey>> = vec![None];
    for current in 3..=certificate.level.get() {
        let this = Level::new(current)?;
        for slot in &slots {
            let Some(shape) = slot.shape else { continue };
            if slot.level != this || shape.is_zero_shape() {
                continue;
            }
            order.push(Some(GroupKey { level: this, shape }));
        }
    }
    let required = order.len() * REGIONS;
    if certificate.blocks.len() != required {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "block count disagrees with the instance",
        )
        .equation("§3.4")
        .value(format!(
            "{} supplied, {required} required",
            certificate.blocks.len()
        )));
    }
    // Slot lookup by (l,s), never by an ordering coincidence between the two
    // arrays: `order` runs in node preorder and `expected_blocks` in group
    // order, and they agree only by construction.
    let slot_of = |key: GroupKey| -> CoreResult<usize> {
        expected_blocks
            .iter()
            .position(|candidate| {
                candidate.is_some_and(|candidate| {
                    candidate.level == key.level && candidate.shape == key.shape
                })
            })
            .ok_or_else(|| missing_group(key))
    };
    let mut cursor = 0usize;
    for key in &order {
        let slot_index = match key {
            None => 0,
            Some(key) => slot_of(*key)?,
        };
        for _ in 0..REGIONS {
            let block = certificate.blocks.get(cursor).ok_or_else(|| {
                CoreError::new(ErrorCode::CountMismatch, "a block is missing").equation("§3.4")
            })?;
            match &blocks[slot_index] {
                None => blocks[slot_index] = Some(block.clone()),
                Some(existing) if blocks_equal(existing, block) => {}
                Some(_) => {
                    let named = key.unwrap_or(GroupKey {
                        level: certificate.level,
                        shape: *Shape::enumerate(certificate.level)
                            .first()
                            .ok_or_else(|| missing_group(keys[0]))?,
                    });
                    return Err(violated("two blocks of the same group differ", named));
                }
            }
            cursor += 1;
        }
    }

    let mut block_payloads = Vec::with_capacity(expected_blocks.len());
    for (index, key) in expected_blocks.iter().enumerate() {
        block_payloads.push(blocks[index].clone().ok_or_else(|| {
            CoreError::new(ErrorCode::CountMismatch, "a group block is missing")
                .equation("§3.4")
                .value(format!("{key:?}"))
        })?);
    }

    Ok(SymmetricCertificate {
        q: certificate.q,
        level: certificate.level,
        omega: certificate.omega.clone(),
        log_precision_bits: certificate.log_precision_bits,
        root,
        groups: group_payloads,
        blocks: block_payloads,
    })
}

fn blocks_equal(left: &BlockPayload, right: &BlockPayload) -> bool {
    left.epsilon == right.epsilon
        && left.lambda0 == right.lambda0
        && left.lambda_x == right.lambda_x
        && left.lambda_y == right.lambda_y
        && left.lambda_z == right.lambda_z
        && left.y == right.y
}

/// Write a symmetric certificate as canonical bytes (§3.1–3.4, §6.3).
///
/// The payload's keys in sorted order are `encoding`, `groups`,
/// `log_precision_bits`, `max_entropy_blocks`, `root`. The envelope, the `claim`
/// object, the rational grammar and the canonicalization rules are those of the
/// general encoding, unchanged.
///
/// # Errors
///
/// Propagates writer failures and the count checks of [`expand`].
pub fn encode_symmetric_omega<W: Write>(
    output: W,
    certificate: &SymmetricCertificate,
) -> CoreResult<([u8; 32], u64)> {
    let mut writer = CanonicalWriter::new(output);
    writer.begin_object()?;
    writer.key("claim")?;
    writer.begin_object()?;
    writer.key("l_star")?;
    writer.integer(u64::from(certificate.level.get()))?;
    writer.key("omega")?;
    write_rational(&mut writer, &certificate.omega)?;
    writer.key("q")?;
    writer.integer(u64::from(certificate.q))?;
    writer.end_object()?;

    writer.key("kind")?;
    writer.string("omega")?;

    writer.key("payload")?;
    writer.begin_object()?;
    writer.key("encoding")?;
    writer.string("symmetric")?;
    writer.key("groups")?;
    writer.begin_array()?;
    for group in &certificate.groups {
        write_group(&mut writer, group)?;
    }
    writer.end_array()?;
    writer.key("log_precision_bits")?;
    writer.integer(u64::from(certificate.log_precision_bits))?;
    writer.key("max_entropy_blocks")?;
    writer.begin_array()?;
    for block in &certificate.blocks {
        write_block(&mut writer, block)?;
    }
    writer.end_array()?;
    writer.key("root")?;
    write_group(&mut writer, &certificate.root)?;
    writer.end_object()?;

    writer.key("schema")?;
    writer.string(CERTIFICATE_SCHEMA)?;
    writer.key("source_hashes")?;
    writer.begin_object()?;
    writer.key("S1")?;
    writer.string(SOURCE_S1_SHA256)?;
    writer.key("S2")?;
    writer.string(SOURCE_S2_SHA256)?;
    writer.end_object()?;
    writer.key("spec_version")?;
    writer.string(SPEC_VERSION)?;
    writer.end_object()?;

    let byte_count = writer.byte_count();
    let digest = writer.finish()?;
    Ok((digest, byte_count))
}

fn write_group<W: Write>(writer: &mut CanonicalWriter<W>, group: &GroupPayload) -> CoreResult<()> {
    writer.begin_object()?;
    match group {
        GroupPayload::Branching {
            region_weights,
            alpha,
        } => {
            writer.key("alpha")?;
            write_rational_array(writer, alpha)?;
            writer.key("region_weights")?;
            write_rational_array(writer, region_weights)?;
        }
        GroupPayload::ZeroShape { beta } => {
            writer.key("beta")?;
            write_rational_array(writer, beta)?;
        }
        GroupPayload::LevelTwo { mu } => {
            writer.key("mu")?;
            write_rational(writer, mu)?;
        }
    }
    writer.end_object()?;
    Ok(())
}

fn write_block<W: Write>(writer: &mut CanonicalWriter<W>, block: &BlockPayload) -> CoreResult<()> {
    writer.begin_object()?;
    writer.key("epsilon")?;
    write_rational(writer, &block.epsilon)?;
    writer.key("lambda0")?;
    write_rational(writer, &block.lambda0)?;
    writer.key("lambda_x")?;
    write_rational_array(writer, &block.lambda_x)?;
    writer.key("lambda_y")?;
    write_rational_array(writer, &block.lambda_y)?;
    writer.key("lambda_z")?;
    write_rational_array(writer, &block.lambda_z)?;
    writer.key("y")?;
    write_rational_array(writer, &block.y)?;
    writer.end_object()?;
    Ok(())
}

/// Read one group entry (§3.3).
///
/// The variant is inferred from the key set, and the caller checks it against
/// the kind the position implies — the same rule §5.2 applies to `nodes`.
fn read_group<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<GroupPayload> {
    reader.begin_object()?;
    let mut alpha: Option<Vec<Rat>> = None;
    let mut beta: Option<Vec<Rat>> = None;
    let mut mu: Option<Rat> = None;
    let mut region_weights: Option<Vec<Rat>> = None;
    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "alpha" => alpha = Some(read_rational_array(reader)?),
            "beta" => beta = Some(read_rational_array(reader)?),
            "mu" => mu = Some(read_rational(reader)?),
            "region_weights" => region_weights = Some(read_rational_array(reader)?),
            other => {
                return Err(CoreError::new(
                    ErrorCode::UnknownField,
                    "unknown key in a group entry",
                )
                .equation("§3.3")
                .value(other.to_string()));
            }
        }
    }
    match (alpha, beta, mu, region_weights) {
        (Some(alpha), None, None, Some(region_weights)) => Ok(GroupPayload::Branching {
            region_weights,
            alpha,
        }),
        (None, Some(beta), None, None) => Ok(GroupPayload::ZeroShape { beta }),
        (None, None, Some(mu), None) => Ok(GroupPayload::LevelTwo { mu }),
        _ => Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "a group entry mixes the keys of different kinds",
        )
        .equation("§3.3")),
    }
}

/// Decode a symmetric omega certificate from canonical bytes (§3.1–3.4).
///
/// Counts are derived from the instance and a mismatch is `count_mismatch`; the
/// certificate never declares how many groups or blocks it carries.
///
/// # Errors
///
/// Returns the stable rejection codes of §5.4 for a malformed payload, and
/// [`ErrorCode::CountMismatch`] when the arrays disagree with the instance.
pub fn decode_symmetric_omega<R: BufRead>(
    reader: &mut CanonicalReader<R>,
) -> CoreResult<SymmetricCertificate> {
    let general_error =
        |detail: &str| CoreError::new(ErrorCode::MissingField, detail.to_string()).equation("§3.1");
    reader.begin_object()?;
    let mut q: Option<u32> = None;
    let mut level: Option<Level> = None;
    let mut omega: Option<Rat> = None;
    let mut precision: Option<u32> = None;
    let mut root: Option<GroupPayload> = None;
    let mut group_payloads: Option<Vec<GroupPayload>> = None;
    let mut blocks: Option<Vec<BlockPayload>> = None;

    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "claim" => {
                reader.begin_object()?;
                while let Some(claim_key) = reader.next_key()? {
                    match claim_key.as_str() {
                        "l_star" => {
                            level = Some(Level::new(u8::try_from(reader.read_u64()?).map_err(
                                |_| {
                                    CoreError::new(
                                        ErrorCode::UnsupportedInstance,
                                        "l_star out of range",
                                    )
                                    .equation("§0.2")
                                },
                            )?)?)
                        }
                        "omega" => omega = Some(read_rational(reader)?),
                        "q" => {
                            q = Some(u32::try_from(reader.read_u64()?).map_err(|_| {
                                CoreError::new(ErrorCode::UnsupportedInstance, "q out of range")
                                    .equation("§6.5")
                            })?);
                        }
                        other => {
                            return Err(CoreError::new(
                                ErrorCode::UnknownField,
                                "unknown key in claim",
                            )
                            .equation("§6.1")
                            .value(other.to_string()));
                        }
                    }
                }
            }
            "kind" => {
                let text = reader.read_string()?;
                if text != "omega" {
                    return Err(CoreError::new(
                        ErrorCode::SchemaMismatch,
                        "not an omega certificate",
                    )
                    .equation("§6.1")
                    .value(text));
                }
            }
            "payload" => {
                reader.begin_object()?;
                while let Some(payload_key) = reader.next_key()? {
                    match payload_key.as_str() {
                        "encoding" => {
                            let text = reader.read_string()?;
                            if text != "symmetric" {
                                return Err(CoreError::new(
                                    ErrorCode::SchemaMismatch,
                                    "expected the symmetric encoding",
                                )
                                .equation("§3.1")
                                .value(text));
                            }
                        }
                        "groups" => {
                            reader.begin_array()?;
                            let mut out = Vec::new();
                            let mut first = true;
                            while reader.next_element(first)? {
                                first = false;
                                out.push(read_group(reader)?);
                            }
                            group_payloads = Some(out);
                        }
                        "log_precision_bits" => {
                            let bits = u32::try_from(reader.read_u64()?).map_err(|_| {
                                CoreError::new(
                                    ErrorCode::UnsupportedInstance,
                                    "log_precision_bits is out of range",
                                )
                                .equation("§6.5")
                            })?;
                            let _ = mm_rat::log2::Precision::new(bits)?;
                            precision = Some(bits);
                        }
                        "max_entropy_blocks" => {
                            reader.begin_array()?;
                            let mut out = Vec::new();
                            let mut first = true;
                            while reader.next_element(first)? {
                                first = false;
                                out.push(read_block(reader)?);
                            }
                            blocks = Some(out);
                        }
                        "root" => root = Some(read_group(reader)?),
                        other => {
                            return Err(CoreError::new(
                                ErrorCode::UnknownField,
                                "unknown key in a symmetric payload",
                            )
                            .equation("§3.1")
                            .value(other.to_string()));
                        }
                    }
                }
            }
            "schema" | "source_hashes" | "spec_version" => {
                reader.skip_value()?;
            }
            other => {
                return Err(
                    CoreError::new(ErrorCode::UnknownField, "unknown key in the envelope")
                        .equation("§6.1")
                        .value(other.to_string()),
                );
            }
        }
    }

    let level = level.ok_or_else(|| general_error("claim.l_star"))?;
    let certificate = SymmetricCertificate {
        q: q.ok_or_else(|| general_error("claim.q"))?,
        level,
        omega: omega.ok_or_else(|| general_error("claim.omega"))?,
        log_precision_bits: precision.ok_or_else(|| general_error("payload.log_precision_bits"))?,
        root: root.ok_or_else(|| general_error("payload.root"))?,
        groups: group_payloads.ok_or_else(|| general_error("payload.groups"))?,
        blocks: blocks.ok_or_else(|| general_error("payload.max_entropy_blocks"))?,
    };

    // Counts come from the instance, never from the certificate (§3.2, §3.4).
    let required_groups = groups(level).len();
    if certificate.groups.len() != required_groups {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "group count disagrees with the instance",
        )
        .equation("§3.2")
        .value(format!(
            "{} supplied, {required_groups} required",
            certificate.groups.len()
        )));
    }
    let required_blocks = block_count(level);
    if certificate.blocks.len() != required_blocks {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "group block count disagrees with the instance",
        )
        .equation("§3.4")
        .value(format!(
            "{} supplied, {required_blocks} required",
            certificate.blocks.len()
        )));
    }
    Ok(certificate)
}
