//! The omega certificate model and decoder (spec §6.1, §6.5).
//!
//! An omega certificate carries `q`, `ℓ*`, the claimed nonnegative rational `Ω`,
//! every free distribution and `μ` in canonical node order, one maximum-entropy
//! block per occurrence of `H_D^max(ρ)`, and `log_precision_bits` in `[32,4096]`
//! (§6.5).
//!
//! Every redundant field is **recomputed** rather than trusted: the node count
//! comes from the instance tree, the per-node variable kind from the node's
//! position, and the block count from the instance (§6.5).

use crate::certificate::{CertificateKind, read_rational};
use crate::reader::CanonicalReader;
use crate::writer::CanonicalWriter;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::level::Level;
use mm_core::{CERTIFICATE_SCHEMA, SOURCE_S1_SHA256, SOURCE_S2_SHA256, SPEC_VERSION};
use mm_rat::Rat;
use std::io::{BufRead, Write};

/// The free variables one node supplies, as decoded from the certificate.
///
/// The variant is chosen by which key the object carries; the checker then
/// validates that choice against the node's position in the tree (§5.2).
#[derive(Clone, Debug)]
pub enum NodePayload {
    /// The root or a positive interior node: `A_T` and `α_T^(r)` per region.
    Branching {
        /// `A_T`, six entries in region order.
        region_weights: Vec<Rat>,
        /// `α_T^(r)`, one distribution per region.
        alpha: Vec<Vec<Rat>>,
    },
    /// A zero-shape node: the free `β_(T,W1)`.
    ZeroShape {
        /// The distribution over `C_(ℓ, s_(T,W1))`.
        beta: Vec<Rat>,
    },
    /// A positive level-2 node: `μ_T ∈ [0,1/2]`.
    LevelTwo {
        /// The single free parameter.
        mu: Rat,
    },
}

/// One maximum-entropy block as it appears in the certificate (§6.5, §7.4).
#[derive(Clone, Debug)]
pub struct BlockPayload {
    /// The slack `ε`.
    pub epsilon: Rat,
    /// `λ₀`.
    pub lambda0: Rat,
    /// `λ_X`.
    pub lambda_x: Vec<Rat>,
    /// `λ_Y`.
    pub lambda_y: Vec<Rat>,
    /// `λ_Z`.
    pub lambda_z: Vec<Rat>,
    /// The strictly positive witness `y`.
    pub y: Vec<Rat>,
}

/// A decoded omega certificate (§6.5).
#[derive(Clone, Debug)]
pub struct OmegaCertificate {
    /// The parameter `q`.
    pub q: u32,
    /// The recursion level `ℓ*`.
    pub level: Level,
    /// The claimed nonnegative rational `Ω`.
    pub omega: Rat,
    /// Target precision in binary fractional bits, in `[32,4096]` (§6.5).
    pub log_precision_bits: u32,
    /// Per-node free variables, in canonical preorder (§5.2).
    pub nodes: Vec<NodePayload>,
    /// Maximum-entropy blocks, in canonical occurrence order (§6.5).
    pub blocks: Vec<BlockPayload>,
}

fn missing(field: &str) -> CoreError {
    CoreError::new(ErrorCode::MissingField, "a required field is absent")
        .equation("§6.5")
        .value(field)
}

fn unknown(field: &str, equation: &'static str) -> CoreError {
    CoreError::new(
        ErrorCode::UnknownField,
        "unknown certificate fields are rejected, never ignored",
    )
    .equation(equation)
    .value(field)
}

pub(crate) fn read_rational_array<R: BufRead>(
    reader: &mut CanonicalReader<R>,
) -> CoreResult<Vec<Rat>> {
    reader.begin_array()?;
    let mut out = Vec::new();
    let mut first = true;
    while reader.next_element(first)? {
        first = false;
        reader.count_rational()?;
        out.push(read_rational(reader)?);
    }
    Ok(out)
}

fn read_rational_matrix<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<Vec<Vec<Rat>>> {
    reader.begin_array()?;
    let mut out = Vec::new();
    let mut first = true;
    while reader.next_element(first)? {
        first = false;
        out.push(read_rational_array(reader)?);
    }
    Ok(out)
}

fn read_node<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<NodePayload> {
    reader.begin_object()?;
    let mut alpha: Option<Vec<Vec<Rat>>> = None;
    let mut beta: Option<Vec<Rat>> = None;
    let mut mu: Option<Rat> = None;
    let mut region_weights: Option<Vec<Rat>> = None;
    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "alpha" => alpha = Some(read_rational_matrix(reader)?),
            "beta" => beta = Some(read_rational_array(reader)?),
            "mu" => {
                reader.count_rational()?;
                mu = Some(read_rational(reader)?);
            }
            "region_weights" => region_weights = Some(read_rational_array(reader)?),
            other => return Err(unknown(other, "§6.5")),
        }
    }
    // The variant is determined by which keys are present, and mixing them is a
    // rejection rather than a precedence rule.
    match (alpha, region_weights, beta, mu) {
        (Some(alpha), Some(region_weights), None, None) => Ok(NodePayload::Branching {
            region_weights,
            alpha,
        }),
        (None, None, Some(beta), None) => Ok(NodePayload::ZeroShape { beta }),
        (None, None, None, Some(mu)) => Ok(NodePayload::LevelTwo { mu }),
        _ => Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "a node must carry exactly one of {alpha, region_weights}, {beta}, or {mu}",
        )
        .equation("A.2")),
    }
}

pub(crate) fn read_block<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<BlockPayload> {
    reader.begin_object()?;
    let mut epsilon = None;
    let mut lambda0 = None;
    let mut lambda_x = None;
    let mut lambda_y = None;
    let mut lambda_z = None;
    let mut y = None;
    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "epsilon" => {
                reader.count_rational()?;
                epsilon = Some(read_rational(reader)?);
            }
            "lambda0" => {
                reader.count_rational()?;
                lambda0 = Some(read_rational(reader)?);
            }
            "lambda_x" => lambda_x = Some(read_rational_array(reader)?),
            "lambda_y" => lambda_y = Some(read_rational_array(reader)?),
            "lambda_z" => lambda_z = Some(read_rational_array(reader)?),
            "y" => y = Some(read_rational_array(reader)?),
            other => return Err(unknown(other, "§7.4")),
        }
    }
    Ok(BlockPayload {
        epsilon: epsilon.ok_or_else(|| missing("epsilon"))?,
        lambda0: lambda0.ok_or_else(|| missing("lambda0"))?,
        lambda_x: lambda_x.ok_or_else(|| missing("lambda_x"))?,
        lambda_y: lambda_y.ok_or_else(|| missing("lambda_y"))?,
        lambda_z: lambda_z.ok_or_else(|| missing("lambda_z"))?,
        y: y.ok_or_else(|| missing("y"))?,
    })
}

/// Decode an omega certificate from canonical bytes (§6.1, §6.5).
///
/// # Errors
///
/// Returns the first structured rejection deterministically (§5.4).
pub fn decode_omega<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<OmegaCertificate> {
    reader.begin_object()?;

    let mut level: Option<Level> = None;
    let mut omega: Option<Rat> = None;
    let mut q: Option<u32> = None;
    let mut precision: Option<u32> = None;
    let mut encoding: Option<String> = None;
    let mut nodes: Option<Vec<NodePayload>> = None;
    let mut blocks: Option<Vec<BlockPayload>> = None;
    let mut schema_seen = false;
    let mut sources_seen = false;
    let mut version_seen = false;

    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "claim" => {
                reader.begin_object()?;
                while let Some(claim_key) = reader.next_key()? {
                    match claim_key.as_str() {
                        "l_star" => {
                            let value = reader.read_u64()?;
                            let narrowed = u8::try_from(value).map_err(|_| {
                                CoreError::new(
                                    ErrorCode::UnsupportedInstance,
                                    "l* is outside the supported range",
                                )
                                .equation("§0.2")
                            })?;
                            level = Some(Level::new(narrowed)?);
                        }
                        "omega" => {
                            reader.count_rational()?;
                            omega = Some(read_rational(reader)?);
                        }
                        "q" => {
                            let value = reader.read_u64()?;
                            q = Some(u32::try_from(value).map_err(|_| {
                                CoreError::new(
                                    ErrorCode::UnsupportedInstance,
                                    "q is outside the supported range",
                                )
                                .equation("§0.2")
                            })?);
                        }
                        other => return Err(unknown(other, "§6.5")),
                    }
                }
            }
            "kind" => {
                let text = reader.read_string()?;
                if CertificateKind::parse(&text)? != CertificateKind::Omega {
                    return Err(CoreError::new(
                        ErrorCode::SchemaMismatch,
                        "expected an omega certificate",
                    )
                    .equation("§6.1")
                    .value(text));
                }
            }
            "payload" => {
                reader.begin_object()?;
                while let Some(payload_key) = reader.next_key()? {
                    match payload_key.as_str() {
                        // §6.5 as amended by `0007_spec.md` §3.1. `encoding` has
                        // no default: a decoder must not infer it from which
                        // other keys happen to be present, because that would
                        // make a truncated symmetric payload readable as a
                        // general one.
                        "encoding" => {
                            let text = reader.read_string()?;
                            match text.as_str() {
                                "general" => encoding = Some(text),
                                "symmetric" => {
                                    return Err(CoreError::new(
                                        ErrorCode::UnsupportedInstance,
                                        "the symmetric encoding is not decoded yet",
                                    )
                                    .equation("§6.5"));
                                }
                                _ => {
                                    return Err(CoreError::new(
                                        ErrorCode::SchemaMismatch,
                                        "encoding must be \"general\" or \"symmetric\"",
                                    )
                                    .equation("§6.5")
                                    .value(text));
                                }
                            }
                        }
                        "log_precision_bits" => {
                            let value = reader.read_u64()?;
                            let bits = u32::try_from(value).map_err(|_| {
                                CoreError::new(
                                    ErrorCode::UnsupportedInstance,
                                    "log_precision_bits is out of range",
                                )
                                .equation("§6.5")
                            })?;
                            // §6.5 fixes the inclusive range 32..=4096.
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
                        "nodes" => {
                            reader.begin_array()?;
                            let mut out = Vec::new();
                            let mut first = true;
                            while reader.next_element(first)? {
                                first = false;
                                out.push(read_node(reader)?);
                            }
                            nodes = Some(out);
                        }
                        other => return Err(unknown(other, "§6.5")),
                    }
                }
            }
            "schema" => {
                let text = reader.read_string()?;
                if text != CERTIFICATE_SCHEMA {
                    return Err(CoreError::new(
                        ErrorCode::SchemaMismatch,
                        "unsupported certificate schema",
                    )
                    .equation("§6.1")
                    .value(text));
                }
                schema_seen = true;
            }
            "source_hashes" => {
                reader.begin_object()?;
                let mut seen = 0usize;
                while let Some(source_key) = reader.next_key()? {
                    let value = reader.read_string()?;
                    let expected = match source_key.as_str() {
                        "S1" => SOURCE_S1_SHA256,
                        "S2" => SOURCE_S2_SHA256,
                        other => return Err(unknown(other, "§0.1")),
                    };
                    if value != expected {
                        return Err(CoreError::new(
                            ErrorCode::SourceHashMismatch,
                            "a certificate source hash disagrees with the locked value",
                        )
                        .equation("§0.1")
                        .value(source_key));
                    }
                    seen += 1;
                }
                if seen != 2 {
                    return Err(missing("source_hashes.S1 and source_hashes.S2"));
                }
                sources_seen = true;
            }
            "spec_version" => {
                let text = reader.read_string()?;
                if text != SPEC_VERSION {
                    return Err(CoreError::new(
                        ErrorCode::SpecVersionMismatch,
                        "this build implements a different specification version",
                    )
                    .equation("§0.5")
                    .value(text));
                }
                version_seen = true;
            }
            other => return Err(unknown(other, "§6.1")),
        }
    }

    if !schema_seen {
        return Err(missing("schema"));
    }
    if !sources_seen {
        return Err(missing("source_hashes"));
    }
    if !version_seen {
        return Err(missing("spec_version"));
    }
    let omega = omega.ok_or_else(|| missing("claim.omega"))?;
    // §7.2 and A.10: the version 1 certificate restriction is Ω ≥ 0, checked
    // here so a negative value never reaches the monotonic shortcut.
    if omega.is_negative() {
        return Err(CoreError::new(
            ErrorCode::NegativeOmega,
            "a claimed omega must be nonnegative",
        )
        .equation("§7.2")
        .value(alloc_format(&omega)));
    }
    // `encoding` has no default (`0007_spec.md` §3.1).
    let _ = encoding.ok_or_else(|| missing("payload.encoding"))?;
    Ok(OmegaCertificate {
        q: q.ok_or_else(|| missing("claim.q"))?,
        level: level.ok_or_else(|| missing("claim.l_star"))?,
        omega,
        log_precision_bits: precision.ok_or_else(|| missing("payload.log_precision_bits"))?,
        nodes: nodes.ok_or_else(|| missing("payload.nodes"))?,
        blocks: blocks.ok_or_else(|| missing("payload.max_entropy_blocks"))?,
    })
}

fn alloc_format(value: &Rat) -> String {
    format!("{value}")
}

/// Encode a decoded omega certificate as canonical bytes (§6.1, §6.3, §6.5).
///
/// This is what makes the §3.5 round trip available for Track A: the typed
/// values a generated Lean module is built from are re-encoded here and required
/// to equal the published bytes, so a proof can never be about data other than
/// what was published.
///
/// # Errors
///
/// Propagates write failures and canonical-order violations.
pub fn encode_omega<W: Write>(
    output: W,
    certificate: &OmegaCertificate,
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
    writer.string(CertificateKind::Omega.as_str())?;

    writer.key("payload")?;
    writer.begin_object()?;
    writer.key("encoding")?;
    writer.string("general")?;
    writer.key("log_precision_bits")?;
    writer.integer(u64::from(certificate.log_precision_bits))?;
    writer.key("max_entropy_blocks")?;
    writer.begin_array()?;
    for block in &certificate.blocks {
        writer.begin_object()?;
        writer.key("epsilon")?;
        write_rational(&mut writer, &block.epsilon)?;
        writer.key("lambda0")?;
        write_rational(&mut writer, &block.lambda0)?;
        writer.key("lambda_x")?;
        write_rational_array(&mut writer, &block.lambda_x)?;
        writer.key("lambda_y")?;
        write_rational_array(&mut writer, &block.lambda_y)?;
        writer.key("lambda_z")?;
        write_rational_array(&mut writer, &block.lambda_z)?;
        writer.key("y")?;
        write_rational_array(&mut writer, &block.y)?;
        writer.end_object()?;
    }
    writer.end_array()?;
    writer.key("nodes")?;
    writer.begin_array()?;
    for node in &certificate.nodes {
        writer.begin_object()?;
        match node {
            NodePayload::Branching {
                region_weights,
                alpha,
            } => {
                writer.key("alpha")?;
                writer.begin_array()?;
                for row in alpha {
                    write_rational_array(&mut writer, row)?;
                }
                writer.end_array()?;
                writer.key("region_weights")?;
                write_rational_array(&mut writer, region_weights)?;
            }
            NodePayload::ZeroShape { beta } => {
                writer.key("beta")?;
                write_rational_array(&mut writer, beta)?;
            }
            NodePayload::LevelTwo { mu } => {
                writer.key("mu")?;
                write_rational(&mut writer, mu)?;
            }
        }
        writer.end_object()?;
    }
    writer.end_array()?;
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

pub(crate) fn write_rational<W: Write>(
    writer: &mut CanonicalWriter<W>,
    value: &Rat,
) -> CoreResult<()> {
    writer.begin_object()?;
    writer.key("d")?;
    writer.string(&value.denominator_text())?;
    writer.key("n")?;
    writer.string(&value.numerator_text())?;
    writer.end_object()
}

pub(crate) fn write_rational_array<W: Write>(
    writer: &mut CanonicalWriter<W>,
    values: &[Rat],
) -> CoreResult<()> {
    writer.begin_array()?;
    for value in values {
        write_rational(writer, value)?;
    }
    writer.end_array()
}
