//! Certificate-specific Lean module generation for Track A (spec §3.5, §6.5).
//!
//! The generator is **untrusted for soundness**. It emits complete published
//! bytes, and Lean independently decodes and checks them at every supported
//! level. One native evaluation binds acceptance, the exact claim and digest.
//! The resulting declarations are queried from the compiled environment for
//! result-local assurance (§4.6); feasibility is never an assumed premise.

use crate::lean::{GeneratedModule, Profile};
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::path::NodeKind;
use mm_exact::domain::support_vectors;
use mm_schema::omega::{NodePayload, OmegaCertificate};

/// Carry the complete published bytes through Lean's raw-string parser.
///
/// A delimiter longer than every hash run following a quote cannot occur as
/// a closing delimiter in the payload. This changes only source representation;
/// the ordinary Lean decoder, digest check and acceptance proof still consume
/// every published byte (ADR 0026).
fn published_raw_literal(published_bytes: &[u8]) -> CoreResult<String> {
    let published = std::str::from_utf8(published_bytes).map_err(|_| {
        CoreError::new(
            ErrorCode::NoncanonicalJson,
            "canonical certificate bytes must be UTF-8",
        )
        .equation("§6.3")
    })?;
    let longest_hash_run = published
        .split('"')
        .skip(1)
        .map(|suffix| suffix.bytes().take_while(|byte| *byte == b'#').count())
        .max()
        .unwrap_or(0);
    let delimiter = "#".repeat(longest_hash_run + 1);
    Ok(format!("r{delimiter}\"{published}\"{delimiter}"))
}

/// Check that one node's payload matches the position it occupies (§5.2, A.2).
fn check_payload_kind(slot: &mm_exact::tree::NodeSlot, payload: &NodePayload) -> CoreResult<()> {
    use mm_core::path::NodeKind;
    let wrong = |what: &'static str| {
        Err(CoreError::new(ErrorCode::BadPath, what)
            .equation("A.2")
            .value(slot.path.clone()))
    };
    match (slot.kind, payload) {
        (NodeKind::Root | NodeKind::PositiveInterior, NodePayload::Branching { .. })
        | (NodeKind::PositiveLevelTwo, NodePayload::LevelTwo { .. }) => Ok(()),
        (NodeKind::ZeroShape, NodePayload::ZeroShape { beta }) => {
            let Some(shape) = slot.shape else {
                return wrong("a zero-shape node has no shape");
            };
            let Some(w1) = shape.first_nonzero_coord() else {
                return wrong("a zero-shape node has no nonzero coordinate");
            };
            let vectors = support_vectors(shape.level(), shape.coord(w1))?;
            if vectors.len() == beta.len() {
                Ok(())
            } else {
                wrong("the free beta length does not match |C(l, s_W1)|")
            }
        }
        _ => wrong("a node's free-variable kind disagrees with its position"),
    }
}

/// Generate the certificate-specific Lean module for an omega certificate.
///
/// # Errors
///
/// Rejects unsupported CK evaluation, incorrect instance-derived counts and
/// node payloads that do not match their positions.
pub fn generate(
    certificate: &OmegaCertificate,
    published_bytes: &[u8],
    digest_hex: &str,
    profile: Profile,
) -> CoreResult<GeneratedModule> {
    if profile == Profile::Ck {
        return Err(CoreError::new(
            ErrorCode::UnsupportedInstance,
            "profile CK is not reachable for Track A: every directed bound is a \
             Lean core Rat, whose arithmetic is opaque to the kernel, so the closed \
             evaluation cannot reduce. Use --profile cn, which §3.4 permits.",
        )
        .equation("§3.4"));
    }
    // The Lean checker and decoder cover the §0.2 range. Everything structural
    // below is an *early* diagnostic: the generated module carries the published
    // bytes and Lean decodes and validates them itself, so these checks exist to
    // fail with a reason before a native compile rather than after it.
    let slots = mm_exact::tree::skeleton(certificate.level)?;
    if certificate.nodes.len() != slots.len() {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the node array length disagrees with the instance tree",
        )
        .equation("§5.2")
        .value(format!(
            "{} nodes, expected {}",
            certificate.nodes.len(),
            slots.len()
        )));
    }
    let blocks_required = 6 + 6 * slots
        .iter()
        .filter(|slot| slot.kind == NodeKind::PositiveInterior)
        .count();
    if certificate.blocks.len() != blocks_required {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the maximum-entropy block count disagrees with the instance",
        )
        .equation("§6.5")
        .value(format!(
            "{} blocks, expected {blocks_required}",
            certificate.blocks.len()
        )));
    }
    for (slot, payload) in slots.iter().zip(certificate.nodes.iter()) {
        check_payload_kind(slot, payload)?;
    }

    let short = digest_hex.get(..16).unwrap_or(digest_hex);
    let module_name = format!("MatrixMath.Generated.Omega_{short}");
    let cert_theorem = format!("omegaCert_{digest_hex}");
    let result_theorem = format!("omegaResult_{digest_hex}");
    let claim = format!("omega <= {}", certificate.omega);

    let literal = published_raw_literal(published_bytes)?;

    let mut source = String::new();
    source.push_str(&format!(
        "/-\n\
         Generated Track A certificate module. Do not edit.\n\n\
         canonical sha256 : {digest_hex}\n\
         claim            : {claim}\n\
         profile          : {}\n\
         spec version     : {}\n\n\
         This module is hashed publication evidence, not a trusted assumption\n\
         (spec §3.3). It carries the **published bytes**, not a typed\n\
         transcription of them: Lean decodes them itself (§3.1), so the theorem\n\
         below is about the artifact rather than about data alongside it.\n\
         The only project axiom permitted here is AX1_combination_loss (§3.2).\n\
         -/\n",
        profile.as_str(),
        mm_core::SPEC_VERSION
    ));
    source.push_str("import MatrixMath.Schema.Omega\nimport MatrixMath.ResultAssurance\n\n");
    source.push_str("namespace MatrixMath.Generated\n\n");
    source.push_str("open MatrixMath MatrixMath.Schema\n\n");

    source.push_str(&format!(
        "/-- The published canonical bytes, verbatim (§6.3). -/\n\
         def bytes_{short} : ByteArray :=\n  {literal}.toUTF8\n\n"
    ));
    source.push_str(&format!(
        "/-- The claimed bound, as an exact rational (§6.2). -/\n\
         def omegaClaim_{short} : Rat :=\n  ({} : Rat) / ({} : Rat)\n\n",
        certificate.omega.numerator_text(),
        certificate.omega.denominator_text()
    ));

    // The artifact identity, as bytes: sha256 hex decoded pairwise. The
    // digest is *checked inside* the native evaluation (§6.3 folded into
    // §3.4's single Boolean), so a module whose byte literal drifts from the
    // published artifact fails verification rather than proving a theorem
    // about the wrong object.
    let digest_bytes: Vec<String> = (0..digest_hex.len() / 2)
        .map(|i| format!("0x{}", &digest_hex[2 * i..2 * i + 2]))
        .collect();
    source.push_str(&format!(
        "/-- The artifact identity: the sha256 of `bytes_{short}` (§6.3). -/\n\
         def omegaDigest_{short} : ByteArray :=\n  ByteArray.mk #[{}]\n\n",
        digest_bytes.join(", ")
    ));

    source.push_str("set_option maxRecDepth 8000000 in\n");
    source.push_str("set_option maxHeartbeats 4000000 in\n");
    source.push_str(&format!(
        "/-- The closed acceptance test over the published bytes (§3.1, §7.2, A21).\n\n\
         One Boolean, and therefore one native-evaluation axiom, as §3.4 requires:\n\
         it conjoins \"the checker accepts these bytes\", \"the omega they carry is\n\
         the one named below\", and \"these bytes' sha256 is the named digest\" —\n\
         so the theorem is checkably about the published artifact itself. -/\n\
         theorem {cert_theorem} :\n\
         \x20   acceptsOmegaDigest Limits.default bytes_{short} omegaClaim_{short} omegaDigest_{short} = true := by\n\
         \x20 {}\n\n",
        profile.tactic()
    ));

    source.push_str(&format!(
        "/-- **{claim}**\n\n\
         The Lean checker decoded the published bytes, decided the directed A21\n\
         condition, and `check_sound` turned that into feasibility of the cited\n\
         A.10 problem; `AX1_combination_loss` turns feasibility into a bound on\n\
         `ω`. This is an upper bound on the exponent and nothing stronger. -/\n\
         theorem {result_theorem} :\n\
         \x20   omegaExponent ≤ ((omegaClaim_{short} : Rat) : Real) :=\n\
         \x20 omega_le_of_acceptsOmegaDigest {cert_theorem}\n\n"
    ));

    source.push_str(&format!(
        "#print axioms {cert_theorem}\n#print axioms {result_theorem}\n\n\
         set_option maxHeartbeats 2000000 in\n\
         run_cmd MatrixMath.ResultAssurance.emit ``MatrixMath.Generated.{cert_theorem} ``MatrixMath.Generated.{result_theorem}\n\n\
         end MatrixMath.Generated\n"
    ));

    Ok(GeneratedModule {
        module_name,
        source,
        cert_theorem,
        result_theorem,
        claim,
        literal_count: published_bytes.len(),
        shard_count: 1,
    })
}

/// Generate the certificate-specific Lean module for a **symmetric** omega
/// certificate (`0007_spec.md` §5.1, `0017_spec.md` §4).
///
/// The module mirrors the general Track A shape: the published compact bytes
/// verbatim, the claim as an exact rational, the digest literal, one closed
/// Boolean decided natively, and the result theorem through
/// `omega_le_of_acceptsSymOmegaDigest`. The compact certificate is what the
/// native evaluation decodes and checks; the 1,552,339-node expansion exists
/// only inside the bridge proof, never at runtime.
///
/// # Errors
///
/// Returns [`ErrorCode::UnsupportedInstance`] for profile CK, and
/// [`ErrorCode::CountMismatch`] when the group or block arrays disagree with
/// the instance.
pub fn generate_symmetric(
    certificate: &mm_schema::symmetric::SymmetricCertificate,
    published_bytes: &[u8],
    digest_hex: &str,
    profile: Profile,
) -> CoreResult<GeneratedModule> {
    if profile == Profile::Ck {
        return Err(CoreError::new(
            ErrorCode::UnsupportedInstance,
            "profile CK is not reachable for Track A: every directed bound is a \
             Lean core Rat, whose arithmetic is opaque to the kernel, so the closed \
             evaluation cannot reduce. Use --profile cn, which §3.4 permits.",
        )
        .equation("§3.4"));
    }
    let required_groups = mm_schema::symmetric::groups(certificate.level).len();
    if certificate.groups.len() != required_groups {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the group array length disagrees with the instance",
        )
        .equation("§3.2")
        .value(format!(
            "{} groups, expected {required_groups}",
            certificate.groups.len()
        )));
    }
    let required_blocks = mm_schema::symmetric::block_count(certificate.level);
    if certificate.blocks.len() != required_blocks {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the group block count disagrees with the instance",
        )
        .equation("§3.4")
        .value(format!(
            "{} blocks, expected {required_blocks}",
            certificate.blocks.len()
        )));
    }

    let short = digest_hex.get(..16).unwrap_or(digest_hex);
    let module_name = format!("MatrixMath.Generated.SymOmega_{short}");
    let cert_theorem = format!("symOmegaCert_{digest_hex}");
    let result_theorem = format!("symOmegaResult_{digest_hex}");
    let claim = format!("omega <= {}", certificate.omega);

    let literal = published_raw_literal(published_bytes)?;

    let mut source = String::new();
    source.push_str(&format!(
        "/-\n\
         Generated Track A symmetric certificate module. Do not edit.\n\n\
         canonical sha256 : {digest_hex}\n\
         claim            : {claim}\n\
         profile          : {}\n\
         spec version     : {}\n\n\
         This module carries the **published compact bytes**: Lean decodes them\n\
         itself and runs the group-level check, and the bridge theorem of\n\
         `0007_spec.md` §5.1 connects acceptance to the general semantics. The\n\
         only project axiom permitted here is AX1_combination_loss (§3.2).\n\
         -/\n",
        profile.as_str(),
        mm_core::SPEC_VERSION
    ));
    source
        .push_str("import MatrixMath.Certificate.SymBridge\nimport MatrixMath.ResultAssurance\n\n");
    source.push_str("namespace MatrixMath.Generated\n\n");
    source.push_str("open MatrixMath MatrixMath.Schema\n\n");

    source.push_str(&format!(
        "/-- The published canonical compact bytes, verbatim (§6.3). -/\n\
         def symBytes_{short} : ByteArray :=\n  {literal}.toUTF8\n\n"
    ));
    source.push_str(&format!(
        "/-- The claimed bound, as an exact rational (§6.2). -/\n\
         def symOmegaClaim_{short} : Rat :=\n  ({} : Rat) / ({} : Rat)\n\n",
        certificate.omega.numerator_text(),
        certificate.omega.denominator_text()
    ));
    let digest_bytes: Vec<String> = (0..digest_hex.len() / 2)
        .map(|i| format!("0x{}", &digest_hex[2 * i..2 * i + 2]))
        .collect();
    source.push_str(&format!(
        "/-- The artifact identity: the sha256 of `symBytes_{short}` (§6.3). -/\n\
         def symOmegaDigest_{short} : ByteArray :=\n  ByteArray.mk #[{}]\n\n",
        digest_bytes.join(", ")
    ));

    source.push_str("set_option maxRecDepth 8000000 in\n");
    source.push_str("set_option maxHeartbeats 4000000 in\n");
    source.push_str(&format!(
        "/-- The closed compact acceptance test over the published bytes.\n\n\
         One Boolean, and therefore one native-evaluation axiom (§3.4): the\n\
         group-level checker accepts these bytes, the omega they carry is the\n\
         one named below, and these bytes' sha256 is the named digest. -/\n\
         theorem {cert_theorem} :\n\
         \x20   acceptsSymOmegaDigest Limits.default symBytes_{short} symOmegaClaim_{short} symOmegaDigest_{short} = true := by\n\
         \x20 {}\n\n",
        profile.tactic()
    ));
    source.push_str(&format!(
        "/-- **{claim}**\n\n\
         Group-level acceptance implies acceptance of the §4 expansion\n\
         (`SymCert.check_implies_expand`), whose feasibility bounds `ω` under\n\
         `AX1_combination_loss`. An upper bound on the exponent and nothing\n\
         stronger. -/\n\
         theorem {result_theorem} :\n\
         \x20   omegaExponent ≤ ((symOmegaClaim_{short} : Rat) : Real) :=\n\
         \x20 omega_le_of_acceptsSymOmegaDigest {cert_theorem}\n\n"
    ));
    source.push_str(&format!(
        "#print axioms {cert_theorem}\n#print axioms {result_theorem}\n\n\
         set_option maxHeartbeats 2000000 in\n\
         run_cmd MatrixMath.ResultAssurance.emit ``MatrixMath.Generated.{cert_theorem} ``MatrixMath.Generated.{result_theorem}\n\n\
         end MatrixMath.Generated\n"
    ));

    Ok(GeneratedModule {
        module_name,
        source,
        cert_theorem,
        result_theorem,
        claim,
        literal_count: published_bytes.len(),
        shard_count: 1,
    })
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::expect_used,
        clippy::panic,
        clippy::unwrap_used,
        reason = "test assertions must fail loudly; §17.1 governs library code"
    )]

    use super::{generate, generate_symmetric, published_raw_literal};
    use crate::lean::Profile;
    use mm_core::codes::ErrorCode;
    use mm_schema::{CanonicalReader, Limits, OmegaCertificate, decode_omega};

    fn hand_fixture() -> (OmegaCertificate, Vec<u8>) {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/vectors/omega-l2-hand.json");
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
        let mut reader =
            CanonicalReader::new(std::io::BufReader::new(bytes.as_slice()), Limits::default());
        (decode_omega(&mut reader).expect("decode"), bytes)
    }

    /// §3.4: a Track A directed bound is a Lean core `Rat`, which the kernel
    /// cannot reduce. Emitting a `decide` module would produce a `sorryAx`, so
    /// the request is refused with the reason instead.
    #[test]
    fn profile_ck_is_refused_with_its_reason() {
        let (certificate, bytes) = hand_fixture();
        let error = generate(&certificate, &bytes, "abc", Profile::Ck).expect_err("CK must refuse");
        assert!(error.message().contains("opaque to the kernel"));
    }

    /// §3.1: the emitted module must carry the **published bytes**, so the
    /// theorem is about the artifact rather than about a transcription of it.
    #[test]
    fn the_generated_module_carries_the_published_bytes() {
        let (certificate, bytes) = hand_fixture();
        let module =
            generate(&certificate, &bytes, "deadbeefdeadbeef00", Profile::Cn).expect("generate");
        let text = String::from_utf8(bytes.clone()).expect("ascii");
        assert!(module.source.contains(&format!("r#\"{text}\"#.toUTF8")));
        assert!(
            module
                .source
                .contains("acceptsOmegaDigest Limits.default bytes_")
        );
        assert!(module.source.contains("omega_le_of_acceptsOmegaDigest"));
        assert!(module.source.contains("ByteArray.mk #[0xde, 0xad, 0xbe"));
        assert_eq!(module.source.matches("native_decide").count(), 1);
        assert!(module.source.contains("import MatrixMath.ResultAssurance"));
        assert!(module.source.contains("run_cmd MatrixMath.ResultAssurance.emit ``MatrixMath.Generated.omegaCert_deadbeefdeadbeef00 ``MatrixMath.Generated.omegaResult_deadbeefdeadbeef00"));
        assert_eq!(module.literal_count, bytes.len());
        assert!(module.cert_theorem.ends_with("deadbeefdeadbeef00"));
        assert!(module.result_theorem.ends_with("deadbeefdeadbeef00"));
    }

    #[test]
    fn raw_literal_preserves_utf8_backslashes_and_delimiter_collisions() {
        let text = "quoted\"# and \"### plus \\ and λ\n";
        let literal = published_raw_literal(text.as_bytes()).expect("UTF-8");
        assert_eq!(literal, format!("r####\"{text}\"####"));
        assert!(!text.contains("\"####"));
        assert_eq!(published_raw_literal(b"").expect("empty"), "r#\"\"#");
    }

    #[test]
    fn raw_literal_rejects_invalid_utf8() {
        let error = published_raw_literal(&[0xff]).expect_err("invalid UTF-8");
        assert_eq!(error.code(), ErrorCode::NoncanonicalJson);
    }

    #[test]
    fn the_symmetric_module_carries_raw_published_bytes() {
        use mm_schema::symmetric::{encode_symmetric_omega, to_symmetric};
        let (certificate, _) = hand_fixture();
        let symmetric = to_symmetric(&certificate).expect("symmetric fixture");
        let mut bytes = Vec::new();
        encode_symmetric_omega(&mut bytes, &symmetric).expect("encode");
        let module = generate_symmetric(&symmetric, &bytes, "deadbeefdeadbeef00", Profile::Cn)
            .expect("generate symmetric");
        let text = std::str::from_utf8(&bytes).expect("UTF-8");
        assert!(module.source.contains(&format!("r#\"{text}\"#.toUTF8")));
        assert!(
            module
                .source
                .contains("acceptsSymOmegaDigest Limits.default symBytes_")
        );
        assert!(module.source.contains("omega_le_of_acceptsSymOmegaDigest"));
        assert!(module.source.contains("ByteArray.mk #[0xde, 0xad, 0xbe"));
        assert!(module.source.contains("MatrixMath.ResultAssurance.emit"));
        assert_eq!(module.source.matches("native_decide").count(), 1);
        assert_eq!(module.literal_count, bytes.len());
    }

    #[test]
    fn the_reported_claim_preserves_the_exact_rational_bound() {
        let (mut certificate, bytes) = hand_fixture();
        certificate.omega = mm_rat::Rat::from_signeds(2_372_001_237_939, 1_000_000_000_000);
        let module = generate(&certificate, &bytes, "ab", Profile::Cn).expect("generate");
        assert_eq!(module.claim, "omega <= 2372001237939/1000000000000");
    }

    /// A certificate whose node array does not match the instance tree is a
    /// count mismatch, caught before Lean is invoked (§5.2).
    #[test]
    fn a_node_array_that_does_not_match_the_tree_is_refused() {
        let (mut certificate, bytes) = hand_fixture();
        certificate.level = mm_core::level::Level::new(3).expect("level 3");
        let error = generate(&certificate, &bytes, "abc", Profile::Cn)
            .expect_err("an ℓ* = 2 node array is not an ℓ* = 3 tree");
        assert_eq!(error.code(), ErrorCode::CountMismatch);
        assert_eq!(error.equation_id(), Some("§5.2"));
    }

    /// A payload that does not match its position in canonical preorder is a
    /// malformed certificate, not something to coerce (§5.2).
    #[test]
    fn a_payload_that_disagrees_with_its_position_is_refused() {
        let (mut certificate, bytes) = hand_fixture();
        certificate.nodes[1] = mm_schema::NodePayload::LevelTwo {
            mu: mm_rat::Rat::zero(),
        };
        let error = generate(&certificate, &bytes, "abc", Profile::Cn).expect_err("must refuse");
        assert_eq!(error.code(), ErrorCode::BadPath);
        assert!(error.message().contains("disagrees with its position"));
    }
}
