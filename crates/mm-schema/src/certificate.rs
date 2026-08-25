//! The versioned certificate envelope and the decomposition certificate model
//! (spec §6.1, §6.6).
//!
//! Only fields affecting mathematical meaning belong in canonical certificate
//! bytes (§6.1). Producer git SHA, run ID, machine, timings, notes, and archive
//! URI live in the separate result manifest. Unknown fields are **rejected**,
//! not ignored, so a certificate cannot smuggle meaning past the checker.

use crate::reader::CanonicalReader;
use crate::writer::CanonicalWriter;
use malachite::Integer;
use mm_core::codes::ErrorCode;
use mm_core::dims::MatMulInstance;
use mm_core::error::{CoreError, CoreResult};
use mm_core::modulus::PrimeModulus;
use mm_core::{CERTIFICATE_SCHEMA, SOURCE_S1_SHA256, SOURCE_S2_SHA256, SPEC_VERSION};
use mm_rat::Rat;
use mm_tensor::decomposition::{Decomposition, Term};
use mm_tensor::ring::{
    ExactRing, Gaussian, GaussianRationalRing, IntegerRing, PrimeField, RationalRing, RingTag,
};
use std::io::{BufRead, Write};

/// The two certificate kinds of version 1 (§6.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateKind {
    /// An upper bound on the matrix multiplication exponent.
    Omega,
    /// An explicit tensor decomposition.
    Decomposition,
}

impl CertificateKind {
    /// The canonical wire string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Omega => "omega",
            Self::Decomposition => "decomposition",
        }
    }

    /// Parse a kind discriminator.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::SchemaMismatch`] for an unknown kind.
    pub fn parse(text: &str) -> CoreResult<Self> {
        match text {
            "omega" => Ok(Self::Omega),
            "decomposition" => Ok(Self::Decomposition),
            _ => Err(
                CoreError::new(ErrorCode::SchemaMismatch, "unknown certificate kind")
                    .equation("§6.1")
                    .value(text),
            ),
        }
    }
}

/// A decoded decomposition, resolved to its concrete ring.
#[derive(Clone, Debug)]
pub enum AnyDecomposition {
    /// Over the integers.
    Z(Decomposition<IntegerRing>),
    /// Over the rationals.
    Q(Decomposition<RationalRing>),
    /// Over a prime field.
    Fp(Decomposition<PrimeField>),
    /// Over the Gaussian rationals.
    Qi(Decomposition<GaussianRationalRing>),
}

impl AnyDecomposition {
    /// The instance this decomposition targets.
    #[must_use]
    pub fn instance(&self) -> MatMulInstance {
        match self {
            Self::Z(d) => d.instance(),
            Self::Q(d) => d.instance(),
            Self::Fp(d) => d.instance(),
            Self::Qi(d) => d.instance(),
        }
    }

    /// The number of terms; a term count, never a proven rank (§10.4).
    #[must_use]
    pub fn term_count(&self) -> usize {
        match self {
            Self::Z(d) => d.term_count(),
            Self::Q(d) => d.term_count(),
            Self::Fp(d) => d.term_count(),
            Self::Qi(d) => d.term_count(),
        }
    }

    /// The ring tag.
    #[must_use]
    pub fn ring_tag(&self) -> RingTag {
        match self {
            Self::Z(_) => RingTag::Z,
            Self::Q(_) => RingTag::Q,
            Self::Fp(_) => RingTag::Fp,
            Self::Qi(_) => RingTag::Qi,
        }
    }

    /// Verify reconstruction against the target tensor (B1).
    ///
    /// # Errors
    ///
    /// Propagates the first reconstruction mismatch.
    pub fn verify(&self) -> CoreResult<mm_tensor::DecompositionClaim> {
        match self {
            Self::Z(d) => mm_tensor::verify_decomposition(d),
            Self::Q(d) => mm_tensor::verify_decomposition(d),
            Self::Fp(d) => mm_tensor::verify_decomposition(d),
            Self::Qi(d) => mm_tensor::verify_decomposition(d),
        }
    }

    /// The total number of coefficients, folded over every term.
    ///
    /// This is the §6.8 "no-op fold": it visits every decoded value without
    /// deciding anything, so the spike times the streaming path rather than the
    /// reconstruction check.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ArithmeticOverflow`] if the count overflows.
    pub fn coefficient_count(&self) -> CoreResult<usize> {
        fn fold<R: ExactRing>(decomposition: &Decomposition<R>) -> CoreResult<usize> {
            let mut total = 0usize;
            for term in decomposition.terms() {
                for mode in mm_core::dims::TensorMode::ALL {
                    total = total.checked_add(term.factor(mode).len()).ok_or_else(|| {
                        CoreError::new(
                            ErrorCode::ArithmeticOverflow,
                            "coefficient count overflowed",
                        )
                    })?;
                }
            }
            Ok(total)
        }
        match self {
            Self::Z(d) => fold(d),
            Self::Q(d) => fold(d),
            Self::Fp(d) => fold(d),
            Self::Qi(d) => fold(d),
        }
    }

    /// Reject a non-canonical term order (§10.4).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::NoncanonicalTermOrder`] when the order is wrong.
    pub fn require_canonical_order(&self) -> CoreResult<()> {
        match self {
            Self::Z(d) => d.require_canonical_order(),
            Self::Q(d) => d.require_canonical_order(),
            Self::Fp(d) => d.require_canonical_order(),
            Self::Qi(d) => d.require_canonical_order(),
        }
    }
}

/// A fully decoded decomposition certificate together with its identity.
#[derive(Clone, Debug)]
pub struct DecompositionCertificate {
    /// The decoded decomposition.
    pub decomposition: AnyDecomposition,
    /// The SHA-256 of the canonical uncompressed bytes (§6.3).
    pub digest: [u8; 32],
    /// The canonical byte count.
    pub byte_count: u64,
}

impl DecompositionCertificate {
    /// The lowercase hexadecimal certificate identity (§6.3, §8.3).
    #[must_use]
    pub fn digest_hex(&self) -> String {
        mm_core::hex::encode_hex(&self.digest)
    }
}

/// Decode a decomposition certificate from canonical bytes (§6.1, §6.6).
///
/// Every redundant field is recomputed and cross-checked rather than trusted:
/// the declared term count must equal the decoded term count, and the declared
/// modulus must pass exact primality (§6.6).
///
/// # Errors
///
/// Returns the first structured rejection deterministically (§5.4).
pub fn decode_decomposition<R: BufRead>(
    reader: &mut CanonicalReader<R>,
) -> CoreResult<AnyDecomposition> {
    reader.begin_object()?;

    let mut claim: Option<ClaimFields> = None;
    let mut kind: Option<CertificateKind> = None;
    let mut payload: Option<AnyDecomposition> = None;
    let mut schema_seen = false;
    let mut sources_seen = false;
    let mut version_seen = false;

    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "claim" => claim = Some(decode_claim(reader)?),
            "kind" => {
                let text = reader.read_string()?;
                let parsed = CertificateKind::parse(&text)?;
                if parsed != CertificateKind::Decomposition {
                    return Err(CoreError::new(
                        ErrorCode::SchemaMismatch,
                        "expected a decomposition certificate",
                    )
                    .equation("§6.1")
                    .value(text));
                }
                kind = Some(parsed);
            }
            "payload" => {
                let claim = claim.as_ref().ok_or_else(|| {
                    CoreError::new(
                        ErrorCode::MissingField,
                        "\"claim\" must precede \"payload\" in canonical key order",
                    )
                    .equation("§6.3")
                })?;
                payload = Some(decode_payload(reader, claim)?);
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
                decode_source_hashes(reader)?;
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
            other => {
                return Err(CoreError::new(
                    ErrorCode::UnknownField,
                    "unknown certificate fields are rejected, never ignored",
                )
                .equation("§6.1")
                .at_byte(reader.offset())
                .value(other));
            }
        }
    }

    let claim = claim.ok_or_else(|| missing("claim"))?;
    kind.ok_or_else(|| missing("kind"))?;
    let decomposition = payload.ok_or_else(|| missing("payload"))?;
    if !schema_seen {
        return Err(missing("schema"));
    }
    if !sources_seen {
        return Err(missing("source_hashes"));
    }
    if !version_seen {
        return Err(missing("spec_version"));
    }

    if decomposition.term_count() != claim.term_count {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the declared term count disagrees with the decoded terms",
        )
        .equation("§6.6")
        .value(format!(
            "declared {} decoded {}",
            claim.term_count,
            decomposition.term_count()
        )));
    }
    decomposition.require_canonical_order()?;
    Ok(decomposition)
}

#[derive(Clone, Copy, Debug)]
struct ClaimFields {
    instance: MatMulInstance,
    term_count: usize,
}

fn decode_claim<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<ClaimFields> {
    reader.begin_object()?;
    let mut m = None;
    let mut n = None;
    let mut p = None;
    let mut term_count = None;
    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "m" => m = Some(reader.read_u16()?),
            "n" => n = Some(reader.read_u16()?),
            "p" => p = Some(reader.read_u16()?),
            "term_count" => term_count = Some(reader.read_u64()?),
            other => {
                return Err(
                    CoreError::new(ErrorCode::UnknownField, "unknown claim field")
                        .equation("§6.1")
                        .value(other),
                );
            }
        }
    }
    let instance = MatMulInstance::from_raw(
        n.ok_or_else(|| missing("claim.n"))?,
        m.ok_or_else(|| missing("claim.m"))?,
        p.ok_or_else(|| missing("claim.p"))?,
    )?;
    let term_count = usize::try_from(term_count.ok_or_else(|| missing("claim.term_count"))?)
        .map_err(|_| {
            CoreError::new(ErrorCode::ResourceLimit, "term count is out of range").equation("§6.4")
        })?;
    Ok(ClaimFields {
        instance,
        term_count,
    })
}

fn decode_source_hashes<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<()> {
    reader.begin_object()?;
    let mut s1 = false;
    let mut s2 = false;
    while let Some(key) = reader.next_key()? {
        let value = reader.read_string()?;
        let expected = match key.as_str() {
            "S1" => {
                s1 = true;
                SOURCE_S1_SHA256
            }
            "S2" => {
                s2 = true;
                SOURCE_S2_SHA256
            }
            other => {
                return Err(CoreError::new(
                    ErrorCode::UnknownField,
                    "unknown locked source identifier",
                )
                .equation("§0.1")
                .value(other));
            }
        };
        if value != expected {
            return Err(CoreError::new(
                ErrorCode::SourceHashMismatch,
                "a certificate source hash disagrees with the locked value",
            )
            .equation("§0.1")
            .value(key)
            .value(value));
        }
    }
    if !s1 || !s2 {
        return Err(missing("source_hashes.S1 and source_hashes.S2"));
    }
    Ok(())
}

fn decode_payload<R: BufRead>(
    reader: &mut CanonicalReader<R>,
    claim: &ClaimFields,
) -> CoreResult<AnyDecomposition> {
    reader.begin_object()?;
    let mut modulus: Option<PrimeModulus> = None;
    let mut result: Option<AnyDecomposition> = None;
    let mut ring: Option<RingTag> = None;

    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            // Canonical key order is modulus < ring < terms, so the ring is
            // always known before its coefficients are read.
            "modulus" => {
                let value = reader.read_u64()?;
                let narrowed = u32::try_from(value).map_err(|_| {
                    CoreError::new(
                        ErrorCode::UnsupportedInstance,
                        "the field modulus exceeds the supported range",
                    )
                    .equation("§0.2")
                })?;
                modulus = Some(PrimeModulus::new(narrowed)?);
            }
            "ring" => {
                let text = reader.read_string()?;
                ring = Some(RingTag::parse(&text)?);
            }
            "terms" => {
                let tag = ring.ok_or_else(|| missing("payload.ring"))?;
                result = Some(match tag {
                    RingTag::Z => AnyDecomposition::Z(decode_terms(
                        reader,
                        claim.instance,
                        IntegerRing,
                        read_integer_coefficient,
                    )?),
                    RingTag::Q => AnyDecomposition::Q(decode_terms(
                        reader,
                        claim.instance,
                        RationalRing,
                        read_rational_coefficient,
                    )?),
                    RingTag::Fp => {
                        let modulus = modulus.ok_or_else(|| missing("payload.modulus"))?;
                        AnyDecomposition::Fp(decode_terms(
                            reader,
                            claim.instance,
                            PrimeField::new(modulus),
                            read_field_coefficient,
                        )?)
                    }
                    RingTag::Qi => AnyDecomposition::Qi(decode_terms(
                        reader,
                        claim.instance,
                        GaussianRationalRing,
                        read_gaussian_coefficient,
                    )?),
                });
            }
            other => {
                return Err(
                    CoreError::new(ErrorCode::UnknownField, "unknown payload field")
                        .equation("§6.6")
                        .value(other),
                );
            }
        }
    }
    let tag = ring.ok_or_else(|| missing("payload.ring"))?;
    if tag == RingTag::Fp && modulus.is_none() {
        return Err(missing("payload.modulus"));
    }
    if tag != RingTag::Fp && modulus.is_some() {
        return Err(CoreError::new(
            ErrorCode::UnknownField,
            "\"modulus\" is meaningful only for the Fp ring",
        )
        .equation("§6.6"));
    }
    result.ok_or_else(|| missing("payload.terms"))
}

fn decode_terms<Rd, Rg, F>(
    reader: &mut CanonicalReader<Rd>,
    instance: MatMulInstance,
    ring: Rg,
    read_coefficient: F,
) -> CoreResult<Decomposition<Rg>>
where
    Rd: BufRead,
    Rg: ExactRing,
    F: Fn(&mut CanonicalReader<Rd>, &Rg) -> CoreResult<Rg::Elem>,
{
    reader.begin_array()?;
    let mut terms = Vec::new();
    let mut first = true;
    while reader.next_element(first)? {
        first = false;
        reader.begin_array()?;
        let mut factors: Vec<Vec<Rg::Elem>> = Vec::with_capacity(3);
        let mut factor_first = true;
        while reader.next_element(factor_first)? {
            factor_first = false;
            reader.begin_array()?;
            let mut values = Vec::new();
            let mut value_first = true;
            while reader.next_element(value_first)? {
                value_first = false;
                reader.count_rational()?;
                values.push(read_coefficient(reader, &ring)?);
            }
            factors.push(values);
        }
        if factors.len() != 3 {
            return Err(CoreError::new(
                ErrorCode::CountMismatch,
                "a term must have exactly three factors",
            )
            .equation("B1")
            .at_byte(reader.offset()));
        }
        let mut drain = factors.into_iter();
        let u = drain.next().unwrap_or_default();
        let v = drain.next().unwrap_or_default();
        let w = drain.next().unwrap_or_default();
        terms.push(Term::new(u, v, w));
    }
    Decomposition::new(instance, ring, terms)
}

fn read_integer_coefficient<R: BufRead>(
    reader: &mut CanonicalReader<R>,
    ring: &IntegerRing,
) -> CoreResult<Integer> {
    let text = reader.read_string()?;
    let value = ring.decode(&text)?;
    if ring.encode(&value) != text {
        return Err(noncanonical(reader.offset(), &text));
    }
    Ok(value)
}

fn read_field_coefficient<R: BufRead>(
    reader: &mut CanonicalReader<R>,
    ring: &PrimeField,
) -> CoreResult<u32> {
    let value = reader.read_u64()?;
    let narrowed = u32::try_from(value).map_err(|_| {
        CoreError::new(
            ErrorCode::BadRationalGrammar,
            "an Fp coefficient must lie in [0,p)",
        )
        .equation("§6.6")
    })?;
    if narrowed >= ring.modulus().get() {
        return Err(CoreError::new(
            ErrorCode::BadRationalGrammar,
            "an Fp coefficient must lie in [0,p)",
        )
        .equation("§6.6")
        .at_byte(reader.offset())
        .value(format!("{narrowed} >= {}", ring.modulus())));
    }
    Ok(narrowed)
}

fn read_rational_coefficient<R: BufRead>(
    reader: &mut CanonicalReader<R>,
    _ring: &RationalRing,
) -> CoreResult<Rat> {
    read_rational(reader)
}

fn read_gaussian_coefficient<R: BufRead>(
    reader: &mut CanonicalReader<R>,
    _ring: &GaussianRationalRing,
) -> CoreResult<Gaussian> {
    reader.begin_object()?;
    let mut im = None;
    let mut re = None;
    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "im" => im = Some(read_rational(reader)?),
            "re" => re = Some(read_rational(reader)?),
            other => {
                return Err(CoreError::new(
                    ErrorCode::UnknownField,
                    "a Gaussian has only \"re\" and \"im\"",
                )
                .equation("B.7")
                .value(other));
            }
        }
    }
    Ok(Gaussian::new(
        re.ok_or_else(|| missing("re"))?,
        im.ok_or_else(|| missing("im"))?,
    ))
}

/// Read one canonical rational object `{"d":"…","n":"…"}` (§6.2).
///
/// # Errors
///
/// Propagates grammar rejections.
pub fn read_rational<R: BufRead>(reader: &mut CanonicalReader<R>) -> CoreResult<Rat> {
    reader.begin_object()?;
    let mut denominator = None;
    let mut numerator = None;
    while let Some(key) = reader.next_key()? {
        match key.as_str() {
            "d" => denominator = Some(reader.read_string()?),
            "n" => numerator = Some(reader.read_string()?),
            other => {
                return Err(CoreError::new(
                    ErrorCode::UnknownField,
                    "a rational object has only \"n\" and \"d\"",
                )
                .equation("§6.2")
                .value(other));
            }
        }
    }
    Rat::decode_canonical(
        &numerator.ok_or_else(|| missing("n"))?,
        &denominator.ok_or_else(|| missing("d"))?,
    )
}

fn missing(field: &str) -> CoreError {
    CoreError::new(ErrorCode::MissingField, "a required field is absent")
        .equation("§6.1")
        .value(field)
}

fn noncanonical(offset: u64, text: &str) -> CoreError {
    CoreError::new(
        ErrorCode::NoncanonicalCoefficient,
        "a coefficient is not in canonical normal form",
    )
    .equation("§6.2")
    .at_byte(offset)
    .value(text)
}

/// Encode a decomposition as canonical certificate bytes (§6.1, §6.3, §6.6).
///
/// # Errors
///
/// Propagates write failures and canonical-order violations.
pub fn encode_decomposition<W: Write>(
    output: W,
    decomposition: &AnyDecomposition,
) -> CoreResult<([u8; 32], u64)> {
    let mut writer = CanonicalWriter::new(output);
    let instance = decomposition.instance();

    writer.begin_object()?;
    writer.key("claim")?;
    writer.begin_object()?;
    writer.key("m")?;
    writer.integer(u64::from(instance.m().get()))?;
    writer.key("n")?;
    writer.integer(u64::from(instance.n().get()))?;
    writer.key("p")?;
    writer.integer(u64::from(instance.p().get()))?;
    writer.key("term_count")?;
    writer.integer(decomposition.term_count() as u64)?;
    writer.end_object()?;

    writer.key("kind")?;
    writer.string(CertificateKind::Decomposition.as_str())?;

    writer.key("payload")?;
    writer.begin_object()?;
    match decomposition {
        AnyDecomposition::Fp(inner) => {
            writer.key("modulus")?;
            writer.integer(u64::from(inner.ring().modulus().get()))?;
            writer.key("ring")?;
            writer.string(RingTag::Fp.as_str())?;
            writer.key("terms")?;
            write_terms(&mut writer, inner)?;
        }
        AnyDecomposition::Z(inner) => {
            writer.key("ring")?;
            writer.string(RingTag::Z.as_str())?;
            writer.key("terms")?;
            write_terms(&mut writer, inner)?;
        }
        AnyDecomposition::Q(inner) => {
            writer.key("ring")?;
            writer.string(RingTag::Q.as_str())?;
            writer.key("terms")?;
            write_terms(&mut writer, inner)?;
        }
        AnyDecomposition::Qi(inner) => {
            writer.key("ring")?;
            writer.string(RingTag::Qi.as_str())?;
            writer.key("terms")?;
            write_terms(&mut writer, inner)?;
        }
    }
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

fn write_terms<W: Write, Rg: ExactRing>(
    writer: &mut CanonicalWriter<W>,
    decomposition: &Decomposition<Rg>,
) -> CoreResult<()> {
    let ring = decomposition.ring();
    writer.begin_array()?;
    for term in decomposition.terms() {
        writer.begin_array()?;
        for mode in mm_core::dims::TensorMode::ALL {
            writer.begin_array()?;
            for value in term.factor(mode) {
                writer.raw_value(&ring.encode_json(value))?;
            }
            writer.end_array()?;
        }
        writer.end_array()?;
    }
    writer.end_array()
}
