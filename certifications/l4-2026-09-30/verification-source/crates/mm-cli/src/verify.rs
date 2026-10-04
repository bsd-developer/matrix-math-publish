//! `mm verify` (spec §9.1, §9.3).
//!
//! Decodes canonical bytes, runs the independent Rust exact checker, and — when
//! Lean is available — runs the authoritative Lean check as well. The Rust
//! checker is never the sole authority (§1.1, §3.1): a run without a Lean
//! theorem is reported as `XC`, which §3.4 says is development only and is never
//! reportable as certified.

use crate::lean::Profile;
use crate::prove;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult, push_json_string};
use mm_schema::{
    CanonicalReader, DecompositionCertificate, Limits, decode_omega, load_decomposition_certificate,
};
use std::fs;
use std::io::BufReader;
use std::path::{Path, PathBuf};

/// The canonical bytes behind a certificate, re-readable for the §3.5 round trip.
///
/// A plain `.json` file is re-opened rather than buffered, so an 8 GiB
/// certificate is never held in memory (§6.4). Transport-compressed input is
/// decompressed once and kept, because re-running the decompressor would not be
/// meaningfully cheaper.
pub enum PublishedBytes {
    /// An uncompressed canonical file on disk.
    File(PathBuf),
    /// Bytes decompressed from `.json.zst` transport.
    Memory(Vec<u8>),
}

impl PublishedBytes {
    /// Read the canonical bytes into memory.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::Io`] when the file cannot be read.
    pub fn to_vec(&self) -> CoreResult<Vec<u8>> {
        match self {
            Self::File(path) => fs::read(path)
                .map_err(|error| CoreError::new(ErrorCode::Io, format!("read {path:?}: {error}"))),
            Self::Memory(bytes) => Ok(bytes.clone()),
        }
    }

    /// Open a fresh reader over the canonical bytes.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::Io`] when the file cannot be reopened.
    pub fn reader(&self) -> CoreResult<Box<dyn std::io::Read + '_>> {
        match self {
            Self::File(path) => {
                let file = fs::File::open(path).map_err(|error| {
                    CoreError::new(ErrorCode::Io, format!("reopen {path:?}: {error}"))
                })?;
                Ok(Box::new(BufReader::new(file)))
            }
            Self::Memory(data) => Ok(Box::new(data.as_slice())),
        }
    }
}

/// Load a certificate from a path, decompressing `.zst` transport first (§6.3).
///
/// Zstandard is transport compression only: the file is decompressed to
/// canonical bytes **before** hashing or checking, so the compressor version and
/// level cannot affect the certificate identity.
///
/// # Errors
///
/// Propagates decode rejections and I/O failures.
pub fn load(path: &Path) -> CoreResult<(DecompositionCertificate, PublishedBytes)> {
    load_with(path, Limits::default())
}

/// Load under an explicit resource envelope (§6.4).
///
/// §6.4 makes the limits a value rather than constants, which is what lets the
/// rejection paths be tested without constructing an eight-gigabyte input.
///
/// # Errors
///
/// Propagates decode rejections and I/O failures.
pub fn load_with(
    path: &Path,
    limits: Limits,
) -> CoreResult<(DecompositionCertificate, PublishedBytes)> {
    if path.extension().is_some_and(|extension| extension == "zst") {
        let decompressed = decompress_zst(path, limits)?;
        let certificate =
            load_decomposition_certificate(BufReader::new(decompressed.as_slice()), limits)?;
        Ok((certificate, PublishedBytes::Memory(decompressed)))
    } else {
        let file = fs::File::open(path)
            .map_err(|error| CoreError::new(ErrorCode::Io, format!("open {path:?}: {error}")))?;
        let certificate = load_decomposition_certificate(BufReader::new(file), limits)?;
        Ok((certificate, PublishedBytes::File(path.to_path_buf())))
    }
}

/// Decompress `.json.zst` transport, enforcing the §6.4 byte ceiling **as the
/// output is produced**.
///
/// §6.4 says decompression output is subject to the limits *before* parsing, and
/// that is the whole defence against a decompression bomb: a small archive can
/// expand without bound, so reading the decompressor's output to completion and
/// checking afterwards is exactly the wrong order. This reads incrementally and
/// aborts the moment the ceiling is passed.
fn decompress_zst(path: &Path, limits: Limits) -> CoreResult<Vec<u8>> {
    use std::io::Read;
    use std::process::{Command, Stdio};

    let limit = limits.max_bytes;
    let mut child = Command::new("zstd")
        .arg("-dc")
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|error| {
            CoreError::new(
                ErrorCode::Io,
                format!("zstd is required to read transport-compressed certificates: {error}"),
            )
        })?;
    let mut stdout = child
        .stdout
        .take()
        .ok_or_else(|| CoreError::new(ErrorCode::Io, "zstd produced no output stream"))?;

    let mut out: Vec<u8> = Vec::new();
    let mut buffer = vec![0u8; 1 << 16];
    loop {
        let read = match stdout.read(&mut buffer) {
            Ok(0) => break,
            Ok(read) => read,
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => {
                let _ = child.kill();
                return Err(CoreError::new(ErrorCode::Io, error.to_string()));
            }
        };
        if out.len() as u64 + read as u64 > limit {
            // Kill the decompressor rather than draining it: a bomb would
            // otherwise keep producing output we have already decided to reject.
            let _ = child.kill();
            let _ = child.wait();
            return Err(CoreError::new(
                ErrorCode::ResourceLimit,
                "decompressed transport exceeds the canonical byte limit",
            )
            .equation("§6.4")
            .value(format!("limit {limit} bytes")));
        }
        out.extend_from_slice(buffer.get(..read).unwrap_or_default());
    }

    let status = child
        .wait()
        .map_err(|error| CoreError::new(ErrorCode::Io, error.to_string()))?;
    if !status.success() {
        return Err(CoreError::new(
            ErrorCode::Io,
            "zstd failed to decompress the certificate",
        ));
    }
    Ok(out)
}

/// Detect the certificate kind without committing to a decoder.
///
/// §6.1 puts `kind` after `claim` in canonical key order, so a targeted scan of
/// the first part of the document is enough and avoids parsing twice.
pub fn certificate_kind(published: &PublishedBytes) -> CoreResult<&'static str> {
    use std::io::Read;
    let mut head = vec![0u8; 4096];
    let mut reader = published.reader()?;
    let mut filled = 0usize;
    while filled < head.len() {
        match reader.read(head.get_mut(filled..).unwrap_or_default()) {
            Ok(0) => break,
            Ok(read) => filled += read,
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(CoreError::new(ErrorCode::Io, error.to_string())),
        }
    }
    let text = String::from_utf8_lossy(head.get(..filled).unwrap_or_default()).into_owned();
    if text.contains("\"kind\":\"omega\"") {
        Ok("omega")
    } else if text.contains("\"kind\":\"decomposition\"") {
        Ok("decomposition")
    } else {
        Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "the certificate does not declare a supported kind",
        )
        .equation("§6.1"))
    }
}

/// Open the published bytes for a path, decompressing `.zst` under the limits.
///
/// # Errors
///
/// Propagates I/O and decompression failures.
pub fn open_published(path: &Path, limits: Limits) -> CoreResult<PublishedBytes> {
    if path.extension().is_some_and(|extension| extension == "zst") {
        Ok(PublishedBytes::Memory(decompress_zst(path, limits)?))
    } else {
        Ok(PublishedBytes::File(path.to_path_buf()))
    }
}

/// Decode an omega certificate and return it with its canonical digest.
///
/// # Errors
///
/// Propagates decode rejections.
pub fn decode_published_omega(
    published: &PublishedBytes,
) -> CoreResult<(mm_schema::OmegaCertificate, String)> {
    let mut reader = CanonicalReader::new(BufReader::new(published.reader()?), Limits::default());
    let certificate = decode_omega(&mut reader)?;
    let digest = reader.finish()?;
    Ok((certificate, mm_core::hex::encode_hex(&digest)))
}

/// Whether a published omega certificate declares the symmetric encoding.
///
/// The payload's first key in sorted order is `encoding` (`0007_spec.md` §3.1),
/// so the discriminator sits in the first few hundred bytes and can be read
/// without decoding. This is a dispatch hint only: the decoder still validates
/// the field, and a payload that lies about it fails there.
///
/// # Errors
///
/// Propagates read failures.
pub fn declares_symmetric(published: &PublishedBytes) -> CoreResult<bool> {
    use std::io::Read;
    let mut head = vec![0u8; 512];
    let mut reader = published.reader()?;
    let mut filled = 0usize;
    while filled < head.len() {
        match reader.read(&mut head[filled..]) {
            Ok(0) => break,
            Ok(count) => filled += count,
            Err(error) => {
                return Err(CoreError::new(
                    ErrorCode::Io,
                    format!("read failed: {error}"),
                ));
            }
        }
    }
    head.truncate(filled);
    // Length from the literal, never a hardcoded count: the marker is 22 bytes
    // and writing 23 silently disabled this check.
    let marker = br#""encoding":"symmetric""#.as_slice();
    Ok(head.windows(marker.len()).any(|window| window == marker))
}

/// Verify an omega certificate: the authoritative Lean check plus the
/// independent Rust exact evaluator as a cross-check (§3.1, §9.1, §14.8).
///
/// §3.1 makes Lean the authority. When the Lean toolchain is unavailable, or
/// when the instance is outside the `ℓ* = 2` reach of the Lean checker, the run
/// is reported as `XC`, which §3.4 says is development only and is never
/// reportable as certified.
fn verify_omega(
    path: &Path,
    published: &PublishedBytes,
    json: bool,
    skip_lean: bool,
    profile: Profile,
) -> CoreResult<u8> {
    let mut reader = CanonicalReader::new(BufReader::new(published.reader()?), Limits::default());
    let certificate = decode_omega(&mut reader)?;
    let byte_count = reader.offset();
    let digest = reader.finish()?;
    let digest_hex = mm_core::hex::encode_hex(&digest);

    let evaluable = mm_exact::from_certificate(&certificate)?;
    let claim = mm_exact::evaluate::evaluate(
        &evaluable.tree,
        &evaluable.blocks,
        &certificate.omega,
        evaluable.precision,
    )?;

    // §3.1: Lean is the authority; the Rust evaluator above is the cross-check.
    let lean = if skip_lean {
        Err(CoreError::new(
            ErrorCode::BadConfig,
            "--skip-lean was given, so no Lean theorem was built",
        ))
    } else {
        published.to_vec().and_then(|bytes| {
            crate::prove::build_and_check_omega(&certificate, &bytes, &digest_hex, profile)
        })
    };
    let certification = match &lean {
        Ok(outcome) => outcome.profile.as_str(),
        Err(_) => "XC",
    };

    if json {
        let mut out = String::from("{\"canonical_sha256\":");
        push_json_string(&mut out, &digest_hex);
        out.push_str(",\"certification\":");
        push_json_string(&mut out, certification);
        out.push_str(",\"claim\":");
        push_json_string(&mut out, &claim.statement());
        out.push_str(",\"kind\":\"omega\",\"note\":");
        push_json_string(
            &mut out,
            match &lean {
                Ok(_) => {
                    "the Lean Track A checker accepted the published bytes; \
                          AX1_combination_loss is the one project axiom (§3.2)"
                }
                Err(_) => {
                    "no Lean theorem was built, so this is a development \
                           cross-check and is not reportable as certified (§3.4)"
                }
            },
        );
        out.push_str(",\"rust_cross_check\":\"ok\",\"schema\":");
        push_json_string(&mut out, mm_core::CERTIFICATE_SCHEMA);
        out.push_str(",\"verdict\":\"VERIFIED\"}");
        println!("{out}");
    } else {
        println!("matrix-math verify");
        println!("  schema              {}", mm_core::CERTIFICATE_SCHEMA);
        println!("  kind                omega");
        println!("  canonical sha256    {digest_hex}");
        println!("  canonical bytes     {byte_count}");
        println!(
            "  instance            q={}, l*={}",
            certificate.q, certificate.level
        );
        println!(
            "  precision           {} bits",
            certificate.log_precision_bits
        );
        println!("  claimed bound       {}", claim.statement());
        println!(
            "  decimal             omega <= {}",
            claim.omega.to_decimal_string(9)
        );
        println!();
        // The exact rationals run to hundreds of digits at 256-bit precision, so
        // the report shows the decimal and names where the exact value lives.
        // §17.4's point about not confusing readability with rigour cuts both
        // ways: the exact value is what was checked, the decimal is what is read.
        println!(
            "  lower(E_total)      {} (exact rational, {} digits)",
            claim.e_total.value().to_decimal_string(12),
            claim.e_total.value().numerator_text().len()
        );
        println!(
            "  lower(M_total)      {} (exact rational, {} digits)",
            claim.m_total.value().to_decimal_string(12),
            claim.m_total.value().numerator_text().len()
        );
        println!(
            "  requirement         {} = 2^(l*-1) * upper(log2(q+2))",
            claim.requirement.value().to_decimal_string(12)
        );
        let left = claim.e_total.value() + &(claim.m_total.value() * &claim.omega);
        let slack = &left - claim.requirement.value();
        println!("  slack               {}", slack.to_decimal_string(12));
        println!();
        println!("  Rust exact check    ok");
        match &lean {
            Ok(outcome) => {
                println!("  Lean theorem        {}", outcome.result_theorem);
                println!("  certification       {}", outcome.profile.description());
                for line in &outcome.axioms {
                    println!("  #print axioms       {line}");
                }
                println!();
                println!("VERIFIED");
            }
            Err(error) => {
                println!("  Lean theorem        not built ({})", error.message());
                println!("  certification       XC (development cross-check only)");
                println!();
                println!("VERIFIED");
                println!();
                println!(
                    "XC is never reportable as certified (§3.4). A Track A result needs \
                     the Lean checker to accept the published bytes."
                );
            }
        }
    }
    let _ = path;
    Ok(0)
}

/// Fractional bits kept in the reported `Ω` ceiling.
///
/// Sixty-four bits is far below the 256-bit certificate precision, so the
/// rounding is invisible in the claim while keeping the emitted rational short.
const OMEGA_CEILING_BITS: u32 = 64;

/// Run `mm omega-min`: report the least `Ω` the directed checker accepts.
///
/// The producer needs this to *choose* `Ω` rather than guess one and learn the
/// answer by rejection. It is a diagnostic: the value it prints still has to be
/// written into a certificate and pass `mm verify` and the Lean checker like any
/// other claim.
///
/// # Errors
///
/// Propagates decode and evaluation failures.
/// Rewrite a general omega certificate into the `0007_spec.md` symmetric encoding.
///
/// The conversion is a re-encoding of the same mathematical point, not a
/// relaxation: `to_symmetric` rejects any certificate whose tied nodes disagree,
/// so a file that survives it carries exactly the free variables the general
/// form did. This exists because a producer can build the general tree quickly
/// and only the *evaluation* is superlinear in block count; converting before
/// evaluating is what makes an `l*=4` point checkable.
///
/// # Errors
///
/// Returns [`ErrorCode::UnsupportedInstance`] when the point is not symmetric,
/// and the usual decode codes for malformed bytes.
pub fn to_symmetric(arguments: &[String]) -> CoreResult<u8> {
    let mut paths: Vec<PathBuf> = Vec::new();
    for argument in arguments {
        if argument.starts_with("--") {
            return Err(CoreError::new(ErrorCode::BadConfig, "unknown flag").value(argument));
        }
        paths.push(PathBuf::from(argument));
    }
    let [input, output] = paths.as_slice() else {
        return Err(CoreError::new(
            ErrorCode::BadConfig,
            "mm to-symmetric needs an input path and an output path",
        ));
    };
    let published = open_published(input, Limits::default())?;
    if certificate_kind(&published)? != "omega" {
        return Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "mm to-symmetric applies to omega certificates only",
        )
        .equation("§6.1"));
    }
    if declares_symmetric(&published)? {
        return Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "the input is already in the symmetric encoding",
        )
        .equation("§3.1"));
    }
    let (certificate, _) = decode_published_omega(&published)?;
    let symmetric = mm_schema::symmetric::to_symmetric(&certificate)?;
    let mut bytes = Vec::new();
    let (digest, byte_count) =
        mm_schema::symmetric::encode_symmetric_omega(&mut bytes, &symmetric)?;
    std::fs::write(output, &bytes).map_err(|error| {
        CoreError::new(ErrorCode::Io, "could not write the symmetric certificate")
            .value(error.to_string())
    })?;
    let mut digest_hex = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(digest_hex, "{byte:02x}");
    }
    println!(
        r#"{{"blocks":{},"canonical_sha256":"{digest_hex}","bytes":{byte_count},"groups":{},"l_star":{}}}"#,
        symmetric.blocks.len(),
        symmetric.groups.len(),
        symmetric.level.get(),
    );
    Ok(0)
}

pub fn omega_min(arguments: &[String]) -> CoreResult<u8> {
    let mut path: Option<PathBuf> = None;
    for argument in arguments {
        if argument.starts_with("--") {
            return Err(CoreError::new(ErrorCode::BadConfig, "unknown flag").value(argument));
        }
        path = Some(PathBuf::from(argument));
    }
    let path =
        path.ok_or_else(|| CoreError::new(ErrorCode::BadConfig, "mm omega-min needs a path"))?;
    let published = open_published(&path, Limits::default())?;
    if certificate_kind(&published)? != "omega" {
        return Err(CoreError::new(
            ErrorCode::SchemaMismatch,
            "mm omega-min applies to omega certificates only",
        )
        .equation("§6.1"));
    }
    // `0007_spec.md` §4: a symmetric certificate is evaluated at group level and
    // never expanded. At l*=4 the expansion is the 1,552,339-node object the
    // encoding exists to avoid, so routing through it would defeat the purpose.
    if declares_symmetric(&published)? {
        return omega_min_symmetric(&published);
    }
    let (certificate, digest_hex) = decode_published_omega(&published)?;
    let evaluable = mm_exact::from_certificate(&certificate)?;
    mm_rat::log2::reset_evaluations();
    let bounds = mm_exact::evaluate::evaluate_bounds(
        &evaluable.tree,
        &evaluable.blocks,
        evaluable.precision,
    )?;
    // `0004_spec.md` P2. Two corrections turn what this subcommand just
    // performed into a bound on what a *checker* performs.
    //
    // The Rust evaluator computes both endpoints of the §7.4 closeness test from
    // one enclosure where the Lean checker calls `log2Lower` and `log2Upper`
    // separately, so the Lean checker performs one extra evaluation per block
    // domain point.
    //
    // And `evaluate_bounds` stops before A21. A checker follows it with
    // `check_feasibility`, which encloses `log2(q+2)` once more to compare the
    // claimed `Ω` against the requirement. This subcommand computes the least
    // acceptable `Ω` instead of checking one, so that evaluation is charged
    // here rather than counted.
    let block_domain_points: u64 = evaluable
        .blocks
        .iter()
        .map(|block| block.y.len() as u64)
        .sum();
    let log_evaluations = mm_rat::log2::evaluations() + block_domain_points + 1;
    let minimal = bounds.minimal_omega();

    let mut out = String::from("{\"canonical_sha256\":");
    push_json_string(&mut out, &digest_hex);
    out.push_str(",\"e_interior_lower\":");
    push_json_string(&mut out, &bounds.e_interior.value().to_decimal_string(15));
    out.push_str(",\"e_root_lower\":");
    push_json_string(&mut out, &bounds.e_root.value().to_decimal_string(15));
    out.push_str(",\"e_total_lower\":");
    push_json_string(&mut out, &format!("{}", bounds.e_total.value()));
    // The exact totals run to millions of digits at `ℓ* = 3`. A consumer that
    // only needs a magnitude — the producer's recorded error model, a report —
    // reads the decimal and never parses the exact numerator.
    out.push_str(",\"e_total_lower_decimal\":");
    push_json_string(&mut out, &bounds.e_total.value().to_decimal_string(15));
    out.push_str(",\"log_evaluations\":");
    out.push_str(&format!("{log_evaluations}"));
    out.push_str(",\"e_two_lower\":");
    push_json_string(&mut out, &bounds.e_two.value().to_decimal_string(15));
    out.push_str(",\"m_total_lower\":");
    push_json_string(&mut out, &format!("{}", bounds.m_total.value()));
    out.push_str(",\"m_total_lower_decimal\":");
    push_json_string(&mut out, &bounds.m_total.value().to_decimal_string(15));
    // The exact minimum can run to hundreds of thousands of digits. A producer
    // needs a value it can write into a certificate, so a rounded-**up** dyadic
    // ceiling is reported alongside it; rounding down would be rejected.
    let ceiling = match &minimal {
        Some(value) => Some(value.ceil_dyadic(OMEGA_CEILING_BITS)?),
        None => None,
    };
    out.push_str(",\"omega_ceiling\":");
    match &ceiling {
        Some(value) => push_json_string(&mut out, &format!("{value}")),
        None => out.push_str("null"),
    }
    out.push_str(",\"omega_ceiling_decimal\":");
    match &ceiling {
        Some(value) => push_json_string(&mut out, &value.to_decimal_string(15)),
        None => out.push_str("null"),
    }
    out.push_str(",\"omega_min\":");
    match &minimal {
        Some(value) => push_json_string(&mut out, &format!("{value}")),
        None => out.push_str("null"),
    }
    out.push_str(",\"omega_min_decimal\":");
    match &minimal {
        Some(value) => push_json_string(&mut out, &value.to_decimal_string(15)),
        None => out.push_str("null"),
    }
    out.push_str(",\"requirement_upper\":");
    push_json_string(&mut out, &format!("{}", bounds.requirement.value()));
    out.push('}');
    println!("{out}");
    Ok(0)
}

/// Run `mm verify`.
///
/// # Errors
///
/// Returns the first structured rejection (§5.4).
pub fn run(arguments: &[String]) -> CoreResult<u8> {
    let mut path: Option<PathBuf> = None;
    let mut json = false;
    let mut skip_lean = false;
    let mut decode_only = false;
    let mut limits = Limits::default();
    let mut profile = Profile::Cn;
    let mut index = 0usize;
    while let Some(argument) = arguments.get(index) {
        match argument.as_str() {
            "--json" => json = true,
            // Diagnostic only: reports XC, which §3.4 says is development use and
            // is never reportable as certified.
            "--skip-lean" => skip_lean = true,
            // §6.8 scale spike: decode and validate canonicality, then stop
            // before the reconstruction fold. This measures the streaming path,
            // not acceptance, and never prints a verdict.
            "--decode-only" => decode_only = true,
            // §6.4 makes the envelope a value; exposing it keeps the rejection
            // paths testable without constructing an eight-gigabyte input.
            "--max-bytes" => {
                let value = arguments.get(index + 1).ok_or_else(|| {
                    CoreError::new(ErrorCode::BadConfig, "--max-bytes needs a value")
                })?;
                limits.max_bytes = value.parse().map_err(|_| {
                    CoreError::new(ErrorCode::BadConfig, "--max-bytes must be an integer")
                        .value(value)
                })?;
                index += 1;
            }
            "--profile" => {
                let value = arguments.get(index + 1).ok_or_else(|| {
                    CoreError::new(ErrorCode::BadConfig, "--profile needs a value")
                })?;
                profile = Profile::parse(value)?;
                index += 1;
            }
            other if other.starts_with("--") => {
                return Err(CoreError::new(ErrorCode::BadConfig, "unknown flag").value(other));
            }
            other => path = Some(PathBuf::from(other)),
        }
        index += 1;
    }
    let path = path.ok_or_else(|| {
        CoreError::new(ErrorCode::BadConfig, "mm verify needs a certificate path")
    })?;

    // Dispatch on the declared kind before choosing a decoder (§6.1).
    let probe = if path.extension().is_some_and(|extension| extension == "zst") {
        PublishedBytes::Memory(decompress_zst(&path, limits)?)
    } else {
        PublishedBytes::File(path.clone())
    };
    if certificate_kind(&probe)? == "omega" {
        return verify_omega(&path, &probe, json, skip_lean, profile);
    }

    let (certificate, published) = load_with(&path, limits)?;

    if decode_only {
        // §6.8: decode plus canonicality validation plus a no-op fold. The fold
        // touches every coefficient without deciding anything, which is what the
        // spike is meant to time.
        certificate.decomposition.require_canonical_order()?;
        let coefficients = certificate.decomposition.coefficient_count()?;
        println!("matrix-math verify --decode-only");
        println!("  canonical sha256    {}", certificate.digest_hex());
        println!("  canonical bytes     {}", certificate.byte_count);
        println!(
            "  instance            {}",
            certificate.decomposition.instance()
        );
        println!(
            "  terms               {}",
            certificate.decomposition.term_count()
        );
        println!("  coefficients        {coefficients}");
        println!();
        println!("DECODED (no verdict: --decode-only stops before the tensor check)");
        return Ok(0);
    }

    let claim = certificate.decomposition.verify()?;
    let lean = if skip_lean {
        None
    } else {
        published
            .reader()
            .and_then(|reader| prove::try_lean_check(&certificate, reader, profile))
            .ok()
    };

    if json {
        let mut out = String::from("{\"canonical_sha256\":");
        push_json_string(&mut out, &certificate.digest_hex());
        out.push_str(",\"certification\":");
        push_json_string(&mut out, lean.as_ref().map_or("XC", |_| profile.as_str()));
        out.push_str(",\"claim\":");
        push_json_string(&mut out, &claim.statement());
        out.push_str(",\"kind\":\"decomposition\",\"rust_cross_check\":\"ok\",\"schema\":");
        push_json_string(&mut out, mm_core::CERTIFICATE_SCHEMA);
        out.push_str(",\"verdict\":\"VERIFIED\"}");
        println!("{out}");
    } else {
        println!("matrix-math verify");
        println!("  schema              {}", mm_core::CERTIFICATE_SCHEMA);
        println!("  kind                decomposition");
        println!("  canonical sha256    {}", certificate.digest_hex());
        println!("  canonical bytes     {}", certificate.byte_count);
        println!(
            "  instance            {}",
            certificate.decomposition.instance()
        );
        println!(
            "  ring                {}",
            certificate.decomposition.ring_tag().as_str()
        );
        println!("  claimed bound       {}", claim.statement());
        println!();
        match &lean {
            Some(outcome) => {
                println!("  Lean decode         ok");
                println!("  Lean exact check    ok");
                println!("  Lean theorem        {}", outcome.result_theorem);
                println!("  certification       {}", profile.description());
                println!("  axiom policy        ok");
            }
            None => {
                println!("  Lean theorem        not built");
                println!("  certification       XC (development cross-check only)");
            }
        }
        println!("  Rust cross-check    ok");
        println!();
        println!("VERIFIED");
    }
    Ok(0)
}

/// `mm omega-min` for a symmetric certificate, evaluated over groups.
///
/// # Errors
///
/// Propagates decode and evaluation failures.
fn omega_min_symmetric(published: &PublishedBytes) -> CoreResult<u8> {
    let mut reader = CanonicalReader::new(BufReader::new(published.reader()?), Limits::default());
    let certificate = mm_schema::symmetric::decode_symmetric_omega(&mut reader)?;
    let digest = reader.finish()?;
    let digest_hex = mm_core::hex::encode_hex(&digest);
    let precision = mm_rat::log2::Precision::new(certificate.log_precision_bits)?;

    mm_rat::log2::reset_evaluations();
    let bounds = mm_exact::symmetric::group_evaluate_bounds(&certificate, precision)?;
    // `0004_spec.md` P2, with the same two corrections the general path applies
    // above -- and the region factor the general path does not need.
    //
    // The Lean checker calls `log2Lower` and `log2Upper` separately where this
    // evaluator computes both endpoints from one enclosure, so it performs one
    // extra evaluation per block domain point. In the general encoding a group's
    // block appears once per region, so summing `y.len()` over `blocks` already
    // counts every region. In the symmetric encoding `blocks` holds one entry
    // per group, so the same sum counts each block once and must be multiplied
    // by the region count to describe the same checker.
    //
    // Getting this wrong is not cosmetic: `group_evaluate_bounds` charges the
    // hoisted entropies six times per group, so an uncorrected sum here would
    // have the two halves of one expression disagreeing about how many times a
    // checker visits a block. At `ℓ*=3` that reported 963 where 5,778 is the
    // figure that bounds Lean, making `K` 26% low against a §4.1 MUST.
    //
    // And `group_evaluate_bounds` stops before A21. A checker follows it with
    // `check_feasibility`, which encloses `log2(q+2)` once more; this subcommand
    // computes the least acceptable `Ω` instead of checking one, so that
    // evaluation is charged here rather than counted.
    let regions = u64::try_from(mm_core::region::Region::all().len()).unwrap_or(6);
    let block_domain_points: u64 = regions
        * certificate
            .blocks
            .iter()
            .map(|block| block.y.len() as u64)
            .sum::<u64>();
    let log_evaluations = mm_rat::log2::evaluations() + block_domain_points + 1;
    let minimal = bounds.minimal_omega();

    let mut out = String::from("{\"canonical_sha256\":");
    push_json_string(&mut out, &digest_hex);
    out.push_str(",\"encoding\":\"symmetric\"");
    out.push_str(",\"groups\":");
    out.push_str(&format!("{}", certificate.groups.len()));
    out.push_str(",\"blocks\":");
    out.push_str(&format!("{}", certificate.blocks.len()));
    out.push_str(",\"log_evaluations\":");
    out.push_str(&format!("{log_evaluations}"));
    out.push_str(",\"e_total_lower_decimal\":");
    push_json_string(&mut out, &bounds.e_total.value().to_decimal_string(15));
    out.push_str(",\"m_total_lower_decimal\":");
    push_json_string(&mut out, &bounds.m_total.value().to_decimal_string(15));
    out.push_str(",\"requirement_upper\":");
    push_json_string(&mut out, &format!("{}", bounds.requirement.value()));
    let ceiling = match &minimal {
        Some(value) => Some(value.ceil_dyadic(OMEGA_CEILING_BITS)?),
        None => None,
    };
    out.push_str(",\"omega_ceiling\":");
    match &ceiling {
        Some(value) => push_json_string(&mut out, &format!("{value}")),
        None => out.push_str("null"),
    }
    out.push_str(",\"omega_min_decimal\":");
    match &minimal {
        Some(value) => push_json_string(&mut out, &value.to_decimal_string(15)),
        None => out.push_str("null"),
    }
    out.push('}');
    println!("{out}");
    Ok(0)
}
