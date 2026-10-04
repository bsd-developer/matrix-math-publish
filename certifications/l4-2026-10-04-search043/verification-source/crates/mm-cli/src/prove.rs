//! `mm prove` (spec §3.5, §9.2, §9.3).
//!
//! Emits the certificate-specific Lean module, enforces the §3.5 byte-for-byte
//! round trip, invokes Lean, captures `#print axioms`, and validates the axiom
//! set against the requested profile's policy (§3.4).

use crate::lean::{GeneratedModule, Profile, generate};
use crate::roundtrip::CompareWriter;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult, push_json_string};
use mm_registry::TcbLedger;
use mm_schema::{DecompositionCertificate, encode_decomposition};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

/// The outcome of a successful certificate-specific proof.
#[derive(Clone, Debug)]
pub struct ProofOutcome {
    /// The generated module's path on disk.
    pub module_path: PathBuf,
    /// The fully qualified Lean module name.
    pub module_name: String,
    /// The closed-evaluation theorem name.
    pub cert_theorem: String,
    /// The published result theorem name.
    pub result_theorem: String,
    /// The exact mathematical claim.
    pub claim: String,
    /// The certification profile actually achieved.
    pub profile: Profile,
    /// The raw `#print axioms` lines Lean emitted.
    pub axioms: Vec<String>,
    /// The TCB ledger for this result.
    pub tcb: TcbLedger,
    /// Compiled result-local facts and source bindings for Track A (§4.6).
    pub compiled_assurance: Option<CompiledAssurance>,
}

/// Compiled Track A declaration evidence, obtained during the proof invocation.
#[derive(Clone, Debug)]
pub struct CompiledAssurance {
    /// Canonical JSON emitted by the Lean compiled-environment query.
    pub json: String,
    /// Handwritten Lean source closure, using the core assurance audit algorithm.
    pub lean_source_closure: String,
    /// SHA-256 of the generated module checked during this invocation.
    pub generated_module_sha256: String,
}

fn repo_root() -> CoreResult<PathBuf> {
    let mut current = std::env::current_dir()
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("current dir: {error}")))?;
    loop {
        if current.join("lean").join("lakefile.toml").is_file() {
            return Ok(current);
        }
        if !current.pop() {
            return Err(CoreError::new(
                ErrorCode::Io,
                "run mm from inside the matrix-math repository",
            ));
        }
    }
}

/// Enforce the §3.5 round trip: re-encode the decoded typed values and require
/// byte-for-byte equality with the published canonical bytes.
///
/// This is what binds the proof package to the published artifact. It is a
/// provenance check, not a soundness check: even a mismatched generator would
/// still have to satisfy the closed Lean checker.
///
/// The comparison streams, so it holds neither side in memory (§6.4).
///
/// # Errors
///
/// Returns [`ErrorCode::ImplementationDisagreement`] when the round trip differs.
fn require_round_trip(
    certificate: &DecompositionCertificate,
    published: impl std::io::Read,
) -> CoreResult<()> {
    let mut comparator = CompareWriter::new(published);
    let (digest, byte_count) = encode_decomposition(&mut comparator, &certificate.decomposition)?;
    comparator.finish()?;
    if digest != certificate.digest || byte_count != certificate.byte_count {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "the re-encoded certificate digest differs from the published identity",
        )
        .equation("§3.5"));
    }
    Ok(())
}

/// Reassemble Lean's `#print axioms` output, which wraps long axiom lists across
/// several lines. Parsing only the first line would let a `sorryAx` on a
/// continuation line escape the §3.4 policy gate.
fn collect_axiom_entries(stdout: &str) -> Vec<String> {
    let mut entries = Vec::new();
    let mut current: Option<String> = None;
    for line in stdout.lines() {
        match current.as_mut() {
            Some(buffer) => {
                buffer.push(' ');
                buffer.push_str(line.trim());
                if line.contains(']') {
                    entries.push(buffer.clone());
                    current = None;
                }
            }
            None => {
                if line.contains("depends on axioms:") {
                    if line.contains(']') {
                        entries.push(line.trim().to_owned());
                    } else {
                        current = Some(line.trim().to_owned());
                    }
                }
            }
        }
    }
    // An unterminated entry is retained so the policy check sees it rather than
    // silently dropping an axiom list.
    if let Some(buffer) = current {
        entries.push(buffer);
    }
    entries
}

/// Validate the captured axiom set against the profile policy (§3.4).
fn check_axiom_policy(axioms: &[String], profile: Profile, track_a: bool) -> CoreResult<()> {
    let standard = Profile::standard_axioms();
    // §3.4 permits "exactly one certificate-specific native-evaluation axiom".
    // That is one *distinct* axiom, not one occurrence: the closed-evaluation
    // theorem and the result theorem derived from it both list the same axiom.
    let mut native_axioms: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for line in axioms {
        let Some((_, listed)) = line.split_once("depends on axioms:") else {
            continue;
        };
        let listed = listed.trim().trim_start_matches('[').trim_end_matches(']');
        for name in listed.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            if name == "sorryAx" {
                return Err(CoreError::new(
                    ErrorCode::ImplementationDisagreement,
                    "the generated theorem depends on sorryAx",
                )
                .equation("§3.4"));
            }
            if standard.contains(&name) {
                continue;
            }
            if name.contains("native_decide") {
                native_axioms.insert(name.to_owned());
                continue;
            }
            // §3.2 permits exactly one project axiom, and only a Track A
            // theorem may depend on it. A Track B theorem that named it would
            // be a release failure, so the allowance is not global.
            // `#print axioms` prints the shortest unambiguous name, so an
            // `open MatrixMath` in the generated module abbreviates it.
            if track_a
                && (name == "MatrixMath.AX1_combination_loss" || name == "AX1_combination_loss")
            {
                continue;
            }
            return Err(CoreError::new(
                ErrorCode::ImplementationDisagreement,
                "the generated theorem depends on an undeclared project axiom",
            )
            .equation("§3.4")
            .value(name));
        }
    }
    match profile {
        Profile::Ck if !native_axioms.is_empty() => Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "profile CK forbids a native-evaluation axiom",
        )
        .equation("§3.4")
        .value(native_axioms.into_iter().collect::<Vec<_>>().join(", "))),
        Profile::Cn if native_axioms.len() > 1 => Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "profile CN permits exactly one distinct certificate-specific \
             native-evaluation axiom",
        )
        .equation("§3.4")
        .value(native_axioms.into_iter().collect::<Vec<_>>().join(", "))),
        _ => Ok(()),
    }
}

/// Generate, write, and check the certificate-specific module.
///
/// # Errors
///
/// Propagates generation, round-trip, Lean, and axiom-policy failures.
pub fn build_and_check(
    certificate: &DecompositionCertificate,
    published: impl std::io::Read,
    profile: Profile,
) -> CoreResult<ProofOutcome> {
    require_round_trip(certificate, published)?;

    let root = repo_root()?;
    let digest = certificate.digest_hex();
    let module: GeneratedModule = generate(&certificate.decomposition, &digest, profile)?;

    let generated_dir = root.join("lean").join("MatrixMath").join("Generated");
    fs::create_dir_all(&generated_dir)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create Generated: {error}")))?;
    let file_name = module
        .module_name
        .rsplit('.')
        .next()
        .unwrap_or("Cert")
        .to_owned();
    let module_path = generated_dir.join(format!("{file_name}.lean"));
    fs::write(&module_path, &module.source)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write module: {error}")))?;

    let (axioms, _) = run_lean(&root, &module_path)?;
    check_axiom_policy(&axioms, profile, false)?;

    let mut tcb = TcbLedger::from_environment(profile.as_str())?;
    tcb.record("certificate_sha256", digest);
    tcb.record("generated_module", module.module_name.clone());
    tcb.record("literal_count", module.literal_count.to_string());
    tcb.record("literal_shards", module.shard_count.to_string());
    if profile == Profile::Cn {
        tcb.record(
            "native_evaluation",
            "Lean compiler, runtime, and native bigint are trusted under CN (§3.6)",
        );
    }

    Ok(ProofOutcome {
        module_path,
        module_name: module.module_name,
        cert_theorem: module.cert_theorem,
        result_theorem: module.result_theorem,
        claim: module.claim,
        profile,
        axioms,
        tcb,
        compiled_assurance: None,
    })
}

/// Enforce the §3.5 round trip for an omega certificate.
///
/// # Errors
///
/// Returns [`ErrorCode::ImplementationDisagreement`] when the round trip differs.
fn require_omega_round_trip(
    certificate: &mm_schema::OmegaCertificate,
    published_bytes: &[u8],
    digest_hex: &str,
) -> CoreResult<()> {
    let mut comparator = CompareWriter::new(published_bytes);
    let (digest, _) = mm_schema::encode_omega(&mut comparator, certificate)?;
    comparator.finish()?;
    if mm_core::hex::encode_hex(&digest) != digest_hex {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "the re-encoded omega certificate digest differs from the published identity",
        )
        .equation("§3.5"));
    }
    Ok(())
}

/// §3.5 round trip for a symmetric certificate.
///
/// # Errors
///
/// Returns [`ErrorCode::ImplementationDisagreement`] when the round trip differs.
fn require_sym_round_trip(
    certificate: &mm_schema::symmetric::SymmetricCertificate,
    published_bytes: &[u8],
    digest_hex: &str,
) -> CoreResult<()> {
    let mut comparator = CompareWriter::new(published_bytes);
    let (digest, _) = mm_schema::symmetric::encode_symmetric_omega(&mut comparator, certificate)?;
    comparator.finish()?;
    if mm_core::hex::encode_hex(&digest) != digest_hex {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "the re-encoded symmetric certificate digest differs from the published identity",
        )
        .equation("§3.5"));
    }
    Ok(())
}

/// Generate, write, and check the compact Track A module for a symmetric
/// certificate (`0017_spec.md` §4).
///
/// # Errors
///
/// Propagates generation, round-trip, Lean, and axiom-policy failures.
pub fn build_and_check_sym_omega(
    certificate: &mm_schema::symmetric::SymmetricCertificate,
    published_bytes: &[u8],
    digest_hex: &str,
    profile: Profile,
) -> CoreResult<ProofOutcome> {
    require_sym_round_trip(certificate, published_bytes, digest_hex)?;

    let root = repo_root()?;
    let module =
        crate::lean_omega::generate_symmetric(certificate, published_bytes, digest_hex, profile)?;

    let generated_dir = root.join("lean").join("MatrixMath").join("Generated");
    fs::create_dir_all(&generated_dir)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create Generated: {error}")))?;
    let file_name = module
        .module_name
        .rsplit('.')
        .next()
        .unwrap_or("SymOmega")
        .to_owned();
    let module_path = generated_dir.join(format!("{file_name}.lean"));
    fs::write(&module_path, &module.source)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write module: {error}")))?;

    let (axioms, compiled_assurance) =
        run_omega_lean(&root, &module_path, "MatrixMath.Certificate.SymBridge")?;
    check_axiom_policy(&axioms, profile, true)?;

    let mut tcb = TcbLedger::from_environment(profile.as_str())?;
    tcb.record("certificate_sha256", digest_hex.to_owned());
    tcb.record("certificate_encoding", "symmetric".to_owned());
    tcb.record("generated_module", module.module_name.clone());
    tcb.record("literal_count", module.literal_count.to_string());
    tcb.record("literal_shards", module.shard_count.to_string());
    if profile == Profile::Cn {
        tcb.record(
            "native_evaluation",
            "Lean compiler, runtime, and native bigint are trusted under CN (§3.6)",
        );
    }
    Ok(ProofOutcome {
        module_path,
        module_name: module.module_name,
        cert_theorem: module.cert_theorem,
        result_theorem: module.result_theorem,
        claim: module.claim,
        profile,
        axioms,
        tcb,
        compiled_assurance: Some(compiled_assurance),
    })
}

/// Generate, write, and check the Track A module for an omega certificate.
///
/// # Errors
///
/// Propagates generation, round-trip, Lean, and axiom-policy failures.
pub fn build_and_check_omega(
    certificate: &mm_schema::OmegaCertificate,
    published_bytes: &[u8],
    digest_hex: &str,
    profile: Profile,
) -> CoreResult<ProofOutcome> {
    // The generated module carries the published bytes and Lean decodes them
    // itself, so re-encoding here is not what binds the theorem to the artifact.
    // It is still required: §3.5 makes the round trip a provenance check, and it
    // is what catches a decoder and an encoder that disagree.
    require_omega_round_trip(certificate, published_bytes, digest_hex)?;

    let root = repo_root()?;
    let module = crate::lean_omega::generate(certificate, published_bytes, digest_hex, profile)?;

    let generated_dir = root.join("lean").join("MatrixMath").join("Generated");
    fs::create_dir_all(&generated_dir)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create Generated: {error}")))?;
    let file_name = module
        .module_name
        .rsplit('.')
        .next()
        .unwrap_or("Omega")
        .to_owned();
    let module_path = generated_dir.join(format!("{file_name}.lean"));
    fs::write(&module_path, &module.source)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write module: {error}")))?;

    let (axioms, compiled_assurance) =
        run_omega_lean(&root, &module_path, "MatrixMath.Schema.Omega")?;
    check_axiom_policy(&axioms, profile, true)?;

    let mut tcb = TcbLedger::from_environment(profile.as_str())?;
    tcb.record("certificate_sha256", digest_hex.to_owned());
    tcb.record("generated_module", module.module_name.clone());
    tcb.record("literal_count", module.literal_count.to_string());
    tcb.record("literal_shards", module.shard_count.to_string());
    tcb.record(
        "project_axiom",
        "AX1_combination_loss: feasibility of the cited S1 problem implies a bound \
         on omega. Version 1 does not prove it (§3.2, §1.4).",
    );
    if profile == Profile::Cn {
        tcb.record(
            "native_evaluation",
            "Lean compiler, runtime, and native bigint are trusted under CN (§3.6)",
        );
    }

    Ok(ProofOutcome {
        module_path,
        module_name: module.module_name,
        cert_theorem: module.cert_theorem,
        result_theorem: module.result_theorem,
        claim: module.claim,
        profile,
        axioms,
        tcb,
        compiled_assurance: Some(compiled_assurance),
    })
}

fn file_digest(path: &Path) -> CoreResult<[u8; 32]> {
    let mut file = fs::File::open(path)
        .map_err(|e| CoreError::new(ErrorCode::Io, format!("open {}: {e}", path.display())))?;
    let mut hash = mm_core::Sha256::new();
    let mut buffer = [0u8; 65536];
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|e| CoreError::new(ErrorCode::Io, format!("read {}: {e}", path.display())))?;
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
    }
    Ok(hash.finalize())
}

fn lean_source_closure(root: &Path) -> CoreResult<String> {
    fn visit(directory: &Path, files: &mut Vec<PathBuf>) -> CoreResult<()> {
        for entry in fs::read_dir(directory)
            .map_err(|e| CoreError::new(ErrorCode::Io, format!("read source directory: {e}")))?
        {
            let entry =
                entry.map_err(|e| CoreError::new(ErrorCode::Io, format!("source entry: {e}")))?;
            if entry.file_name() == "Generated" {
                continue;
            }
            let path = entry.path();
            let kind = entry
                .file_type()
                .map_err(|e| CoreError::new(ErrorCode::Io, format!("source type: {e}")))?;
            if kind.is_symlink() {
                return Err(CoreError::new(
                    ErrorCode::Io,
                    "Lean source closure contains a symlink",
                )
                .value(path.display().to_string()));
            }
            if kind.is_dir() {
                visit(&path, files)?;
            } else if kind.is_file() && path.extension().is_some_and(|ext| ext == "lean") {
                files.push(path);
            }
        }
        Ok(())
    }
    let mut files = Vec::new();
    visit(&root.join("lean/MatrixMath"), &mut files)?;
    files.sort();
    let mut hash = mm_core::Sha256::new();
    for path in files {
        let relative = path
            .strip_prefix(root)
            .map_err(|e| CoreError::new(ErrorCode::Io, format!("source path: {e}")))?;
        let text = relative
            .to_str()
            .ok_or_else(|| CoreError::new(ErrorCode::Io, "Lean source path is not UTF-8"))?;
        hash.update(text.as_bytes());
        hash.update(&[0]);
        hash.update(&file_digest(&path)?);
    }
    Ok(hash.finalize_hex())
}

fn compiled_audit(stdout: &str) -> CoreResult<String> {
    let mut records = stdout
        .lines()
        .filter_map(|line| line.strip_prefix("MATRIX_MATH_RESULT_AUDIT "));
    let record = records.next().ok_or_else(|| {
        CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "Lean emitted no compiled result assurance",
        )
    })?;
    if records.next().is_some()
        || !record.starts_with("{\"declarations\":[")
        || !record.ends_with("\"schema\":\"matrix-math-compiled-result-assurance/1\"}")
    {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "Lean emitted duplicate or malformed compiled result assurance",
        ));
    }
    Ok(record.to_owned())
}

fn run_omega_lean(
    root: &Path,
    module_path: &Path,
    dependency: &str,
) -> CoreResult<(Vec<String>, CompiledAssurance)> {
    // Refresh the actual import closure. Current source hashes alone cannot
    // establish that previously built oleans came from those sources (§4.6).
    let source_before = lean_source_closure(root)?;
    let module_before = file_digest(module_path)?;
    let build = std::process::Command::new("lake")
        .current_dir(root.join("lean"))
        .args(["build", dependency, "MatrixMath.ResultAssurance"])
        .output()
        .map_err(|e| CoreError::new(ErrorCode::Io, format!("build proof dependencies: {e}")))?;
    if !build.status.success() {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "Lean proof dependencies failed to build",
        )
        .value(String::from_utf8_lossy(&build.stdout).into_owned())
        .value(String::from_utf8_lossy(&build.stderr).into_owned()));
    }
    let (axioms, stdout) = run_lean(root, module_path)?;
    let json = compiled_audit(&stdout)?;
    if lean_source_closure(root)? != source_before || file_digest(module_path)? != module_before {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "Lean sources or generated module changed during proof",
        ));
    }
    Ok((
        axioms,
        CompiledAssurance {
            json,
            lean_source_closure: source_before,
            generated_module_sha256: mm_core::hex::encode_hex(&module_before),
        },
    ))
}

fn run_lean(root: &Path, module_path: &Path) -> CoreResult<(Vec<String>, String)> {
    let output = std::process::Command::new("lake")
        .current_dir(root.join("lean"))
        .arg("env")
        .arg("lean")
        .arg(module_path)
        .output()
        .map_err(|error| {
            CoreError::new(
                ErrorCode::Io,
                format!("lake env lean could not start: {error}"),
            )
        })?;
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    if !output.status.success() {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "Lean rejected the generated certificate module",
        )
        .equation("§3.5")
        .value(stdout)
        .value(stderr));
    }
    let axioms = collect_axiom_entries(&stdout);
    if axioms.is_empty() {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "Lean produced no #print axioms output for the generated theorems",
        )
        .equation("§3.5")
        .value(stdout));
    }
    Ok((axioms, stdout))
}

/// Attempt the Lean check against the certificate's published bytes.
///
/// Used by `mm verify`, where a missing Lean toolchain downgrades the report to
/// `XC` rather than failing the run.
///
/// # Errors
///
/// Propagates every failure; callers decide whether to downgrade.
pub fn try_lean_check(
    certificate: &DecompositionCertificate,
    published: impl std::io::Read,
    profile: Profile,
) -> CoreResult<ProofOutcome> {
    build_and_check(certificate, published, profile)
}

/// Run `mm prove`.
///
/// # Errors
///
/// Returns the first structured rejection (§5.4).
pub fn run(arguments: &[String]) -> CoreResult<u8> {
    let mut path: Option<PathBuf> = None;
    let mut profile = Profile::Cn;
    let mut json = false;
    let mut index = 0usize;
    while let Some(argument) = arguments.get(index) {
        match argument.as_str() {
            "--json" => json = true,
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
    let path = path.ok_or_else(|| CoreError::new(ErrorCode::BadConfig, "mm prove needs a path"))?;

    // §6.1 dispatches on the declared kind before choosing a decoder.
    let probe = crate::verify::open_published(&path, mm_schema::Limits::default())?;
    if crate::verify::certificate_kind(&probe)? == "omega" {
        return prove_omega(&probe, profile, json);
    }

    let (certificate, published) = crate::verify::load(&path)?;
    certificate.decomposition.verify()?;
    let outcome = build_and_check(&certificate, published.reader()?, profile)?;

    // §3.5 requires the result-local assurance record and TCB ledger on disk.
    let root = repo_root()?;
    let reports = root
        .join("docs")
        .join("results")
        .join(certificate.digest_hex());
    fs::create_dir_all(&reports)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create report dir: {error}")))?;
    fs::write(reports.join("tcb.json"), outcome.tcb.to_canonical_json())
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write tcb.json: {error}")))?;
    fs::write(
        reports.join("assurance.json"),
        assurance_json(&outcome, &certificate),
    )
    .map_err(|error| CoreError::new(ErrorCode::Io, format!("write assurance.json: {error}")))?;

    if json {
        println!("{}", assurance_json(&outcome, &certificate));
    } else {
        println!("matrix-math prove");
        println!("  canonical sha256    {}", certificate.digest_hex());
        println!("  generated module    {}", outcome.module_path.display());
        println!("  theorem             {}", outcome.result_theorem);
        println!("  claim               {}", outcome.claim);
        println!("  certification       {}", outcome.profile.description());
        for line in &outcome.axioms {
            println!("  #print axioms       {line}");
        }
        println!(
            "  TCB ledger          {}",
            reports.join("tcb.json").display()
        );
        println!(
            "  assurance record    {}",
            reports.join("assurance.json").display()
        );
        println!();
        println!("PROVED");
    }
    Ok(0)
}

/// Run `mm prove` for an omega certificate (Track A).
fn prove_omega(
    published: &crate::verify::PublishedBytes,
    profile: Profile,
    json: bool,
) -> CoreResult<u8> {
    if crate::verify::declares_symmetric(published)? {
        return prove_omega_symmetric(published, profile, json);
    }
    let (certificate, digest_hex) = crate::verify::decode_published_omega(published)?;
    // The independent Rust evaluator runs first, so a disagreement is reported
    // as a disagreement rather than as a Lean failure (§4.3).
    let evaluable = mm_exact::from_certificate(&certificate)?;
    mm_exact::evaluate::evaluate(
        &evaluable.tree,
        &evaluable.blocks,
        &certificate.omega,
        evaluable.precision,
    )?;

    let bytes = published.to_vec()?;
    let outcome = build_and_check_omega(&certificate, &bytes, &digest_hex, profile)?;

    let root = repo_root()?;
    let reports = root.join("docs").join("results").join(&digest_hex);
    fs::create_dir_all(&reports)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create report dir: {error}")))?;
    fs::write(reports.join("tcb.json"), outcome.tcb.to_canonical_json())
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write tcb.json: {error}")))?;
    let record = omega_assurance_json(&outcome, &digest_hex)?;
    write_compiled_assurance(&outcome, &reports)?;
    fs::write(reports.join("assurance.json"), &record)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write assurance.json: {error}")))?;

    if json {
        println!("{record}");
    } else {
        println!("matrix-math prove");
        println!("  kind                omega");
        println!("  canonical sha256    {digest_hex}");
        println!("  generated module    {}", outcome.module_path.display());
        println!("  theorem             {}", outcome.result_theorem);
        println!("  claim               {}", outcome.claim);
        println!("  certification       {}", outcome.profile.description());
        for line in &outcome.axioms {
            println!("  #print axioms       {line}");
        }
        println!();
        println!(
            "  AX1_combination_loss is the one project axiom §3.2 permits. This is an \
             upper bound on omega and nothing stronger."
        );
    }
    Ok(0)
}

/// Run `mm prove` for a symmetric omega certificate (`0017_spec.md` §4).
fn prove_omega_symmetric(
    published: &crate::verify::PublishedBytes,
    profile: Profile,
    json: bool,
) -> CoreResult<u8> {
    let (certificate, digest_hex) = crate::verify::decode_published_symmetric(published)?;
    // The independent Rust group evaluator runs first, so a disagreement is
    // reported as a disagreement rather than as a Lean failure (§4.3).
    let precision = mm_rat::log2::Precision::new(certificate.log_precision_bits)?;
    let bounds = mm_exact::symmetric::group_evaluate_bounds(&certificate, precision)?;
    match bounds.minimal_omega() {
        Some(minimal) if minimal <= certificate.omega => {}
        _ => {
            return Err(CoreError::new(
                ErrorCode::FeasibilityViolated,
                "the group evaluation does not accept the claimed omega",
            )
            .equation("A21"));
        }
    }

    let bytes = published.to_vec()?;
    let outcome = build_and_check_sym_omega(&certificate, &bytes, &digest_hex, profile)?;

    let root = repo_root()?;
    let reports = root.join("docs").join("results").join(&digest_hex);
    fs::create_dir_all(&reports)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create report dir: {error}")))?;
    fs::write(reports.join("tcb.json"), outcome.tcb.to_canonical_json())
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write tcb.json: {error}")))?;
    let record = omega_assurance_json(&outcome, &digest_hex)?;
    write_compiled_assurance(&outcome, &reports)?;
    fs::write(reports.join("assurance.json"), &record)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write assurance.json: {error}")))?;

    if json {
        println!("{record}");
    } else {
        println!("matrix-math prove");
        println!("  kind                omega (symmetric encoding)");
        println!("  canonical sha256    {digest_hex}");
        println!("  generated module    {}", outcome.module_path.display());
        println!("  theorem             {}", outcome.result_theorem);
        println!("  claim               {}", outcome.claim);
        println!("  certification       {}", outcome.profile.description());
        for line in &outcome.axioms {
            println!("  #print axioms       {line}");
        }
        println!();
        println!(
            "  AX1_combination_loss is the one project axiom §3.2 permits. This is an \
             upper bound on omega and nothing stronger."
        );
    }
    Ok(0)
}

pub(crate) fn write_compiled_assurance(outcome: &ProofOutcome, reports: &Path) -> CoreResult<()> {
    let audit = outcome.compiled_assurance.as_ref().ok_or_else(|| {
        CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "omega proof lacks compiled assurance",
        )
    })?;
    fs::write(reports.join("compiled-assurance.json"), &audit.json)
        .map_err(|e| CoreError::new(ErrorCode::Io, format!("write compiled assurance: {e}")))
}

pub(crate) fn omega_assurance_json(outcome: &ProofOutcome, digest_hex: &str) -> CoreResult<String> {
    let audit = outcome.compiled_assurance.as_ref().ok_or_else(|| {
        CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "omega proof lacks compiled assurance",
        )
    })?;
    let mut out = String::from("{\"axioms\":[");
    for (index, line) in outcome.axioms.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        push_json_string(&mut out, line);
    }
    out.push_str("],\"certificate_sha256\":");
    push_json_string(&mut out, digest_hex);
    out.push_str(",\"claim\":");
    push_json_string(&mut out, &outcome.claim);
    out.push_str(",\"compiled_assurance\":");
    out.push_str(&audit.json);
    out.push_str(",\"declaration\":");
    push_json_string(
        &mut out,
        &format!("MatrixMath.Generated.{}", outcome.result_theorem),
    );
    out.push_str(",\"evaluation_declaration\":");
    push_json_string(
        &mut out,
        &format!("MatrixMath.Generated.{}", outcome.cert_theorem),
    );
    out.push_str(",\"evidence\":{\"certificate_sha256\":");
    push_json_string(&mut out, digest_hex);
    out.push_str(",\"compiled_assurance_sha256\":");
    push_json_string(
        &mut out,
        &mm_core::hex::encode_hex(&mm_core::sha256(audit.json.as_bytes())),
    );
    out.push_str(",\"generated_module_sha256\":");
    push_json_string(&mut out, &audit.generated_module_sha256);
    out.push_str("},\"lean_source_closure\":");
    push_json_string(&mut out, &audit.lean_source_closure);
    out.push_str(",\"module\":");
    push_json_string(&mut out, &outcome.module_name);
    out.push_str(",\"profile\":");
    push_json_string(&mut out, outcome.profile.as_str());
    out.push_str(
        ",\"project_axioms\":[\"MatrixMath.AX1_combination_loss\"],\"residual_assumptions\":[],",
    );
    out.push_str("\"schema\":\"matrix-math-assurance-record/1\",\"spec_version\":");
    push_json_string(&mut out, mm_core::SPEC_VERSION);
    out.push_str(",\"status\":\"active\"}");
    Ok(out)
}

fn assurance_json(outcome: &ProofOutcome, certificate: &DecompositionCertificate) -> String {
    let mut out = String::from("{\"axioms\":[");
    for (index, line) in outcome.axioms.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        push_json_string(&mut out, line);
    }
    out.push_str("],\"certificate_sha256\":");
    push_json_string(&mut out, &certificate.digest_hex());
    out.push_str(",\"claim\":");
    push_json_string(&mut out, &outcome.claim);
    out.push_str(",\"declaration\":");
    push_json_string(&mut out, &outcome.result_theorem);
    out.push_str(",\"evaluation_declaration\":");
    push_json_string(&mut out, &outcome.cert_theorem);
    out.push_str(",\"module\":");
    push_json_string(&mut out, &outcome.module_name);
    out.push_str(",\"profile\":");
    push_json_string(&mut out, outcome.profile.as_str());
    out.push_str(",\"residual_assumptions\":[],\"schema\":\"matrix-math-assurance-record/1\",\"spec_version\":");
    push_json_string(&mut out, mm_core::SPEC_VERSION);
    out.push_str(",\"status\":\"active\"}");
    out
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::expect_used,
        clippy::panic,
        clippy::unwrap_used,
        reason = "test assertions must fail loudly; §17.1 governs library code"
    )]

    use super::{
        CompiledAssurance, ProofOutcome, check_axiom_policy, collect_axiom_entries, compiled_audit,
        lean_source_closure, omega_assurance_json,
    };
    use crate::lean::Profile;

    #[test]
    fn compiled_audit_requires_one_complete_marker() {
        let record = "{\"declarations\":[],\"schema\":\"matrix-math-compiled-result-assurance/1\"}";
        let line = format!("MATRIX_MATH_RESULT_AUDIT {record}\n");
        assert_eq!(
            compiled_audit(&format!("ordinary Lean output\n{line}")).unwrap(),
            record
        );
        for text in [
            String::new(),
            format!("{line}{line}"),
            "MATRIX_MATH_RESULT_AUDIT {}\n".to_owned(),
            format!("MATRIX_MATH_RESULT_AUDIT {record} trailing"),
        ] {
            assert!(compiled_audit(&text).is_err(), "{text}");
        }
    }

    #[test]
    fn source_closure_hashes_sorted_paths_and_raw_digests() {
        let root =
            std::env::temp_dir().join(format!("mm-source-closure-test-{}", std::process::id()));
        let directory = root.join("lean/MatrixMath");
        std::fs::create_dir_all(directory.join("Generated")).unwrap();
        std::fs::write(directory.join("Z.lean"), "def z := 2\n").unwrap();
        std::fs::write(directory.join("A.lean"), "def a := 1\n").unwrap();
        std::fs::write(directory.join("ignored.txt"), "not Lean").unwrap();
        std::fs::write(directory.join("Generated/Cert.lean"), "generated").unwrap();
        let mut expected = mm_core::Sha256::new();
        for (path, contents) in [
            ("lean/MatrixMath/A.lean", "def a := 1\n"),
            ("lean/MatrixMath/Z.lean", "def z := 2\n"),
        ] {
            expected.update(path.as_bytes());
            expected.update(&[0]);
            expected.update(&mm_core::sha256(contents.as_bytes()));
        }
        assert_eq!(lean_source_closure(&root).unwrap(), expected.finalize_hex());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn omega_record_requires_compiled_evidence_and_binds_its_exact_bytes() {
        let mut outcome = ProofOutcome {
            module_path: "unused".into(),
            module_name: "MatrixMath.Generated.Omega_ab".into(),
            cert_theorem: "omegaCert_ab".into(),
            result_theorem: "omegaResult_ab".into(),
            claim: "omega <= 3".into(),
            profile: Profile::Cn,
            axioms: vec![],
            tcb: mm_registry::TcbLedger::new(),
            compiled_assurance: None,
        };
        assert!(omega_assurance_json(&outcome, "ab").is_err());
        let json = "{\"compiled\":true}";
        outcome.compiled_assurance = Some(CompiledAssurance {
            json: json.into(),
            lean_source_closure: "closure".into(),
            generated_module_sha256: "module".into(),
        });
        let record = omega_assurance_json(&outcome, "ab").unwrap();
        assert!(
            record.contains("\"evaluation_declaration\":\"MatrixMath.Generated.omegaCert_ab\"")
        );
        assert!(record.contains("\"declaration\":\"MatrixMath.Generated.omegaResult_ab\""));
        assert!(record.contains(&mm_core::hex::encode_hex(&mm_core::sha256(json.as_bytes()))));
        assert!(record.contains("\"lean_source_closure\":\"closure\""));
        assert!(record.contains("\"residual_assumptions\":[]"));
        assert!(record.contains("\"status\":\"active\""));
    }

    /// Lean wraps long axiom lists. Parsing only the first line would let a
    /// `sorryAx` on a continuation line escape the §3.4 policy gate.
    #[test]
    fn wrapped_axiom_lists_are_reassembled() {
        let stdout = "\
'MatrixMath.Generated.cert_ab' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MatrixMath.Generated.result_ab' depends on axioms: [propext, Quot.sound]
";
        let entries = collect_axiom_entries(stdout);
        assert_eq!(entries.len(), 2, "{entries:?}");
        assert!(entries[0].contains("Classical.choice"));
        assert!(entries[0].contains("Quot.sound"));
        check_axiom_policy(&entries, Profile::Ck, false).expect("standard axioms satisfy CK");
    }

    #[test]
    fn a_wrapped_sorry_is_still_rejected() {
        let stdout = "\
'MatrixMath.Generated.cert_ab' depends on axioms: [propext,
 sorryAx]
";
        let entries = collect_axiom_entries(stdout);
        let error =
            check_axiom_policy(&entries, Profile::Cn, false).expect_err("sorryAx must reject");
        assert!(error.message().contains("sorryAx"), "{error}");
    }

    /// The closed-evaluation theorem and the result theorem derived from it both
    /// list the same native axiom. §3.4 permits one *distinct* axiom, so two
    /// occurrences of one axiom must pass.
    #[test]
    fn cn_accepts_one_axiom_listed_by_two_theorems() {
        let stdout = "\
'X.cert' depends on axioms: [propext, Quot.sound, X.cert._native.native_decide.ax_1_1]
'X.result' depends on axioms: [propext, Quot.sound, X.cert._native.native_decide.ax_1_1]
";
        let entries = collect_axiom_entries(stdout);
        assert_eq!(entries.len(), 2);
        check_axiom_policy(&entries, Profile::Cn, false).expect("one distinct native axiom");
    }

    #[test]
    fn cn_rejects_two_distinct_native_axioms() {
        let stdout = "\
'X.cert' depends on axioms: [propext, X.cert._native.native_decide.ax_1_1]
'X.other' depends on axioms: [propext, X.other._native.native_decide.ax_2_1]
";
        let entries = collect_axiom_entries(stdout);
        assert!(check_axiom_policy(&entries, Profile::Cn, false).is_err());
    }

    #[test]
    fn ck_rejects_a_native_evaluation_axiom() {
        let stdout = "'X.cert' depends on axioms: [propext, Quot.sound, X.cert._native.native_decide.ax_1_1]\n";
        let entries = collect_axiom_entries(stdout);
        assert!(check_axiom_policy(&entries, Profile::Ck, false).is_err());
        check_axiom_policy(&entries, Profile::Cn, false).expect("CN permits exactly one");
    }

    #[test]
    fn an_undeclared_project_axiom_is_rejected_under_both_profiles() {
        let stdout = "'X.cert' depends on axioms: [propext, MatrixMath.myShortcut]\n";
        let entries = collect_axiom_entries(stdout);
        for profile in [Profile::Ck, Profile::Cn] {
            let error = check_axiom_policy(&entries, profile, false).expect_err("undeclared axiom");
            assert!(error.message().contains("undeclared"), "{error}");
        }
    }
}
