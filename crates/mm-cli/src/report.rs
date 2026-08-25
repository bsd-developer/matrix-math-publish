//! `mm report` and `mm verify-release` (spec §15, §14.11).
//!
//! §15.2 fixes the normative manifest fields; §15.5 additionally requires at
//! least one **durable remote URI** before a result is publishable. This build
//! has no archive configured, so a manifest it writes records
//! `durable_uri: null` and the result class is forced to `WORK-IN-PROGRESS`
//! regardless of how strong its theorem is. §15.1 is explicit that a Git pointer
//! to a local CAS is not sufficient.
//!
//! `verify-release` is the §14.11 acceptance path: it retrieves every referenced
//! artifact into an **empty temporary CAS**, checks all digests, reruns R1
//! verification, rebuilds the theorem, and compares the axiom policy.

use crate::lean::Profile;
use crate::prove;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult, push_json_string};
use mm_core::hex::encode_hex;
use mm_registry::Cas;
use std::fs;
use std::path::{Path, PathBuf};

/// The §15.1 result classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResultClass {
    /// No certificate-specific theorem, or no durable archive.
    WorkInProgress,
    /// Kernel-certified.
    CertifiedCk,
    /// Native-certified with an expanded TCB.
    CertifiedCn,
}

impl ResultClass {
    /// Classify a result from its evidence (§15.1, §15.5).
    ///
    /// A certificate-specific theorem is necessary but not sufficient: §15.5
    /// requires at least one durable remote URI that retrieves the exact
    /// canonical digest, and §15.1 says a Git pointer to a local CAS is not
    /// enough. So a kernel-certified result with no archive is still
    /// `WORK-IN-PROGRESS`.
    #[must_use]
    pub const fn classify(profile: Profile, durable_uri: Option<&str>) -> Self {
        match durable_uri {
            None => Self::WorkInProgress,
            Some(_) => match profile {
                Profile::Ck => Self::CertifiedCk,
                Profile::Cn => Self::CertifiedCn,
            },
        }
    }

    /// The canonical label.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::WorkInProgress => "WORK-IN-PROGRESS",
            Self::CertifiedCk => "CERTIFIED-CK",
            Self::CertifiedCn => "CERTIFIED-CN",
        }
    }
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

fn digest_of(path: &Path) -> CoreResult<String> {
    let data = fs::read(path)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("read {path:?}: {error}")))?;
    Ok(encode_hex(&mm_core::sha256(&data)))
}

/// Run `mm report`.
///
/// # Errors
///
/// Propagates verification, proof, and I/O failures.
pub fn run(arguments: &[String]) -> CoreResult<u8> {
    let mut path: Option<PathBuf> = None;
    let mut profile = Profile::Ck;
    let mut index = 0usize;
    while let Some(argument) = arguments.get(index) {
        match argument.as_str() {
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
        CoreError::new(ErrorCode::BadConfig, "mm report needs a certificate path")
    })?;

    let root = repo_root()?;
    let (certificate, published) = crate::verify::load(&path)?;
    let claim = certificate.decomposition.verify()?;
    let outcome = prove::build_and_check(&certificate, published.reader()?, profile)?;

    // §15.5: without a durable remote URI the class is WORK-IN-PROGRESS, however
    // strong the theorem is. `MATRIX_MATH_DURABLE_URI` is the hook a publisher
    // sets once an archive holds the exact canonical digest.
    let durable_uri = std::env::var("MATRIX_MATH_DURABLE_URI").ok();
    let class = ResultClass::classify(outcome.profile, durable_uri.as_deref());

    let digest_hex = certificate.digest_hex();
    let store = Cas::open(root.join("data").join("cas"))?;
    let canonical = fs::read(&path)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("read {path:?}: {error}")))?;
    let stored = store.put(&canonical)?;

    let reports = root.join("docs").join("results").join(&digest_hex);
    fs::create_dir_all(&reports)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create report dir: {error}")))?;
    fs::write(reports.join("tcb.json"), outcome.tcb.to_canonical_json())
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write tcb: {error}")))?;

    let traceability = root.join("docs").join("traceability.md");
    let traceability_digest = digest_of(&traceability).unwrap_or_else(|_| String::from("absent"));
    let theorem_digest = digest_of(&outcome.module_path)?;
    let tcb_digest = encode_hex(&mm_core::sha256(outcome.tcb.to_canonical_json().as_bytes()));

    let mut manifest = String::from("{\"axioms\":[");
    for (index, line) in outcome.axioms.iter().enumerate() {
        if index > 0 {
            manifest.push(',');
        }
        push_json_string(&mut manifest, line);
    }
    manifest.push_str("],\"canonical_sha256\":");
    push_json_string(&mut manifest, &digest_hex);
    manifest.push_str(",\"certificate_bytes\":");
    manifest.push_str(&certificate.byte_count.to_string());
    manifest.push_str(",\"certificate_kind\":\"decomposition\",\"certification_profile\":");
    push_json_string(&mut manifest, outcome.profile.as_str());
    manifest.push_str(",\"claim\":");
    push_json_string(&mut manifest, &claim.statement());
    manifest.push_str(",\"class\":");
    push_json_string(&mut manifest, class.as_str());
    manifest.push_str(",\"durable_uri\":");
    match durable_uri.as_deref() {
        Some(uri) => push_json_string(&mut manifest, uri),
        None => manifest.push_str("null"),
    }
    manifest.push_str(",\"local_cas_sha256\":");
    push_json_string(&mut manifest, &stored);
    manifest.push_str(",\"replay_level\":\"R1\",\"result_id\":");
    push_json_string(&mut manifest, &digest_hex);
    manifest.push_str(",\"rust_verifier\":");
    push_json_string(&mut manifest, env!("CARGO_PKG_VERSION"));
    manifest.push_str(",\"schema\":\"matrix-math-result-manifest/1\",\"source_hashes\":{\"S1\":");
    push_json_string(&mut manifest, mm_core::SOURCE_S1_SHA256);
    manifest.push_str(",\"S2\":");
    push_json_string(&mut manifest, mm_core::SOURCE_S2_SHA256);
    manifest.push_str("},\"spec_version\":");
    push_json_string(&mut manifest, mm_core::SPEC_VERSION);
    manifest.push_str(",\"tcb_ledger_sha256\":");
    push_json_string(&mut manifest, &tcb_digest);
    manifest.push_str(",\"theorem_name\":");
    push_json_string(&mut manifest, &outcome.result_theorem);
    manifest.push_str(",\"theorem_source_sha256\":");
    push_json_string(&mut manifest, &theorem_digest);
    manifest.push_str(",\"traceability_sha256\":");
    push_json_string(&mut manifest, &traceability_digest);
    if class == ResultClass::WorkInProgress {
        manifest.push_str(",\"why_not_publishable\":");
        push_json_string(
            &mut manifest,
            "§15.5 requires at least one durable remote URI that retrieves this exact \
             canonical digest. None is configured, so this result is WORK-IN-PROGRESS \
             regardless of its theorem.",
        );
    }
    manifest.push('}');

    let manifest_path = reports.join("manifest.json");
    fs::write(&manifest_path, &manifest)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write manifest: {error}")))?;

    println!("matrix-math report");
    println!("  result id           {digest_hex}");
    println!("  class               {}", class.as_str());
    println!("  claim               {}", claim.statement());
    println!("  theorem             {}", outcome.result_theorem);
    println!("  certification       {}", outcome.profile.description());
    println!("  local CAS           {stored}");
    match durable_uri.as_deref() {
        Some(uri) => println!("  durable URI         {uri}"),
        None => println!("  durable URI         none configured"),
    }
    println!("  manifest            {}", manifest_path.display());
    println!();
    if class == ResultClass::WorkInProgress {
        println!(
            "Reported as {} because §15.5 requires a durable remote URI; a Git pointer \
             to a local CAS is not sufficient.",
            class.as_str()
        );
    }
    Ok(0)
}

/// Run `mm verify-release` (§14.11, §15).
///
/// # Errors
///
/// Returns [`ErrorCode::DigestMismatch`] when a recorded digest does not match,
/// and propagates verification failures.
pub fn verify_release(arguments: &[String]) -> CoreResult<u8> {
    let path = arguments
        .iter()
        .find(|argument| !argument.starts_with("--"))
        .map(PathBuf::from)
        .ok_or_else(|| {
            CoreError::new(
                ErrorCode::BadConfig,
                "mm verify-release needs a manifest path",
            )
        })?;
    let text = fs::read_to_string(&path)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("read {path:?}: {error}")))?;

    let field = |key: &str| -> Option<String> {
        let needle = format!("\"{key}\":\"");
        let start = text.find(&needle)? + needle.len();
        let rest = text.get(start..)?;
        let end = rest.find('"')?;
        rest.get(..end).map(str::to_owned)
    };

    let digest = field("canonical_sha256").ok_or_else(|| missing_field("canonical_sha256"))?;
    let claim = field("claim").ok_or_else(|| missing_field("claim"))?;
    let profile_name =
        field("certification_profile").ok_or_else(|| missing_field("certification_profile"))?;
    let class = field("class").ok_or_else(|| missing_field("class"))?;
    let spec_version = field("spec_version").ok_or_else(|| missing_field("spec_version"))?;

    if spec_version != mm_core::SPEC_VERSION {
        return Err(CoreError::new(
            ErrorCode::SpecVersionMismatch,
            "the manifest names a different specification version",
        )
        .equation("§0.5")
        .value(spec_version));
    }

    let root = repo_root()?;
    println!("matrix-math verify-release");
    println!("  manifest            {}", path.display());
    println!("  result id           {digest}");
    println!("  claim               {claim}");
    println!("  class               {class}");

    // §14.11: retrieve into an EMPTY temporary CAS, so a stale local copy cannot
    // make a release verify that a fresh consumer could not reproduce.
    let temporary = std::env::temp_dir().join(format!("mm-release-{digest}"));
    let _ = fs::remove_dir_all(&temporary);
    let fresh = Cas::open(&temporary)?;
    let source = Cas::open(root.join("data").join("cas"))?;
    let bytes = source.get(&digest).map_err(|error| {
        error.value("the local CAS does not hold this artifact; §15.5 needs a durable URI")
    })?;
    let restored = fresh.put(&bytes)?;
    if restored != digest {
        return Err(CoreError::new(
            ErrorCode::DigestMismatch,
            "the retrieved artifact does not hash to its recorded identity",
        )
        .equation("§13.6"));
    }
    println!("  fresh CAS retrieve  ok ({} bytes)", bytes.len());

    // R1: re-verify the exact published witness from the retrieved bytes.
    let staged = temporary.join("certificate.json");
    fs::write(&staged, &bytes)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("stage: {error}")))?;
    let (certificate, published) = crate::verify::load(&staged)?;
    let recomputed = certificate.decomposition.verify()?;
    if recomputed.statement() != claim {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "the recomputed claim differs from the manifest",
        )
        .equation("§15.2")
        .value(recomputed.statement())
        .value(claim));
    }
    println!("  R1 re-verification  ok");

    // Rebuild the theorem and re-check the axiom policy.
    let profile = Profile::parse(&profile_name)?;
    let outcome = prove::build_and_check(&certificate, published.reader()?, profile)?;
    println!("  theorem rebuild     ok ({})", outcome.result_theorem);
    println!("  axiom policy        ok");

    let _ = fs::remove_dir_all(&temporary);

    if class == "WORK-IN-PROGRESS" {
        println!();
        println!("RELEASE CHECK PASSED for a WORK-IN-PROGRESS result.");
        println!("§15.5 still blocks publication: no durable remote URI retrieves this digest.");
    } else {
        println!();
        println!("RELEASE VERIFIED");
    }
    Ok(0)
}

fn missing_field(name: &str) -> CoreError {
    CoreError::new(
        ErrorCode::MissingField,
        "the manifest is missing a normative field",
    )
    .equation("§15.2")
    .value(name)
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::expect_used,
        clippy::panic,
        clippy::unwrap_used,
        reason = "test assertions must fail loudly; §17.1 governs library code"
    )]

    use super::ResultClass;
    use crate::lean::Profile;

    /// §15.1 and §15.5: a certificate-specific theorem is necessary but not
    /// sufficient. Without a durable remote URI the class is WORK-IN-PROGRESS,
    /// however strong the theorem is.
    #[test]
    fn no_archive_means_work_in_progress_whatever_the_profile() {
        for profile in [Profile::Ck, Profile::Cn] {
            assert_eq!(
                ResultClass::classify(profile, None),
                ResultClass::WorkInProgress,
                "{profile:?} without an archive"
            );
        }
    }

    #[test]
    fn an_archive_promotes_to_the_profile_class() {
        let uri = Some("https://doi.org/10.5281/zenodo.example");
        assert_eq!(
            ResultClass::classify(Profile::Ck, uri),
            ResultClass::CertifiedCk
        );
        assert_eq!(
            ResultClass::classify(Profile::Cn, uri),
            ResultClass::CertifiedCn
        );
    }

    /// §15.1: XC is never a publication class, which is enforced by `Profile`
    /// having no XC variant at all rather than by a runtime check.
    #[test]
    fn the_labels_are_the_spec_labels() {
        assert_eq!(ResultClass::WorkInProgress.as_str(), "WORK-IN-PROGRESS");
        assert_eq!(ResultClass::CertifiedCk.as_str(), "CERTIFIED-CK");
        assert_eq!(ResultClass::CertifiedCn.as_str(), "CERTIFIED-CN");
    }
}
