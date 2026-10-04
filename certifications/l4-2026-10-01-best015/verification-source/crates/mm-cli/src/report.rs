//! `mm report` and `mm verify-release` (spec §15, §14.11).
//!
//! Local proof reports support both certificate kinds and both omega encodings.
//! Local reports remain work in progress. Release verification delegates fresh
//! remote retrieval and independent Rust/Lean replay to repository-owned Python
//! orchestration. A configured URI is never proof or release acceptance.

use crate::cas::{CanonicalInput, Certificate};
use crate::lean::Profile;
use crate::prove;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult, push_json_string};
use mm_core::hex::encode_hex;
use mm_registry::Cas;
use std::fs;
use std::path::{Path, PathBuf};

const LOCAL_RESULT_CLASS: &str = "WORK-IN-PROGRESS";

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

struct CheckedClaim {
    statement: String,
    omega: Option<mm_exact::evaluate::OmegaClaim>,
}

fn check_claim(input: &CanonicalInput) -> CoreResult<CheckedClaim> {
    let omega = match &input.certificate {
        Certificate::Decomposition(certificate) => {
            return Ok(CheckedClaim {
                statement: certificate.decomposition.verify()?.statement(),
                omega: None,
            });
        }
        Certificate::Omega(certificate) => {
            let evaluable = mm_exact::from_certificate(certificate)?;
            mm_exact::evaluate::evaluate(
                &evaluable.tree,
                &evaluable.blocks,
                &certificate.omega,
                evaluable.precision,
            )?
        }
        Certificate::Symmetric(certificate) => {
            let precision = mm_rat::log2::Precision::new(certificate.log_precision_bits)?;
            let bounds = mm_exact::symmetric::group_evaluate_bounds(certificate, precision)?;
            match bounds.minimal_omega() {
                Some(minimum) if minimum <= certificate.omega => {}
                _ => {
                    return Err(CoreError::new(
                        ErrorCode::FeasibilityViolated,
                        "the group evaluation does not accept the claimed omega",
                    )
                    .equation("A21"));
                }
            }
            mm_exact::evaluate::OmegaClaim {
                e_total: bounds.e_total,
                m_total: bounds.m_total,
                requirement: bounds.requirement,
                omega: certificate.omega.clone(),
            }
        }
    };
    Ok(CheckedClaim {
        statement: omega.statement(),
        omega: Some(omega),
    })
}

fn build_proof(input: &CanonicalInput, profile: Profile) -> CoreResult<prove::ProofOutcome> {
    match &input.certificate {
        Certificate::Decomposition(certificate) => {
            prove::build_and_check(certificate, input.bytes.as_slice(), profile)
        }
        Certificate::Omega(certificate) => {
            prove::build_and_check_omega(certificate, &input.bytes, &input.digest, profile)
        }
        Certificate::Symmetric(certificate) => {
            prove::build_and_check_sym_omega(certificate, &input.bytes, &input.digest, profile)
        }
    }
}

fn require_matching_claim(claim: &CheckedClaim, outcome: &prove::ProofOutcome) -> CoreResult<()> {
    if claim.statement != outcome.claim {
        return Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "the Rust and Lean report claims differ",
        )
        .equation("§4.3"));
    }
    Ok(())
}

const PUBLICATION_BLOCKER: &str = "M8 incomplete: durable artifact retrieval and full normative \
    manifest validation are not implemented. A supplied URI has not been validated; this local \
    proof report is WORK-IN-PROGRESS and is not a verified release.";

fn quoted(value: &str) -> String {
    let mut output = String::new();
    push_json_string(&mut output, value);
    output
}

struct ReportDigests {
    theorem: String,
    tcb: String,
    traceability: String,
    assurance: Option<String>,
}

fn manifest_json(
    input: &CanonicalInput,
    claim: &CheckedClaim,
    outcome: &prove::ProofOutcome,
    digests: &ReportDigests,
    supplied_uri: Option<&str>,
) -> String {
    // A small local report, not a substitute for the full §15.2 release schema.
    let mut fields = std::collections::BTreeMap::<&str, String>::new();
    fields.insert(
        "axioms",
        format!(
            "[{}]",
            outcome
                .axioms
                .iter()
                .map(|line| quoted(line))
                .collect::<Vec<_>>()
                .join(",")
        ),
    );
    fields.insert("canonical_sha256", quoted(&input.digest));
    fields.insert("certificate_bytes", input.bytes.len().to_string());
    if let Some(encoding) = input.certificate.encoding() {
        fields.insert("certificate_encoding", quoted(encoding));
    }
    fields.insert("certificate_kind", quoted(input.certificate.kind()));
    fields.insert("certification_profile", quoted(outcome.profile.as_str()));
    fields.insert("claim", quoted(&claim.statement));
    fields.insert("class", quoted(LOCAL_RESULT_CLASS));
    fields.insert("durable_uri", "null".to_owned());
    fields.insert("local_cas_sha256", quoted(&input.digest));
    fields.insert("replay_level", quoted("R1"));
    fields.insert("result_id", quoted(&input.digest));
    fields.insert("rust_verifier", quoted(env!("CARGO_PKG_VERSION")));
    fields.insert("schema", quoted("matrix-math-result-manifest/1"));
    fields.insert(
        "source_hashes",
        format!(
            "{{\"S1\":{},\"S2\":{}}}",
            quoted(mm_core::SOURCE_S1_SHA256),
            quoted(mm_core::SOURCE_S2_SHA256)
        ),
    );
    fields.insert("spec_version", quoted(mm_core::SPEC_VERSION));
    fields.insert("tcb_ledger_sha256", quoted(&digests.tcb));
    fields.insert("theorem_name", quoted(&outcome.result_theorem));
    fields.insert("theorem_source_sha256", quoted(&digests.theorem));
    fields.insert("traceability_sha256", quoted(&digests.traceability));
    fields.insert("why_not_publishable", quoted(PUBLICATION_BLOCKER));
    if let Some(uri) = supplied_uri {
        fields.insert("unvalidated_durable_uri", quoted(uri));
    }
    if let Some(omega) = &claim.omega {
        fields.insert("omega", quoted(&omega.omega.to_string()));
        fields.insert("e_total_lower", quoted(&omega.e_total.value().to_string()));
        fields.insert("m_total_lower", quoted(&omega.m_total.value().to_string()));
        fields.insert(
            "requirement_upper",
            quoted(&omega.requirement.value().to_string()),
        );
    }
    if let Some(assurance) = &digests.assurance {
        fields.insert("assurance_sha256", quoted(assurance));
    }
    if let Some(audit) = &outcome.compiled_assurance {
        fields.insert(
            "compiled_assurance_sha256",
            quoted(&encode_hex(&mm_core::sha256(audit.json.as_bytes()))),
        );
        fields.insert("lean_source_closure", quoted(&audit.lean_source_closure));
    }
    format!(
        "{{{}}}",
        fields
            .into_iter()
            .map(|(key, value)| format!("{}:{value}", quoted(key)))
            .collect::<Vec<_>>()
            .join(",")
    )
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
            other => {
                if path.is_some() {
                    return Err(CoreError::new(
                        ErrorCode::BadConfig,
                        "mm report accepts one certificate path",
                    ));
                }
                path = Some(PathBuf::from(other));
            }
        }
        index += 1;
    }
    let path = path.ok_or_else(|| {
        CoreError::new(ErrorCode::BadConfig, "mm report needs a certificate path")
    })?;

    let root = repo_root()?;
    let input = crate::cas::load_canonical(&path)?;
    let claim = check_claim(&input)?;
    let outcome = build_proof(&input, profile)?;
    require_matching_claim(&claim, &outcome)?;

    // A configuration string is not evidence of retrievable archived bytes.
    let supplied_uri = std::env::var("MATRIX_MATH_DURABLE_URI").ok();
    let digest_hex = &input.digest;
    let store = Cas::open(root.join("data").join("cas"))?;
    let stored = crate::cas::store_canonical(&store, &input)?;
    let reports = root.join("docs").join("results").join(digest_hex);
    fs::create_dir_all(&reports)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("create report dir: {error}")))?;
    let tcb = outcome.tcb.to_canonical_json();
    fs::write(reports.join("tcb.json"), &tcb)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write tcb: {error}")))?;
    let assurance = if input.certificate.kind() == "omega" {
        let record = prove::omega_assurance_json(&outcome, digest_hex)?;
        prove::write_compiled_assurance(&outcome, &reports)?;
        fs::write(reports.join("assurance.json"), &record)
            .map_err(|error| CoreError::new(ErrorCode::Io, format!("write assurance: {error}")))?;
        Some(encode_hex(&mm_core::sha256(record.as_bytes())))
    } else {
        None
    };
    let digests = ReportDigests {
        theorem: digest_of(&outcome.module_path)?,
        tcb: encode_hex(&mm_core::sha256(tcb.as_bytes())),
        traceability: digest_of(&root.join("docs/traceability.md"))?,
        assurance,
    };
    let manifest = manifest_json(&input, &claim, &outcome, &digests, supplied_uri.as_deref());

    let manifest_path = reports.join("manifest.json");
    fs::write(&manifest_path, &manifest)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("write manifest: {error}")))?;

    println!("matrix-math report");
    println!("  result id           {digest_hex}");
    println!("  class               {}", LOCAL_RESULT_CLASS);
    println!("  claim               {}", claim.statement);
    println!("  theorem             {}", outcome.result_theorem);
    println!("  certification       {}", outcome.profile.description());
    println!("  local CAS           {stored}");
    println!("  durable URI         none validated");
    if let Some(uri) = supplied_uri.as_deref() {
        println!("  unvalidated URI     {uri}");
    }
    println!("  manifest            {}", manifest_path.display());
    println!();
    println!("{PUBLICATION_BLOCKER}");
    Ok(0)
}

/// Run fresh remote retrieval and full independent release replay (§14.11).
///
/// # Errors
///
/// Returns an I/O error if the pinned local publication controller cannot start.
/// The controller's nonzero exit status propagates without accepting a release.
pub fn verify_release(arguments: &[String]) -> CoreResult<u8> {
    let orchestration_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let python = orchestration_root.join(".venv/bin/python3");
    let mut command = std::process::Command::new(if python.is_file() {
        python
    } else {
        PathBuf::from("python3")
    });
    let checker = std::env::current_exe()
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("current executable: {error}")))?;
    command
        .arg("-I")
        .arg(orchestration_root.join("python/mm_release_cli.py"))
        .arg("verify")
        .arg("--mm")
        .arg(checker)
        .args(arguments);
    // No timeout: the detached proof worker owns its durable terminal receipt.
    let status = command.status().map_err(|error| {
        CoreError::new(ErrorCode::Io, format!("start release controller: {error}"))
    })?;
    Ok(status
        .code()
        .and_then(|code| u8::try_from(code).ok())
        .unwrap_or(2))
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::expect_used,
        clippy::panic,
        clippy::unwrap_used,
        reason = "test assertions must fail loudly"
    )]
    use super::*;

    fn input() -> CanonicalInput {
        crate::cas::load_canonical(
            &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/vectors/omega-l2-hand.json"),
        )
        .expect("omega fixture")
    }

    #[test]
    fn report_keeps_exact_omega_and_never_promotes_a_supplied_uri() {
        let input = input();
        let exact = mm_rat::Rat::from_signeds(2_371_176_123_456_789, 1_000_000_000_000_000);
        let omega = mm_exact::evaluate::OmegaClaim {
            e_total: mm_rat::LowerBound::exact(mm_rat::Rat::one()),
            m_total: mm_rat::LowerBound::exact(mm_rat::Rat::one()),
            requirement: mm_rat::UpperBound::exact(mm_rat::Rat::one()),
            omega: exact,
        };
        let claim = CheckedClaim {
            statement: omega.statement(),
            omega: Some(omega),
        };
        let outcome = prove::ProofOutcome {
            module_path: PathBuf::new(),
            module_name: "test.module".to_owned(),
            cert_theorem: "test.cert".to_owned(),
            result_theorem: "test.result".to_owned(),
            claim: claim.statement.clone(),
            profile: Profile::Cn,
            axioms: vec![],
            tcb: mm_registry::TcbLedger::new(),
            compiled_assurance: Some(prove::CompiledAssurance {
                json: "{\"test\":true}".to_owned(),
                lean_source_closure: "source".to_owned(),
                generated_module_sha256: "module".to_owned(),
            }),
        };
        let digests = ReportDigests {
            theorem: "theorem".to_owned(),
            tcb: "tcb".to_owned(),
            traceability: "traceability".to_owned(),
            assurance: Some("assurance".to_owned()),
        };
        for uri in [None, Some(""), Some("https://unverified.invalid/artifact")] {
            let manifest = manifest_json(&input, &claim, &outcome, &digests, uri);
            assert!(manifest.contains(r#""class":"WORK-IN-PROGRESS""#));
            assert!(manifest.contains(r#""durable_uri":null"#));
            assert!(manifest.contains(r#""omega":"2371176123456789/1000000000000000""#));
            assert!(manifest.contains(r#""claim":"omega <= 2371176123456789/1000000000000000""#));
            assert!(manifest.contains(r#""certificate_encoding":"general""#));
            assert!(manifest.contains(r#""compiled_assurance_sha256":""#));
            assert!(manifest.contains(PUBLICATION_BLOCKER));
        }
        require_matching_claim(&claim, &outcome).expect("same exact claim");
        let mut wrong = outcome;
        wrong.claim = "omega <= 2.371176".to_owned();
        assert_eq!(
            require_matching_claim(&claim, &wrong)
                .expect_err("rounded claim")
                .code(),
            ErrorCode::ImplementationDisagreement
        );
    }

    #[test]
    fn general_and_symmetric_reports_check_the_same_exact_claim() {
        let general = input();
        let Certificate::Omega(certificate) = &general.certificate else {
            panic!("fixture kind")
        };
        let symmetric = mm_schema::symmetric::to_symmetric(certificate).expect("symmetric point");
        let mut bytes = Vec::new();
        let (digest, _) =
            mm_schema::symmetric::encode_symmetric_omega(&mut bytes, &symmetric).expect("encode");
        let symmetric = CanonicalInput {
            certificate: Certificate::Symmetric(symmetric),
            bytes,
            digest: encode_hex(&digest),
        };
        let left = check_claim(&general).expect("general exact check");
        let right = check_claim(&symmetric).expect("symmetric exact check");
        assert_eq!(left.statement, right.statement);
        assert_eq!(
            left.omega.expect("omega").omega,
            right.omega.expect("omega").omega
        );
    }
}
