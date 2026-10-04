//! `mm replay` (spec §9.3, §12.3).
//!
//! Replay level R2 requires that the same config and seed recreate the same CPU
//! search state and reach the same witness at the same step. This command reruns
//! a recorded search configuration and compares the outcome against the recorded
//! witness, refusing to call a run replayed unless the worker, step, term count,
//! and state digest all match.
//!
//! Wall-clock time is deliberately not compared: §12.3 says it is not a replay
//! coordinate.

use crate::config::SearchConfig;
use mm_core::codes::ErrorCode;
use mm_core::dims::MatMulInstance;
use mm_core::error::{CoreError, CoreResult};
use mm_core::hex::encode_hex;
use mm_search::walk::{RestartPolicy, Walk, WalkConfig, WalkOutcome};
use std::fs;
use std::path::{Path, PathBuf};

/// Extract a **top-level** field from a canonical witness document.
///
/// Depth awareness is not optional here: a witness carries a `steps` array whose
/// elements repeat `step` and `term_count`, so a first-match scan silently reads
/// a step's value instead of the run's. The reader therefore tracks object and
/// array depth and only accepts a key at depth one.
fn field<'a>(text: &'a str, key: &str) -> Option<&'a str> {
    let bytes = text.as_bytes();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    let mut index = 0usize;
    while index < bytes.len() {
        let byte = bytes[index];
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            index += 1;
            continue;
        }
        match byte {
            b'"' => {
                // A key can only start here; check it before entering the string.
                if depth == 1 {
                    let needle = format!("\"{key}\":");
                    if text
                        .get(index..)
                        .is_some_and(|rest| rest.starts_with(&needle))
                    {
                        let start = index + needle.len();
                        let rest = text.get(start..)?;
                        return if let Some(stripped) = rest.strip_prefix('"') {
                            let end = stripped.find('"')?;
                            stripped.get(..end)
                        } else {
                            let end = rest.find([',', '}'])?;
                            rest.get(..end)
                        };
                    }
                }
                in_string = true;
            }
            b'{' | b'[' => depth += 1,
            b'}' | b']' => depth -= 1,
            _ => {}
        }
        index += 1;
    }
    None
}

/// Run `mm replay`.
///
/// # Errors
///
/// Returns [`ErrorCode::ImplementationDisagreement`] when the replay diverges.
pub fn run(arguments: &[String]) -> CoreResult<u8> {
    let mut run_dir: Option<PathBuf> = None;
    let mut level = String::from("bitwise");
    let mut index = 0usize;
    while let Some(argument) = arguments.get(index) {
        match argument.as_str() {
            "--level" => {
                level = arguments
                    .get(index + 1)
                    .cloned()
                    .ok_or_else(|| CoreError::new(ErrorCode::BadConfig, "--level needs a value"))?;
                index += 1;
            }
            other if other.starts_with("--") => {
                return Err(CoreError::new(ErrorCode::BadConfig, "unknown flag").value(other));
            }
            other => run_dir = Some(PathBuf::from(other)),
        }
        index += 1;
    }
    if !matches!(level.as_str(), "witness" | "bitwise" | "statistical") {
        return Err(CoreError::new(
            ErrorCode::BadConfig,
            "level must be witness, bitwise, or statistical",
        )
        .equation("§12.3")
        .value(level));
    }
    let run_dir = run_dir
        .ok_or_else(|| CoreError::new(ErrorCode::BadConfig, "mm replay needs a run directory"))?;

    let config_path = run_dir.join("config.toml");
    let witness_path = find_witness(&run_dir)?;
    let text = fs::read_to_string(&config_path)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("read {config_path:?}: {error}")))?;
    let config = SearchConfig::parse(&text)?;
    let witness_text = fs::read_to_string(&witness_path).map_err(|error| {
        CoreError::new(ErrorCode::Io, format!("read {witness_path:?}: {error}"))
    })?;

    let recorded_worker: u32 = field(&witness_text, "worker")
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| missing("worker"))?;
    let recorded_step: u64 = field(&witness_text, "step")
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| missing("step"))?;
    let recorded_terms: usize = field(&witness_text, "term_count")
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| missing("term_count"))?;
    let recorded_digest = field(&witness_text, "state_digest")
        .ok_or_else(|| missing("state_digest"))?
        .to_owned();

    println!("matrix-math replay");
    println!("  run                 {}", run_dir.display());
    println!("  level               R2 {level}");
    println!("  config sha256       {}", config.digest);
    println!("  recorded worker     {recorded_worker}");
    println!("  recorded step       {recorded_step}");
    println!("  recorded terms      {recorded_terms}");
    println!("  recorded digest     {recorded_digest}");
    println!();

    let instance = MatMulInstance::from_raw(config.n, config.m, config.p)?;
    let walk_config = WalkConfig {
        instance,
        target_terms: config.target_terms,
        step_budget: config.step_budget,
        restart_interval: config.restart_interval.max(1),
        verify_every_move: false,
        full_check_interval: 0,
        allow_plus: config.allow_plus,
        plus_interval: config.plus_interval,
        max_terms: config.max_terms,
        restart_policy: if config.restart_policy == "naive" {
            RestartPolicy::Naive
        } else {
            RestartPolicy::Best
        },
    };
    let mut walk = Walk::new(walk_config, config.master_seed, recorded_worker)?;
    let outcome = walk.run()?;

    let (step, terms, digest) = match outcome {
        WalkOutcome::Success(witness) => (
            witness.step,
            witness.term_count,
            encode_hex(&witness.state_digest),
        ),
        WalkOutcome::Exhausted {
            best_terms,
            best_digest,
            steps,
        } => (steps, best_terms, encode_hex(&best_digest)),
    };

    println!("  replayed step       {step}");
    println!("  replayed terms      {terms}");
    println!("  replayed digest     {digest}");
    println!();

    let mut mismatches = Vec::new();
    if terms != recorded_terms {
        mismatches.push(format!("term count {recorded_terms} -> {terms}"));
    }
    if digest != recorded_digest {
        mismatches.push(format!("state digest {recorded_digest} -> {digest}"));
    }
    // R2 additionally pins the step; R1 only re-verifies the published witness.
    if level == "bitwise" && step != recorded_step {
        mismatches.push(format!("step {recorded_step} -> {step}"));
    }

    if mismatches.is_empty() {
        println!("REPLAYED");
        Ok(0)
    } else {
        Err(CoreError::new(
            ErrorCode::ImplementationDisagreement,
            "the replay diverged from the recorded witness",
        )
        .equation("§12.3")
        .value(mismatches.join("; ")))
    }
}

fn find_witness(run_dir: &Path) -> CoreResult<PathBuf> {
    let direct = run_dir.join("witness.json");
    if direct.is_file() {
        return Ok(direct);
    }
    let mut candidates: Vec<PathBuf> = fs::read_dir(run_dir)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("read {run_dir:?}: {error}")))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.to_string_lossy().ends_with(".witness.json"))
        .collect();
    candidates.sort();
    candidates.into_iter().next().ok_or_else(|| {
        CoreError::new(ErrorCode::Io, "no witness file found in the run directory")
            .equation("§12.3")
    })
}

fn missing(field_name: &str) -> CoreError {
    CoreError::new(
        ErrorCode::BadConfig,
        "the witness is missing a required field",
    )
    .equation("§10.8")
    .value(field_name)
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::expect_used,
        clippy::panic,
        clippy::unwrap_used,
        reason = "test assertions must fail loudly; §17.1 governs library code"
    )]

    use super::field;

    /// A witness repeats `step` and `term_count` inside its `steps` array. A
    /// first-match scan reads a step's value instead of the run's, which is a
    /// silent wrong answer rather than an error.
    #[test]
    fn nested_keys_do_not_shadow_top_level_ones() {
        let witness = concat!(
            r#"{"restart":0,"state_digest":"ab","step":211,"steps":["#,
            r#"{"step":1,"term_count":8},{"step":2,"term_count":8}],"#,
            r#""term_count":7,"worker":3}"#
        );
        assert_eq!(field(witness, "term_count"), Some("7"));
        assert_eq!(field(witness, "step"), Some("211"));
        assert_eq!(field(witness, "worker"), Some("3"));
        assert_eq!(field(witness, "state_digest"), Some("ab"));
        assert_eq!(field(witness, "absent"), None);
    }

    /// A key-like sequence inside a string value must not be mistaken for a key.
    #[test]
    fn keys_inside_string_values_are_ignored() {
        let witness = r#"{"note":"contains "term_count":99 inside","term_count":5}"#;
        assert_eq!(field(witness, "term_count"), Some("5"));
    }

    /// `steps` must not match a scan for `step`.
    #[test]
    fn a_prefix_key_does_not_match() {
        let witness = r#"{"steps":[],"term_count":4}"#;
        assert_eq!(field(witness, "step"), None);
    }
}
