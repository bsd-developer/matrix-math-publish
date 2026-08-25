//! `mm search` (spec §9.3, §10.8, §13.1–§13.3).
//!
//! Independent uniform random walks, one per configured worker, with no shared
//! mutable search state (§10.8). Worker outputs are merged deterministically by
//! `(objective, worker_id, step, digest)` (§13.3), so the reported result does
//! not depend on which thread happened to finish first.
//!
//! A successful run emits a canonical decomposition certificate. That
//! certificate is a *candidate* until the Lean checker accepts it: the search is
//! untrusted (§1.1).

use crate::config::SearchConfig;
use mm_core::codes::ErrorCode;
use mm_core::dims::MatMulInstance;
use mm_core::error::{CoreError, CoreResult};
use mm_core::hex::encode_hex;
use mm_registry::Cas;
use mm_schema::{AnyDecomposition, encode_decomposition};
use mm_search::f2::F2State;
use mm_search::walk::{RestartPolicy, Walk, WalkConfig, WalkOutcome, WalkSnapshot};
use mm_search::witness::Witness;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

/// One worker's result, in the order §13.3 merges by.
#[derive(Clone, Debug)]
struct WorkerResult {
    best_terms: usize,
    worker: u32,
    step: u64,
    digest: [u8; 32],
    state: F2State,
    witness: Option<Box<Witness>>,
    interrupted: bool,
}

/// The process resident set size in mebibytes, if it can be determined.
///
/// Read through `ps` rather than a platform crate so the I/O shell needs no
/// `unsafe` and no additional dependency; §13.5 only needs this at checkpoint
/// granularity.
fn resident_set_mib() -> Option<u64> {
    let pid = std::process::id();
    let output = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&output.stdout);
    text.trim().parse::<u64>().ok().map(|kib| kib / 1024)
}

/// Install a SIGINT handler that requests a checkpoint (§13.2).
///
/// Registration is best effort: a platform that refuses simply leaves the run
/// uninterruptible, which is a degraded experience rather than a wrong result.
fn install_interrupt_handler(flag: &Arc<AtomicBool>) {
    let flag = Arc::clone(flag);
    let _ = signal_hook::flag::register(signal_hook::consts::SIGINT, flag);
}

/// The §13.2 checkpoint record: normalized config hash, algorithm state, every
/// worker RNG state, step counters, current best candidate, and tool versions.
fn checkpoint_json(config_digest: &str, snapshot: &WalkSnapshot) -> String {
    let mut out = String::from("{\"best_terms\":");
    out.push_str(&snapshot.best_terms.len().to_string());
    out.push_str(",\"config_sha256\":");
    mm_core::error::push_json_string(&mut out, config_digest);
    out.push_str(",\"restart\":");
    out.push_str(&snapshot.restart.to_string());
    out.push_str(",\"rng_algorithm\":");
    mm_core::error::push_json_string(&mut out, mm_search::rng::RNG_ALGORITHM);
    out.push_str(",\"rng_counter\":");
    out.push_str(&snapshot.rng_counter.to_string());
    out.push_str(",\"schema\":\"matrix-math-checkpoint/1\",\"since_improvement\":");
    out.push_str(&snapshot.since_improvement.to_string());
    out.push_str(",\"spec_version\":");
    mm_core::error::push_json_string(&mut out, mm_core::SPEC_VERSION);
    out.push_str(",\"state_terms\":");
    out.push_str(&snapshot.state_terms.len().to_string());
    out.push_str(",\"steps\":");
    out.push_str(&snapshot.steps.to_string());
    out.push_str(",\"worker\":");
    out.push_str(&snapshot.worker.to_string());
    out.push_str(",\"worker_seed\":");
    mm_core::error::push_json_string(&mut out, &encode_hex(&snapshot.worker_seed));
    out.push('}');
    out
}

/// Wrap a search state as the ring-tagged decomposition the schema encodes.
///
/// # Errors
///
/// Propagates conversion failures.
fn state_to_certificate(state: &F2State) -> CoreResult<AnyDecomposition> {
    Ok(AnyDecomposition::Fp(mm_search::state_to_decomposition(
        state,
    )?))
}

/// Run `mm search`.
///
/// # Errors
///
/// Returns the first structured rejection (§5.4).
pub fn run(arguments: &[String]) -> CoreResult<u8> {
    let mut config_path: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut index = 0usize;
    while let Some(argument) = arguments.get(index) {
        match argument.as_str() {
            "--config" => {
                config_path = arguments.get(index + 1).map(PathBuf::from);
                index += 1;
            }
            "--out" => {
                output = arguments.get(index + 1).map(PathBuf::from);
                index += 1;
            }
            other if other.starts_with("--") => {
                return Err(CoreError::new(ErrorCode::BadConfig, "unknown flag").value(other));
            }
            other => config_path = Some(PathBuf::from(other)),
        }
        index += 1;
    }
    let config_path = config_path
        .ok_or_else(|| CoreError::new(ErrorCode::BadConfig, "mm search needs --config <toml>"))?;
    let text = fs::read_to_string(&config_path)
        .map_err(|error| CoreError::new(ErrorCode::Io, format!("read {config_path:?}: {error}")))?;
    let config = SearchConfig::parse(&text)?;
    let instance = MatMulInstance::from_raw(config.n, config.m, config.p)?;

    println!("matrix-math search");
    println!("  config              {}", config_path.display());
    println!("  config sha256       {}", config.digest);
    println!(
        "  algorithm           {} {}",
        config.algorithm, config.algorithm_version
    );
    println!("  rng                 {}", mm_search::rng::RNG_ALGORITHM);
    println!("  instance            {instance}");
    println!("  target terms        {}", config.target_terms);
    println!("  master seed         {}", encode_hex(&config.master_seed));
    println!("  workers             {}", config.workers);
    println!(
        "  restart policy      {} every {} idle steps",
        config.restart_policy, config.restart_interval
    );
    println!("  step budget         {} per worker", config.step_budget);
    if config.allow_plus {
        println!(
            "  plus transitions    enabled every {} idle steps, ceiling {} terms (§10.5)",
            config.plus_interval, config.max_terms
        );
    } else {
        println!("  plus transitions    disabled (§10.5 baseline)");
    }
    println!("  hardware profile    {}", config.hardware_profile);
    println!("  memory limit        {} MiB", config.memory_limit_mib);
    println!("  checkpoint every    {} steps", config.checkpoint_interval);
    if config.wall_clock_limit_seconds > 0 {
        println!(
            "  wall-clock limit    {}s (checkpoints only; the step counter defines progress)",
            config.wall_clock_limit_seconds
        );
    }
    println!();

    let walk_config = WalkConfig {
        instance,
        target_terms: config.target_terms,
        step_budget: config.step_budget,
        restart_interval: config.restart_interval.max(1),
        verify_every_move: config.verify_every_move,
        full_check_interval: config.full_check_interval,
        allow_plus: config.allow_plus,
        plus_interval: config.plus_interval,
        max_terms: config.max_terms,
        restart_policy: if config.restart_policy == "naive" {
            RestartPolicy::Naive
        } else {
            RestartPolicy::Best
        },
    };

    // SIGINT requests a checkpoint and exits with code 7 (§13.2). The flag is
    // polled between slices rather than acted on inside a move, so a checkpoint
    // is never taken mid-transition.
    let interrupted = Arc::new(AtomicBool::new(false));
    install_interrupt_handler(&interrupted);

    let cas = Cas::open(PathBuf::from("data/cas")).ok();
    let memory_limit_mib = config.memory_limit_mib;
    let checkpoint_interval = config.checkpoint_interval.max(1);
    let wall_clock_limit = config.wall_clock_limit_seconds;
    let config_digest = config.digest.clone();

    // Independent workers with no shared mutable search state (§10.8).
    let mut handles = Vec::new();
    for worker in 0..config.workers {
        let seed = config.master_seed;
        let interrupted = Arc::clone(&interrupted);
        let cas = cas.clone();
        let config_digest = config_digest.clone();
        handles.push(std::thread::spawn(move || -> CoreResult<WorkerResult> {
            let started = Instant::now();
            let mut walk = Walk::new(walk_config, seed, worker)?;
            let mut witness = None;
            let mut interrupted_here = false;
            loop {
                if let Some(outcome) = walk.run_slice(checkpoint_interval)? {
                    if let WalkOutcome::Success(found) = outcome {
                        witness = Some(found);
                    }
                    break;
                }
                if let Some(store) = cas.as_ref() {
                    let record = checkpoint_json(&config_digest, &walk.snapshot());
                    let _ = store.put(record.as_bytes());
                }
                if interrupted.load(Ordering::Relaxed) {
                    interrupted_here = true;
                    break;
                }
                // §13.5: monitor RSS and stop before sustained swapping. The
                // exit is structured and the checkpoint above is already
                // durable, so the run stays replayable.
                if memory_limit_mib > 0
                    && let Some(rss_mib) = resident_set_mib()
                    && rss_mib > memory_limit_mib
                {
                    return Err(CoreError::new(
                        ErrorCode::ResourceLimit,
                        "the search exceeded its configured memory limit",
                    )
                    .equation("§13.5")
                    .value(format!("{rss_mib} MiB > {memory_limit_mib} MiB")));
                }
                // A wall-clock limit checkpoints but does not define progress
                // (§10.8); the step counter is the replay coordinate.
                if wall_clock_limit > 0 && started.elapsed().as_secs() >= wall_clock_limit {
                    break;
                }
            }
            Ok(WorkerResult {
                best_terms: walk.best().term_count(),
                worker,
                step: walk.steps(),
                digest: walk.best().digest(),
                state: walk.best().clone(),
                witness,
                interrupted: interrupted_here,
            })
        }));
    }

    let mut results = Vec::new();
    for handle in handles {
        match handle.join() {
            Ok(result) => results.push(result?),
            Err(_) => {
                return Err(CoreError::new(
                    ErrorCode::Io,
                    "a search worker panicked; this is an internal defect (§9.3 code 8)",
                ));
            }
        }
    }

    // Deterministic merge order (§13.3).
    results.sort_by(|left, right| {
        left.best_terms
            .cmp(&right.best_terms)
            .then(left.worker.cmp(&right.worker))
            .then(left.step.cmp(&right.step))
            .then(left.digest.cmp(&right.digest))
    });

    for result in &results {
        println!(
            "  worker {:>3}  best {:>4} terms  step {:>10}  {}",
            result.worker,
            result.best_terms,
            result.step,
            encode_hex(&result.digest).get(..16).unwrap_or_default()
        );
    }
    println!();

    let Some(best) = results.first() else {
        return Err(CoreError::new(ErrorCode::BadConfig, "no workers ran"));
    };

    // Re-verify the best state exactly before emitting anything.
    if !best.state.reconstructs()? {
        return Err(CoreError::new(
            ErrorCode::ReconstructionMismatch,
            "the best search state does not reconstruct the target tensor",
        )
        .equation("B1"));
    }

    let decomposition = state_to_certificate(&best.state)?;
    let destination = output.unwrap_or_else(|| {
        PathBuf::from(format!(
            "data/search/{}-{}-terms.json",
            config.target, best.best_terms
        ))
    });
    if let Some(parent) = destination.parent() {
        fs::create_dir_all(parent).map_err(|error| {
            CoreError::new(ErrorCode::Io, format!("create {parent:?}: {error}"))
        })?;
    }
    let file = fs::File::create(&destination).map_err(|error| {
        CoreError::new(ErrorCode::Io, format!("create {destination:?}: {error}"))
    })?;
    let (digest, byte_count) = encode_decomposition(file, &decomposition)?;

    println!("  best term count     {}", best.best_terms);
    println!("  certificate         {}", destination.display());
    println!("  canonical sha256    {}", encode_hex(&digest));
    println!("  canonical bytes     {byte_count}");
    if let Some(witness) = &best.witness {
        let witness_path = destination.with_extension("witness.json");
        fs::write(&witness_path, witness.to_canonical_json())
            .map_err(|error| CoreError::new(ErrorCode::Io, format!("write witness: {error}")))?;
        println!("  witness             {}", witness_path.display());
        println!();
        println!("SUCCESS: reached {} terms", best.best_terms);
        println!("The claim begins when `mm verify` and `mm prove` accept this certificate.");
        Ok(0)
    } else {
        println!();
        println!(
            "EXHAUSTED: best {} terms, target {} not reached within the budget",
            best.best_terms, config.target_terms
        );
        println!("This is an honest negative result, not an implementation failure (§8.4).");
        if results.iter().any(|result| result.interrupted) {
            // §9.3 code 7: interrupted after a successful checkpoint.
            return Ok(7);
        }
        Ok(0)
    }
}
