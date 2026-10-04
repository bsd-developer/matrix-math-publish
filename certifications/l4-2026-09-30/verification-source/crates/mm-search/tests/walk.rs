//! Flip-graph search acceptance (spec §12.5, §14.6, §10.5–§10.8).

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::dims::MatMulInstance;
use mm_search::f2::F2State;
use mm_search::walk::{Walk, WalkConfig, WalkOutcome};

fn instance(n: u16, m: u16, p: u16) -> MatMulInstance {
    MatMulInstance::from_raw(n, m, p).expect("supported instance")
}

#[test]
fn the_naive_state_reconstructs_and_has_nmp_terms() {
    for (n, m, p) in [(1u16, 1u16, 1u16), (2, 2, 2), (2, 3, 4), (3, 3, 3)] {
        let state = F2State::naive(instance(n, m, p)).expect("naive");
        assert_eq!(
            state.term_count(),
            usize::from(n) * usize::from(m) * usize::from(p)
        );
        assert!(state.reconstructs().expect("check"), "T[{n},{m},{p}]");
    }
}

/// §14.6: every move preserves exact reconstruction.
#[test]
fn every_flip_and_reduction_preserves_reconstruction() {
    let state = F2State::naive(instance(2, 2, 2)).expect("naive");
    let flips = Walk::enumerate_flips(&state);
    assert!(!flips.is_empty(), "the naive state must admit flips");
    for applied in &flips {
        let terms = Walk::apply(&state, *applied).expect("valid move");
        let moved = F2State::new(state.instance(), terms).expect("state");
        assert!(
            moved.reconstructs().expect("check"),
            "flip {applied:?} broke the tensor sum"
        );
    }
    if let Some(reduction) = Walk::find_reduction(&state) {
        let terms = Walk::apply(&state, reduction).expect("valid move");
        let reduced = F2State::new(state.instance(), terms).expect("state");
        assert!(reduced.reconstructs().expect("check"));
        assert!(reduced.term_count() < state.term_count());
    }
}

/// Exhaustive property check over every move variant on a small state (§14.6
/// implementation order step 2).
#[test]
fn exhaustive_move_property_on_a_small_state() {
    // Walk a few steps first so the state is not the trivial start point.
    let mut walk = Walk::new(
        WalkConfig {
            verify_every_move: true,
            ..WalkConfig::new(instance(2, 2, 2), 7, 40)
        },
        [3u8; 32],
        0,
    )
    .expect("walk");
    let _ = walk.run().expect("walk runs");
    let state = walk.state().clone();

    let flips = Walk::enumerate_flips(&state);
    for applied in flips {
        let terms = Walk::apply(&state, applied).expect("valid move");
        let moved = F2State::new(state.instance(), terms).expect("state");
        assert!(moved.reconstructs().expect("check"), "{applied:?}");
        // A flip never increases the term count once degenerate terms are
        // dropped by normalization (§10.5).
        assert!(moved.term_count() <= state.term_count(), "{applied:?}");
    }
}

/// §14.6: the same config and seed find the same witness at the same step.
#[test]
fn the_same_config_and_seed_replay_identically() {
    let config = WalkConfig::new(instance(2, 2, 2), 7, 200_000);
    let run = |seed: [u8; 32], worker: u32| {
        let mut walk = Walk::new(config, seed, worker).expect("walk");
        let outcome = walk.run().expect("walk runs");
        (
            walk.steps(),
            walk.best().digest_hex(),
            format!("{outcome:?}"),
        )
    };
    let first = run([9u8; 32], 2);
    let second = run([9u8; 32], 2);
    assert_eq!(first, second, "identical seeds diverged");
    let different = run([9u8; 32], 3);
    assert_ne!(
        first.1, different.1,
        "distinct workers must explore differently"
    );
}

/// §12.4 known-answer test: uniform search rediscovers a seven-term `T₂`
/// decomposition over `𝔽₂`.
#[test]
fn uniform_search_rediscovers_seven_term_t2() {
    let config = WalkConfig {
        verify_every_move: true,
        restart_interval: 500,
        ..WalkConfig::new(instance(2, 2, 2), 7, 200_000)
    };
    let mut found = None;
    for worker in 0..8u32 {
        let mut walk = Walk::new(config, [0x42u8; 32], worker).expect("walk");
        if let WalkOutcome::Success(witness) = walk.run().expect("walk runs") {
            assert_eq!(witness.term_count, 7);
            assert!(walk.state().reconstructs().expect("check"));
            found = Some((worker, witness));
            break;
        }
    }
    let (worker, witness) = found.expect("a seven-term T2 must be found within the budget");
    assert_eq!(witness.worker, worker);
    assert!(
        !witness.steps.is_empty(),
        "the witness records its move history"
    );
    // The witness must carry everything §10.8 requires.
    let json = witness.to_canonical_json();
    for field in [
        "worker",
        "worker_seed",
        "step",
        "state_digest",
        "rng_algorithm",
    ] {
        assert!(json.contains(field), "witness is missing {field}");
    }
}

#[test]
fn an_unreachable_target_reports_an_honest_exhausted_run() {
    // Two terms cannot reconstruct T2; the run must exhaust rather than claim.
    let config = WalkConfig::new(instance(2, 2, 2), 2, 2_000);
    let mut walk = Walk::new(config, [1u8; 32], 0).expect("walk");
    match walk.run().expect("walk runs") {
        WalkOutcome::Exhausted {
            best_terms, steps, ..
        } => {
            assert!(best_terms >= 7, "T2 needs at least 7 terms over F2");
            assert!(steps > 0);
        }
        WalkOutcome::Success(_) => panic!("a two-term T2 decomposition cannot exist"),
    }
}

/// §17.4: an optimized path keeps a reference comparison test.
///
/// `count_flips` + `select_flip` sample without materializing the move list.
/// They must agree with `enumerate_flips` on every index, or the walk would no
/// longer be uniform over valid flips and §10.8's baseline would be misstated.
#[test]
fn the_sampler_agrees_with_reference_enumeration() {
    for (n, m, p) in [(2u16, 2u16, 2u16), (2, 3, 3), (3, 3, 3)] {
        let target = instance(n, m, p);
        // Exercise several states along a real walk, not just the start point.
        let mut walk = Walk::new(WalkConfig::new(target, 1, 60), [11u8; 32], 1).expect("walk");
        for _ in 0..6 {
            let state = walk.state().clone();
            let reference = Walk::enumerate_flips(&state);
            let sampled = Walk::sample_all_flips(&state);
            assert_eq!(
                sampled, reference,
                "sampler disagreed with reference enumeration on T[{n},{m},{p}]"
            );
            let _ = walk.run();
        }
    }
}

/// The restart policies must both preserve reconstruction and replay.
#[test]
fn both_restart_policies_are_deterministic_and_sound() {
    use mm_search::walk::RestartPolicy;
    for policy in [RestartPolicy::Naive, RestartPolicy::Best] {
        let config = WalkConfig {
            restart_interval: 25,
            restart_policy: policy,
            verify_every_move: true,
            ..WalkConfig::new(instance(2, 3, 3), 1, 500)
        };
        let run = || {
            let mut walk = Walk::new(config, [21u8; 32], 0).expect("walk");
            let _ = walk.run().expect("walk runs");
            (
                walk.steps(),
                walk.best().digest_hex(),
                walk.best().term_count(),
            )
        };
        let first = run();
        assert_eq!(first, run(), "{policy:?} is not deterministic");
        let mut walk = Walk::new(config, [21u8; 32], 0).expect("walk");
        let _ = walk.run().expect("walk runs");
        assert!(
            walk.best().reconstructs().expect("check"),
            "{policy:?} produced a state that does not reconstruct"
        );
    }
}

/// The bit-packed search state and the certificate representation must agree in
/// both directions, or a search result would not survive being written out.
#[test]
fn state_and_certificate_representations_round_trip() {
    for (n, m, p) in [(2u16, 2u16, 2u16), (2, 3, 4), (3, 3, 3)] {
        let state = F2State::naive(instance(n, m, p)).expect("naive");
        let decomposition = mm_search::state_to_decomposition(&state).expect("to cert");
        let restored = mm_search::decomposition_to_state(&decomposition).expect("back");
        assert_eq!(
            restored, state,
            "round trip changed the state for T[{n},{m},{p}]"
        );
        assert!(restored.reconstructs().expect("check"));
    }
}

/// §10.5 and B4: a plus transition preserves the tensor sum while raising the
/// term count, which is how a walk escapes a plateau that flips cannot.
#[test]
fn plus_transitions_preserve_reconstruction_and_can_reduce_further() {
    use mm_search::walk::RestartPolicy;
    let target = instance(3, 3, 3);
    let config = WalkConfig {
        allow_plus: true,
        plus_interval: 50,
        max_terms: 40,
        restart_interval: 100_000,
        restart_policy: RestartPolicy::Best,
        verify_every_move: true,
        full_check_interval: 0,
        ..WalkConfig::new(target, 23, 20_000)
    };
    let mut walk = Walk::new(config, [77u8; 32], 0).expect("walk");
    let _ = walk.run().expect("walk runs");
    assert!(
        walk.plus_moves() > 0,
        "the fixture must exercise plus transitions"
    );
    assert!(
        walk.state().reconstructs().expect("check"),
        "a plus transition broke the tensor invariant"
    );
    assert!(
        walk.best().reconstructs().expect("check"),
        "the best state must still reconstruct"
    );
    assert!(
        walk.state().term_count() <= config.max_terms,
        "the plus ceiling must hold"
    );
}

/// Plus transitions must not break determinism: the walk is still a function of
/// (seed, step).
#[test]
fn plus_transitions_stay_deterministic() {
    use mm_search::walk::RestartPolicy;
    let config = WalkConfig {
        allow_plus: true,
        plus_interval: 40,
        max_terms: 30,
        restart_policy: RestartPolicy::Best,
        ..WalkConfig::new(instance(2, 2, 2), 7, 5_000)
    };
    let run = || {
        let mut walk = Walk::new(config, [5u8; 32], 1).expect("walk");
        let _ = walk.run().expect("walk runs");
        (walk.steps(), walk.plus_moves(), walk.best().digest_hex())
    };
    assert_eq!(run(), run());
}
