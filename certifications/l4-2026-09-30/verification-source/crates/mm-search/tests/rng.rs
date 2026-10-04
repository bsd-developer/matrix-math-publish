//! ChaCha20 conformance against RFC 8439 (spec §8.3).

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_search::rng::{ChaCha20Rng, derive_worker_seed};

/// RFC 8439 §2.3.2 test vector.
#[test]
fn rfc8439_block_vector() {
    let mut seed = [0u8; 32];
    for (index, slot) in seed.iter_mut().enumerate() {
        *slot = index as u8;
    }
    let nonce = [0, 0, 0, 9, 0, 0, 0, 0x4a, 0, 0, 0, 0];
    let block = ChaCha20Rng::block(seed, nonce, 1);
    let expected: [u32; 16] = [
        0xe4e7_f110,
        0x1559_3bd1,
        0x1fdd_0f50,
        0xc471_20a3,
        0xc7f4_d1c7,
        0x0368_c033,
        0x9aaa_2204,
        0x4e6c_d4c3,
        0x4664_82d2,
        0x09aa_9f07,
        0x05d7_c214,
        0xa202_8bd9,
        0xd19c_12b5,
        0xb94e_16de,
        0xe883_d0cb,
        0x4e3c_50a2,
    ];
    assert_eq!(block, expected);
}

/// RFC 8439 §2.3.2 vector with an all-zero key at counter zero.
#[test]
fn rfc8439_zero_key_block_zero() {
    let block = ChaCha20Rng::block([0u8; 32], [0u8; 12], 0);
    let expected: [u32; 16] = [
        0xade0_b876,
        0x903d_f1a0,
        0xe56a_5d40,
        0x28bd_8653,
        0xb819_d2bd,
        0x1aed_8da0,
        0xccef_36a8,
        0xc70d_778b,
        0x7c59_41da,
        0x8d48_5751,
        0x3fe0_2477,
        0x374a_d8b8,
        0xf4b8_436a,
        0x1ca1_1815,
        0x69b6_87c3,
        0x8665_eeb2,
    ];
    assert_eq!(block, expected);
}

#[test]
fn the_stream_is_reproducible_from_its_seed() {
    let seed = derive_worker_seed([7u8; 32], 3);
    let first: Vec<u64> = {
        let mut rng = ChaCha20Rng::from_seed(seed);
        (0..64).map(|_| rng.next_u64()).collect()
    };
    let second: Vec<u64> = {
        let mut rng = ChaCha20Rng::from_seed(seed);
        (0..64).map(|_| rng.next_u64()).collect()
    };
    assert_eq!(first, second);
}

#[test]
fn worker_seeds_are_distinct_and_deterministic() {
    let master = [0x5au8; 32];
    let seeds: Vec<_> = (0..64)
        .map(|worker| derive_worker_seed(master, worker))
        .collect();
    let mut unique = seeds.clone();
    unique.sort_unstable();
    unique.dedup();
    assert_eq!(unique.len(), seeds.len(), "worker seeds collided");
    assert_eq!(derive_worker_seed(master, 5), seeds[5]);
    assert_ne!(derive_worker_seed([0x5bu8; 32], 5), seeds[5]);
}

/// Rejection sampling must not bias the outcomes; the uniform baseline of §10.8
/// is what H6 measures learned guidance against.
#[test]
fn below_is_uniform_within_tolerance() {
    let mut rng = ChaCha20Rng::from_seed([1u8; 32]);
    let bound = 7u64;
    let draws = 70_000u64;
    let mut counts = [0u64; 7];
    for _ in 0..draws {
        let value = rng.below(bound);
        assert!(value < bound);
        counts[value as usize] += 1;
    }
    let expected = draws / bound;
    for (value, count) in counts.iter().enumerate() {
        let deviation = count.abs_diff(expected);
        assert!(
            deviation * 20 < expected,
            "value {value} appeared {count} times, expected about {expected}"
        );
    }
}

#[test]
fn below_handles_degenerate_bounds() {
    let mut rng = ChaCha20Rng::from_seed([2u8; 32]);
    assert_eq!(rng.below(0), 0);
    assert_eq!(rng.below(1), 0);
}
