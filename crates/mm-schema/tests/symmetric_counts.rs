//! Group and block counts derived from the instance (`0007_spec.md` §3.2, §3.4).
//!
//! These are the numbers the encoding's whole value rests on, and the decoder
//! derives them from the tree rather than reading them from a certificate.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::level::Level;
use mm_schema::symmetric::{block_count, groups};

#[test]
fn group_and_block_counts_match_the_specification() {
    // §3.2: |Groups| = 15, 60, 213. §3.4: 1 + sum of positive shapes above 2.
    for (level, expected_groups, expected_blocks) in
        [(2u8, 15usize, 1usize), (3, 60, 22), (4, 213, 127)]
    {
        let this = Level::new(level).expect("supported level");
        assert_eq!(groups(this).len(), expected_groups, "groups at l*={level}");
        assert_eq!(block_count(this), expected_blocks, "blocks at l*={level}");
    }
}

#[test]
fn groups_run_by_decreasing_level() {
    let this = Level::new(4).expect("supported level");
    let keys = groups(this);
    let levels: Vec<u8> = keys.iter().map(|key| key.level.get()).collect();
    let mut sorted = levels.clone();
    sorted.sort_by(|a, b| b.cmp(a));
    assert_eq!(levels, sorted, "groups must run by decreasing level (§3.2)");
    assert_eq!(levels.first().copied(), Some(4));
    assert_eq!(levels.last().copied(), Some(2));
}
