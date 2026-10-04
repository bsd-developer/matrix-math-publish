//! Identity 1: group masses aggregate node masses (`0007_spec.md` §5.2).
//!
//! `groupMass_eq_sum` is the Lean statement Stage C must prove. This is the
//! empirical form of it on real certificates: the group mass computed from S1
//! and S2 over 60 groups must equal the sum of the general evaluator's node
//! masses over the 5,779 nodes of the same level and shape.
//!
//! Exact rational equality is demanded, not a tolerance. §5.7 explains why that
//! is available: every quantity is a rational and the aggregation is
//! distributivity.

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_exact::bridge::from_certificate;
use mm_exact::symmetric::group_masses;
use mm_rat::rational::Rat;
use mm_schema::symmetric::{groups, to_symmetric};
use mm_schema::{CanonicalReader, Limits, decode_omega};
use std::fs;
use std::io::BufReader;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn load(relative: &str) -> mm_schema::OmegaCertificate {
    let path = repo_root().join(relative);
    let file = fs::File::open(&path).unwrap_or_else(|error| panic!("open {path:?}: {error}"));
    let mut reader = CanonicalReader::new(BufReader::new(file), Limits::default());
    let certificate = decode_omega(&mut reader).expect("decode");
    reader.finish().expect("trailing bytes");
    certificate
}

#[test]
fn group_masses_equal_the_node_masses_they_aggregate() {
    for relative in [
        "tests/vectors/omega-l2-hand.json",
        "tests/vectors/omega-l3-optimized.json",
        "tests/vectors/omega-l3-uniform.json",
    ] {
        let general = load(relative);
        let symmetric = to_symmetric(&general).expect("symmetric");
        let evaluable = from_certificate(&general).expect("bridge");

        let computed = group_masses(&symmetric).expect("group masses");
        let keys = groups(symmetric.level);
        assert_eq!(computed.len(), keys.len());

        // The general side: sum node masses by (level, shape).
        let nodes = evaluable.tree.nodes();
        let masses = evaluable.tree.masses();
        for (index, key) in keys.iter().enumerate() {
            let mut expected = Rat::zero();
            for (node, mass) in nodes.iter().zip(masses.iter()) {
                let Some(shape) = node.shape else { continue };
                if shape == key.shape && shape.level() == key.level {
                    expected = &expected + mass;
                }
            }
            assert_eq!(
                computed[index],
                expected,
                "{relative}: group (level {}, shape {}) mass",
                key.level.get(),
                key.shape
            );
        }
    }
}

#[test]
fn the_top_level_masses_are_the_root_alpha() {
    // S1: M(l*, s) = alpha_G(s), with no region weights involved, because
    // alpha_G does not depend on the region and A_G is a distribution.
    let general = load("tests/vectors/omega-l3-optimized.json");
    let symmetric = to_symmetric(&general).expect("symmetric");
    let computed = group_masses(&symmetric).expect("group masses");
    let keys = groups(symmetric.level);
    let mm_schema::symmetric::GroupPayload::Branching { alpha, .. } = &symmetric.root else {
        panic!("the root is branching");
    };
    let top: Vec<&Rat> = keys
        .iter()
        .enumerate()
        .filter(|(_, key)| key.level == symmetric.level)
        .map(|(index, _)| &computed[index])
        .collect();
    assert_eq!(top.len(), alpha.len());
    for (got, want) in top.iter().zip(alpha.iter()) {
        assert_eq!(*got, want);
    }
}

#[test]
#[ignore = "slow tier: the general beta table over 5,779 nodes needs --release"]
fn group_beta_equals_the_node_beta_it_replaces() {
    // Identities 3 and 4 (§5.4, §5.5) together: the A6 region mixture collapses
    // when beta is region-independent, and A5's concatenation is the outer
    // product the dense representation computes. Every node of a group must
    // therefore carry exactly the group's beta.
    use mm_exact::evaluate::beta_table;
    use mm_exact::symmetric::group_beta_table;

    for relative in [
        "tests/vectors/omega-l2-hand.json",
        "tests/vectors/omega-l3-optimized.json",
        "tests/vectors/omega-l3-uniform.json",
    ] {
        let general = load(relative);
        let symmetric = to_symmetric(&general).expect("symmetric");
        let evaluable = from_certificate(&general).expect("bridge");

        let group_table = group_beta_table(&symmetric).expect("group beta");
        let node_table = beta_table(&evaluable.tree).expect("node beta");
        let keys = groups(symmetric.level);
        let nodes = evaluable.tree.nodes();

        let mut compared = 0usize;
        for (node, node_beta) in nodes.iter().zip(node_table.iter()) {
            let Some(shape) = node.shape else { continue };
            let index = keys
                .iter()
                .position(|key| key.shape == shape && key.level == shape.level())
                .expect("every node's group is enumerated");
            for coordinate in 0..3 {
                assert_eq!(
                    group_table[index][coordinate], node_beta[coordinate],
                    "{relative}: beta mismatch at shape {shape} coordinate {coordinate}"
                );
            }
            compared += 1;
        }
        assert!(compared > 0, "{relative}: nothing compared");
        println!(
            "  {relative}: {compared} nodes matched against {} groups",
            keys.len()
        );
    }
}

#[test]
#[ignore = "slow tier: exact evaluation over 5,779 nodes at 256 bits needs --release"]
fn group_leaf_aggregates_equal_the_general_totals() {
    // Identity 5 (§5.6): A17's E_2 and A20's M_total sum over leaves by distinct
    // NodePath; under symmetry each regroups by group using aggregated masses.
    // At l*=4 the general side is 1,080,288 zero-shape leaves plus 437,400
    // positive level-two leaves; the group side visits 213 entries.
    use mm_exact::evaluate::{e_level_two, m_total};
    use mm_exact::symmetric::{group_e_level_two, group_m_total};
    use mm_rat::log2::Precision;

    for relative in [
        "tests/vectors/omega-l2-hand.json",
        "tests/vectors/omega-l3-optimized.json",
        "tests/vectors/omega-l3-uniform.json",
    ] {
        let general = load(relative);
        let symmetric = to_symmetric(&general).expect("symmetric");
        let evaluable = from_certificate(&general).expect("bridge");
        let precision = Precision::new(general.log_precision_bits).expect("precision");
        let masses = mm_exact::symmetric::group_masses(&symmetric).expect("masses");

        let general_m = m_total(&evaluable.tree, precision).expect("m_total");
        let group_m = group_m_total(&symmetric, &masses, general.q, precision).expect("group m");
        assert_eq!(
            group_m.value(),
            general_m.value(),
            "{relative}: M_total must agree exactly"
        );

        let general_e2 = e_level_two(&evaluable.tree, precision).expect("e_level_two");
        let group_e2 = group_e_level_two(&symmetric, &masses, precision).expect("group e2");
        assert_eq!(
            group_e2.value(),
            general_e2.value(),
            "{relative}: E_2 must agree exactly"
        );
        println!("  {relative}: M_total and E_2 agree exactly");
    }
}

#[test]
#[ignore = "slow tier: the general E_l over 5,778 nodes needs --release"]
fn group_level_exponents_equal_the_general_ones() {
    // S3 (§5.4): the largest identity, and the one carrying the eta_Y trap.
    // A15 does NOT collapse over regions -- the region-r quantity depends on r
    // through the permutation pi_r, and Q_Y takes the ORDERED pair because A8
    // and A12 sum over u_Y while selecting on u_Z. Getting that wrong is the
    // defect omega-l3.md records, caught by float-versus-exact disagreement
    // rather than inspection, so it is checked here the same way: exactly,
    // against the general evaluator, on real certificates.
    use mm_exact::evaluate::{beta_table, e_level};
    use mm_exact::symmetric::{group_beta_table, group_e_level, group_masses};
    use mm_rat::log2::Precision;
    use std::collections::VecDeque;

    for relative in [
        "tests/vectors/omega-l3-optimized.json",
        "tests/vectors/omega-l3-uniform.json",
    ] {
        let general = load(relative);
        let symmetric = to_symmetric(&general).expect("symmetric");
        let evaluable = from_certificate(&general).expect("bridge");
        let precision = Precision::new(general.log_precision_bits).expect("precision");
        let level = symmetric.level;

        let masses = group_masses(&symmetric).expect("masses");
        let group_beta = group_beta_table(&symmetric).expect("group beta");
        let node_beta = beta_table(&evaluable.tree).expect("node beta");

        // The general side consumes blocks in order after the root's six.
        let mut queue: VecDeque<_> = evaluable.blocks.iter().skip(6).cloned().collect();
        let general_e = e_level(&evaluable.tree, level, &mut queue, &node_beta, precision)
            .expect("general e_level");

        let blocks: Vec<_> = symmetric
            .blocks
            .iter()
            .map(|block| mm_exact::maxent::MaxEntropyBlock {
                y: block.y.clone(),
                lambda0: block.lambda0.clone(),
                lambda_x: block.lambda_x.clone(),
                lambda_y: block.lambda_y.clone(),
                lambda_z: block.lambda_z.clone(),
                epsilon: block.epsilon.clone(),
            })
            .collect();
        let group_e = group_e_level(&symmetric, &masses, &group_beta, &blocks, level, precision)
            .expect("group e_level");

        assert_eq!(
            group_e.value(),
            general_e.value(),
            "{relative}: E_l must agree exactly at level {}",
            level.get()
        );
        println!("  {relative}: E_l agrees exactly at level {}", level.get());
    }
}

#[test]
#[ignore = "slow tier: the general evaluation over 5,779 nodes needs --release"]
fn the_symmetric_path_reproduces_every_bound_without_expanding() {
    // §5.1 asks for equality, not merely implication. This is that equality on
    // real certificates: all six A20 quantities, computed from 60 groups without
    // ever materializing the 5,779-node expansion, against the general
    // evaluator's own numbers.
    use mm_exact::evaluate::evaluate_bounds;
    use mm_exact::symmetric::group_evaluate_bounds;
    use mm_rat::log2::Precision;

    for relative in [
        "tests/vectors/omega-l2-hand.json",
        "tests/vectors/omega-l3-optimized.json",
        "tests/vectors/omega-l3-uniform.json",
    ] {
        let general = load(relative);
        let symmetric = to_symmetric(&general).expect("symmetric");
        let evaluable = from_certificate(&general).expect("bridge");
        let precision = Precision::new(general.log_precision_bits).expect("precision");

        let want =
            evaluate_bounds(&evaluable.tree, &evaluable.blocks, precision).expect("general bounds");
        let got = group_evaluate_bounds(&symmetric, precision).expect("group bounds");

        assert_eq!(got.e_root.value(), want.e_root.value(), "{relative}: E_G");
        assert_eq!(got.e_two.value(), want.e_two.value(), "{relative}: E_2");
        assert_eq!(
            got.e_interior.value(),
            want.e_interior.value(),
            "{relative}: interior"
        );
        assert_eq!(
            got.e_total.value(),
            want.e_total.value(),
            "{relative}: E_total"
        );
        assert_eq!(
            got.m_total.value(),
            want.m_total.value(),
            "{relative}: M_total"
        );
        assert_eq!(
            got.requirement.value(),
            want.requirement.value(),
            "{relative}: requirement"
        );
        assert_eq!(
            got.minimal_omega(),
            want.minimal_omega(),
            "{relative}: the least accepted Omega"
        );
        println!("  {relative}: all six bounds and the minimal Omega agree exactly");
    }
}
