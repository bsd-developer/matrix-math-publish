//! Domain-type conformance tests (spec §10.3, §5.1, §5.2, §6.6).

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::dims::TensorMode;
use mm_core::level::{MAX_LEVEL, MIN_LEVEL};
use mm_core::path::{NodeKind, Walk, collect_paths, node_count, visit_preorder};
use mm_core::{Coordinate, Dim, ErrorCode, Level, MatMulInstance, PrimeModulus, Region, Shape};

fn level(value: u8) -> Level {
    Level::new(value).expect("supported level")
}

#[test]
fn level_rejects_unsupported_range() {
    for value in [0u8, 1, 5, 6, 255] {
        let error = Level::new(value).expect_err("out-of-range level must reject");
        assert_eq!(error.code(), ErrorCode::UnsupportedInstance);
    }
    for value in MIN_LEVEL..=MAX_LEVEL {
        assert_eq!(level(value).get(), value);
    }
}

#[test]
fn level_powers_are_exact() {
    assert_eq!(level(2).shape_sum(), 4);
    assert_eq!(level(3).shape_sum(), 8);
    assert_eq!(level(4).shape_sum(), 16);
    assert_eq!(level(2).support_len(), 2);
    assert_eq!(level(3).support_len(), 4);
    assert_eq!(level(4).support_len(), 8);
}

#[test]
fn level_two_has_no_children() {
    assert_eq!(
        level(2).child().expect_err("level 2 is a leaf").code(),
        ErrorCode::BadPath
    );
    assert_eq!(level(3).child().expect("level 3 has children").get(), 2);
}

/// §5.1 fixes the region table literally; no library permutation order may be
/// substituted implicitly.
#[test]
fn region_permutation_table_is_normative() {
    use Coordinate::{X, Y, Z};
    let expected = [
        (1u8, [X, Y, Z]),
        (2, [X, Z, Y]),
        (3, [Y, X, Z]),
        (4, [Y, Z, X]),
        (5, [Z, X, Y]),
        (6, [Z, Y, X]),
    ];
    for (id, permutation) in expected {
        let region = Region::new(id).expect("valid region");
        assert_eq!(region.permutation(), permutation, "region {id}");
    }
    for value in [0u8, 7, 255] {
        assert_eq!(
            Region::new(value).expect_err("bad region").code(),
            ErrorCode::UnsupportedInstance
        );
    }
}

#[test]
fn region_permutation_is_a_bijection_with_exact_inverse() {
    for region in Region::all() {
        let image = region.permutation();
        let mut seen = [false; 3];
        for coordinate in image {
            assert!(
                !seen[coordinate.index()],
                "region {region} is not injective"
            );
            seen[coordinate.index()] = true;
        }
        for coordinate in Coordinate::ALL {
            assert_eq!(region.unpermute(region.permute(coordinate)), coordinate);
            assert_eq!(region.permute(region.unpermute(coordinate)), coordinate);
        }
    }
}

#[test]
fn shape_enumeration_is_lexicographic_and_complete() {
    for value in MIN_LEVEL..=MAX_LEVEL {
        let l = level(value);
        let shapes = Shape::enumerate(l);
        assert_eq!(shapes.len(), Shape::count(l), "level {value} count");
        for window in shapes.windows(2) {
            assert!(
                window[0].canonical_key() < window[1].canonical_key(),
                "level {value} enumeration is not strictly lexicographic"
            );
        }
        for shape in &shapes {
            let [x, y, z] = shape.coords();
            assert_eq!(x + y + z, l.shape_sum());
        }
    }
}

#[test]
fn shape_rejects_wrong_sum() {
    let error = Shape::new(level(2), 1, 1, 1).expect_err("sum must be 2^l");
    assert_eq!(error.code(), ErrorCode::UnsupportedInstance);
    assert_eq!(error.equation_id(), Some("A.1"));
    assert!(Shape::new(level(2), 1, 1, 2).is_ok());
}

#[test]
fn shape_positivity_classification() {
    let positive = Shape::new(level(2), 1, 1, 2).expect("valid");
    assert!(positive.is_positive());
    assert!(!positive.is_zero_shape());
    let zero = Shape::new(level(2), 0, 1, 3).expect("valid");
    assert!(zero.is_zero_shape());
    assert_eq!(zero.first_zero_coord(), Some(Coordinate::X));
    assert_eq!(zero.first_nonzero_coord(), Some(Coordinate::Y));
}

/// `Split(s) = { u ∈ S_(ℓ-1) : 0 ≤ u_W ≤ s_W }` (A.1).
#[test]
fn splits_match_the_defining_predicate() {
    let l3 = level(3);
    for shape in Shape::enumerate(l3) {
        let splits = shape.splits().expect("level 3 has splits");
        let brute: Vec<Shape> = Shape::enumerate(level(2))
            .into_iter()
            .filter(|candidate| {
                let [ux, uy, uz] = candidate.coords();
                let [sx, sy, sz] = shape.coords();
                ux <= sx && uy <= sy && uz <= sz
            })
            .collect();
        assert_eq!(splits, brute, "splits of {shape}");
        for window in splits.windows(2) {
            assert!(window[0].canonical_key() < window[1].canonical_key());
        }
        for split in &splits {
            let complement = shape.complement(*split).expect("complement exists");
            let [cx, cy, cz] = complement.coords();
            let [ux, uy, uz] = split.coords();
            let [sx, sy, sz] = shape.coords();
            assert_eq!((cx + ux, cy + uy, cz + uz), (sx, sy, sz));
        }
    }
}

#[test]
fn complement_rejects_a_split_above_its_parent() {
    let parent = Shape::new(level(3), 1, 1, 6).expect("valid");
    let bad = Shape::new(level(2), 2, 1, 1).expect("valid");
    let error = parent.complement(bad).expect_err("2 > 1 in X");
    assert_eq!(error.code(), ErrorCode::BadPath);
}

/// The complete normative `T₂` support table of Appendix B.2.
#[test]
fn t2_support_table_is_normative() {
    let instance = MatMulInstance::from_raw(2, 2, 2).expect("valid instance");
    let expected = [
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize),
        (0, 0, 1, 0, 1, 2),
        (0, 1, 0, 1, 2, 0),
        (0, 1, 1, 1, 3, 2),
        (1, 0, 0, 2, 0, 1),
        (1, 0, 1, 2, 1, 3),
        (1, 1, 0, 3, 2, 1),
        (1, 1, 1, 3, 3, 3),
    ];
    let mut support = Vec::new();
    for (i, k, j, fa, fb, fc) in expected {
        assert_eq!(
            instance.flat_a(i, k).expect("in range"),
            fa,
            "flatA({i},{k})"
        );
        assert_eq!(
            instance.flat_b(k, j).expect("in range"),
            fb,
            "flatB({k},{j})"
        );
        assert_eq!(
            instance.flat_c_dual(j, i).expect("in range"),
            fc,
            "flatCdual({j},{i})"
        );
        support.push((fa, fb, fc));
    }
    support.sort_unstable();
    support.dedup();
    assert_eq!(support.len(), 8, "the T2 support has exactly eight entries");
    let total = instance.entry_count().expect("no overflow");
    assert_eq!(total, 64);
    assert_eq!(total - support.len(), 56, "the other 56 entries are zero");
}

#[test]
fn flattening_round_trips_through_dimension_twelve() {
    for n in 1..=12u16 {
        for m in 1..=12u16 {
            for p in 1..=12u16 {
                let instance = MatMulInstance::from_raw(n, m, p).expect("supported");
                for i in 0..instance.n().as_usize() {
                    for k in 0..instance.m().as_usize() {
                        let flat = instance.flat_a(i, k).expect("in range");
                        assert_eq!(instance.unflat_a(flat).expect("in range"), (i, k));
                    }
                }
                for k in 0..instance.m().as_usize() {
                    for j in 0..instance.p().as_usize() {
                        let flat = instance.flat_b(k, j).expect("in range");
                        assert_eq!(instance.unflat_b(flat).expect("in range"), (k, j));
                    }
                }
                for j in 0..instance.p().as_usize() {
                    for i in 0..instance.n().as_usize() {
                        let flat = instance.flat_c_dual(j, i).expect("in range");
                        assert_eq!(instance.unflat_c_dual(flat).expect("in range"), (j, i));
                    }
                }
                assert_eq!(
                    instance.mode_len(TensorMode::A).expect("ok"),
                    usize::from(n) * usize::from(m)
                );
                assert_eq!(
                    instance.mode_len(TensorMode::B).expect("ok"),
                    usize::from(m) * usize::from(p)
                );
                assert_eq!(
                    instance.mode_len(TensorMode::C).expect("ok"),
                    usize::from(p) * usize::from(n)
                );
            }
        }
    }
}

#[test]
fn dimensions_outside_the_supported_range_reject() {
    for value in [0u16, 13, 1000] {
        assert_eq!(
            Dim::new(value).expect_err("unsupported").code(),
            ErrorCode::UnsupportedInstance
        );
    }
    assert!(MatMulInstance::from_raw(13, 2, 2).is_err());
}

#[test]
fn prime_modulus_validation_is_exact() {
    for prime in [2u32, 3, 5, 7, 11, 13, 97, 65_521, 2_147_483_647] {
        assert_eq!(
            PrimeModulus::new(prime).expect("prime").get(),
            prime,
            "{prime} is prime"
        );
    }
    for composite in [0u32, 1, 4, 9, 15, 21, 121, 65_535, 2_147_483_645] {
        let error = PrimeModulus::new(composite).expect_err("composite must reject");
        assert_eq!(error.code(), ErrorCode::CompositeModulus, "{composite}");
    }
    let error = PrimeModulus::new(0x8000_0000).expect_err("above 2^31-1");
    assert_eq!(error.code(), ErrorCode::UnsupportedInstance);
}

#[test]
fn trial_division_agrees_with_a_sieve_below_one_hundred_thousand() {
    const LIMIT: usize = 100_000;
    let mut sieve = vec![true; LIMIT];
    sieve[0] = false;
    sieve[1] = false;
    let mut candidate = 2usize;
    while candidate * candidate < LIMIT {
        if sieve[candidate] {
            let mut multiple = candidate * candidate;
            while multiple < LIMIT {
                sieve[multiple] = false;
                multiple += candidate;
            }
        }
        candidate += 1;
    }
    for (value, &expected) in sieve.iter().enumerate() {
        let actual = mm_core::modulus::is_prime_trial_division(value as u32);
        assert_eq!(actual, expected, "primality of {value}");
    }
}

/// §5.2: the tree is walked depth-first preorder, children ordered by region
/// `1..=6` outermost, then shape or split lexicographically.
#[test]
fn preorder_traversal_is_canonical_at_level_two() {
    let l = level(2);
    let paths = collect_paths(l).expect("traversal succeeds");
    assert!(paths[0].is_root());
    let shapes = Shape::enumerate(l);
    assert_eq!(paths.len(), 1 + 6 * shapes.len());

    let mut cursor = 1usize;
    for region in Region::all() {
        for shape in &shapes {
            let path = &paths[cursor];
            assert_eq!(path.steps().len(), 1);
            assert_eq!(path.region(), Some(region));
            assert_eq!(path.shape(), Some(*shape));
            cursor += 1;
        }
    }
}

#[test]
fn level_two_nodes_are_leaves_and_root_children_are_level_two() {
    let l = level(2);
    for path in collect_paths(l).expect("traversal") {
        match path.kind() {
            NodeKind::Root => assert!(path.is_root()),
            NodeKind::PositiveLevelTwo | NodeKind::ZeroShape => {
                assert_eq!(path.level().map(|value| value.get()), Some(2));
                assert!(!path.kind().has_children());
            }
            NodeKind::PositiveInterior => panic!("level 2 has no interior nodes"),
        }
    }
}

#[test]
fn level_three_tree_has_the_expected_structure() {
    let l = level(3);
    let mut roots = 0u64;
    let mut interiors = 0u64;
    let mut leaves = 0u64;
    visit_preorder(l, |cursor| {
        match cursor.kind() {
            NodeKind::Root => roots += 1,
            NodeKind::PositiveInterior => interiors += 1,
            NodeKind::PositiveLevelTwo | NodeKind::ZeroShape => leaves += 1,
        }
        Ok(Walk::Continue)
    })
    .expect("traversal");

    assert_eq!(roots, 1);
    // Positive level-3 shapes: x,y,z >= 1 with x+y+z = 8, i.e. C(7,2) = 21 shapes
    // over six regions.
    assert_eq!(interiors, 21 * 6);

    let expected_leaves: u64 = {
        let zero_level3 = (Shape::count(l) as u64 - 21) * 6;
        let positive_children: u64 = Shape::enumerate(l)
            .into_iter()
            .filter(|shape| shape.is_positive())
            .map(|shape| shape.splits().expect("splits").len() as u64 * 6)
            .sum::<u64>()
            * 6;
        zero_level3 + positive_children
    };
    assert_eq!(leaves, expected_leaves);
    assert_eq!(node_count(l).expect("count"), roots + interiors + leaves);
}

#[test]
fn traversal_can_stop_early_without_error() {
    let mut seen = 0u32;
    visit_preorder(level(3), |_| {
        seen += 1;
        if seen == 10 {
            Ok(Walk::Stop)
        } else {
            Ok(Walk::Continue)
        }
    })
    .expect("early stop is not an error");
    assert_eq!(seen, 10);
}

#[test]
fn node_paths_distinguish_identical_level_shape_region() {
    // Two distinct level-2 nodes may share level, shape, and region while having
    // different ancestors. They are genuinely distinct nodes with independent
    // free variables, so their paths must differ (§5.2).
    use std::collections::BTreeMap;
    let l3 = level(3);
    let mut groups: BTreeMap<(String, u8), Vec<String>> = BTreeMap::new();
    for path in collect_paths(l3).expect("traversal") {
        if path.steps().len() != 2 {
            continue;
        }
        let shape = path.shape().expect("non-root");
        let region = path.region().expect("non-root");
        groups
            .entry((format!("{shape}"), region.get()))
            .or_default()
            .push(path.render());
    }
    let colliding: usize = groups.values().filter(|paths| paths.len() > 1).count();
    assert!(
        colliding > 0,
        "the fixture must exercise a real level/shape/region collision"
    );
    for paths in groups.values() {
        let mut unique = paths.clone();
        unique.sort();
        unique.dedup();
        assert_eq!(
            unique.len(),
            paths.len(),
            "distinct nodes must have distinct rendered paths"
        );
    }
}

#[test]
fn node_path_validation_rejects_inconsistent_data() {
    let l3 = level(3);
    let root_shape = Shape::new(l3, 2, 3, 3).expect("valid");
    let region = Region::IDENTITY;
    let path = mm_core::path::NodePath::root()
        .child(l3, root_shape, region)
        .expect("root child");
    // A split that exceeds the parent in X must reject.
    let bad_split = Shape::new(level(2), 3, 1, 0).expect("valid level-2 shape");
    assert_eq!(
        path.child(l3, bad_split, region)
            .expect_err("split exceeds parent")
            .code(),
        ErrorCode::BadPath
    );
    // A child of a level-2 leaf must reject.
    let leaf_split = Shape::new(level(2), 1, 2, 1).expect("valid");
    let leaf = path.child(l3, leaf_split, region).expect("valid child");
    assert_eq!(
        leaf.child(l3, leaf_split, region)
            .expect_err("leaf has no children")
            .code(),
        ErrorCode::BadPath
    );
    // A root step at the wrong level must reject.
    assert_eq!(
        mm_core::path::NodePath::root()
            .child(l3, leaf_split, region)
            .expect_err("root step must be level 3")
            .code(),
        ErrorCode::BadPath
    );
}
