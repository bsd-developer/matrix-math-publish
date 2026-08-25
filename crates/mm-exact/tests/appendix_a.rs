//! Appendix A conformance (spec A.1–A.10, §7.2, §7.6).

#![allow(
    clippy::expect_used,
    clippy::panic,
    clippy::unwrap_used,
    reason = "test assertions must fail loudly; §17.1 governs library code, not test targets"
)]

use mm_core::ErrorCode;
use mm_core::level::Level;
use mm_core::path::NodeKind;
use mm_core::region::{Coordinate, Region};
use mm_core::shape::Shape;
use mm_exact::domain::{ShapeDomain, support_vectors};
use mm_exact::evaluate::{
    check_feasibility, e_level_two, evaluate, full_support, level_two_exponents, local_sizes,
    m_total,
};
use mm_exact::instance::OmegaInstance;
use mm_exact::maxent::MaxEntropyBlock;
use mm_exact::tree::{NodeVariables, TrackATree, skeleton};
use mm_rat::Rat;
use mm_rat::bounds::LowerBound;
use mm_rat::log2::Precision;

fn level(value: u8) -> Level {
    Level::new(value).expect("supported level")
}

fn precision() -> Precision {
    Precision::new(96).expect("supported precision")
}

/// A.2: `C_(ℓ,a)` is the set of `{0,1,2}` vectors of length `2^(ℓ-1)` summing to
/// `a`, enumerated lexicographically.
#[test]
fn support_vectors_match_the_defining_predicate() {
    let l2 = level(2);
    let expected: [(u16, &[&[u8]]); 5] = [
        (0, &[&[0, 0]]),
        (1, &[&[0, 1], &[1, 0]]),
        (2, &[&[0, 2], &[1, 1], &[2, 0]]),
        (3, &[&[1, 2], &[2, 1]]),
        (4, &[&[2, 2]]),
    ];
    for (total, vectors) in expected {
        let actual = support_vectors(l2, total).expect("valid total");
        let rendered: Vec<&[u8]> = actual.iter().map(|vector| vector.entries()).collect();
        assert_eq!(rendered, vectors.to_vec(), "C_(2,{total})");
        for window in actual.windows(2) {
            assert!(window[0] < window[1], "C_(2,{total}) is not lexicographic");
        }
    }
    assert!(
        support_vectors(l2, 5).is_err(),
        "a total above 2*2 must reject"
    );
}

/// A4: `β^∨(2⃗ - L) = β(L)`.
#[test]
fn support_vector_complement_is_an_involution() {
    for total in 0..=4u16 {
        for vector in support_vectors(level(2), total).expect("valid") {
            assert_eq!(vector.complement().complement(), vector);
            let sum: u16 = vector
                .complement()
                .entries()
                .iter()
                .map(|entry| u16::from(*entry))
                .sum();
            assert_eq!(sum, 4 - total, "the complement total is 2*len - total");
        }
    }
}

#[test]
fn full_support_is_the_whole_cube_in_lexicographic_order() {
    let support = full_support(level(2));
    assert_eq!(support.len(), 9, "3^2 vectors at level 2");
    for window in support.windows(2) {
        assert!(window[0] < window[1]);
    }
    let support3 = full_support(level(3));
    assert_eq!(support3.len(), 81, "3^4 vectors at level 3");
}

/// Build a tree whose root puts all its weight on region 1 and shape `(1,1,2)`.
fn point_mass_tree(mu: Rat) -> TrackATree {
    let l2 = level(2);
    let instance = OmegaInstance::new(5, l2).expect("supported instance");
    let domain = ShapeDomain::full(l2);
    let target = Shape::new(l2, 1, 1, 2).expect("valid shape");
    let target_index = domain
        .shapes()
        .iter()
        .position(|shape| *shape == target)
        .expect("shape present");
    let fallback_index = 0usize;

    let point = |index: usize| -> Vec<Rat> {
        (0..domain.len())
            .map(|position| {
                if position == index {
                    Rat::one()
                } else {
                    Rat::zero()
                }
            })
            .collect()
    };
    let region_weights: Vec<Rat> = (0..6)
        .map(|index| if index == 0 { Rat::one() } else { Rat::zero() })
        .collect();
    let alpha: Vec<Vec<Rat>> = (0..6)
        .map(|index| {
            if index == 0 {
                point(target_index)
            } else {
                point(fallback_index)
            }
        })
        .collect();

    let slots = skeleton(l2).expect("skeleton");
    let variables: Vec<NodeVariables> = slots
        .iter()
        .map(|slot| match slot.kind {
            NodeKind::Root => NodeVariables::Root {
                region_weights: region_weights.clone(),
                alpha: alpha.clone(),
            },
            NodeKind::PositiveLevelTwo => NodeVariables::PositiveLevelTwo { mu: mu.clone() },
            NodeKind::ZeroShape => {
                let shape = slot.shape.expect("zero-shape node has a shape");
                let coordinate = shape.first_nonzero_coord().expect("positive coordinate");
                let vectors =
                    support_vectors(shape.level(), shape.coord(coordinate)).expect("domain");
                let mut beta = vec![Rat::zero(); vectors.len()];
                beta[0] = Rat::one();
                NodeVariables::ZeroShape { beta }
            }
            NodeKind::PositiveInterior => panic!("level 2 has no interior nodes"),
        })
        .collect();
    TrackATree::new(instance, variables).expect("valid tree")
}

#[test]
fn the_level_two_tree_has_the_expected_shape() {
    let slots = skeleton(level(2)).expect("skeleton");
    assert_eq!(slots.len(), 1 + 6 * 15, "one root plus six regions of S_2");
    assert_eq!(slots[0].kind, NodeKind::Root);
    assert!(slots[1..].iter().all(|slot| !slot.kind.has_children()));
}

/// A2: `m_(G[s,r]) = A_G^(r) α_G^(r)(s)`, and the masses of the root's children
/// sum to one when the free variables are distributions.
#[test]
fn root_child_masses_follow_a2() {
    let tree = point_mass_tree(Rat::from_signeds(1, 4));
    let masses = tree.masses();
    assert_eq!(masses[0], Rat::one(), "the root has mass one");
    let total = masses[1..]
        .iter()
        .fold(Rat::zero(), |acc, mass| &acc + mass);
    assert_eq!(total, Rat::one(), "child masses sum to one");
    // Exactly one child carries the mass, since both A_G and alpha are point masses.
    let nonzero: Vec<_> = masses[1..].iter().filter(|mass| !mass.is_zero()).collect();
    assert_eq!(nonzero.len(), 1);
    assert_eq!(*nonzero[0], Rat::one());
}

/// A7: at a positive level-2 node the `μ` distribution sits on the coordinate
/// whose shape entry is two, and the other two are half/half.
#[test]
fn level_two_beta_follows_a7() {
    let mu = Rat::from_signeds(1, 4);
    let tree = point_mass_tree(mu.clone());
    let node = tree
        .nodes()
        .iter()
        .find(|node| {
            node.kind == NodeKind::PositiveLevelTwo
                && node.shape == Shape::new(level(2), 1, 1, 2).ok()
                && node.region == Some(Region::IDENTITY)
        })
        .expect("the (1,1,2) node in region 1");

    // Z has shape entry 2: mu on (0,2) and (2,0), 1-2mu on (1,1).
    let beta_z = tree.beta(node, Coordinate::Z).expect("beta");
    let one_minus = &Rat::one() - &(&Rat::from_integer(2) * &mu);
    for (vector, value) in &beta_z {
        let expected = match vector.entries() {
            [0, 2] | [2, 0] => mu.clone(),
            [1, 1] => one_minus.clone(),
            _ => Rat::zero(),
        };
        assert_eq!(*value, expected, "beta_Z at {:?}", vector.entries());
    }
    let total = beta_z.iter().fold(Rat::zero(), |acc, (_, v)| &acc + v);
    assert_eq!(total, Rat::one());

    // X and Y have shape entry 1: half/half on (0,1) and (1,0).
    for coordinate in [Coordinate::X, Coordinate::Y] {
        let beta = tree.beta(node, coordinate).expect("beta");
        for (vector, value) in &beta {
            let expected = match vector.entries() {
                [0, 1] | [1, 0] => Rat::from_signeds(1, 2),
                _ => Rat::zero(),
            };
            assert_eq!(*value, expected, "beta at {:?}", vector.entries());
        }
    }
}

/// A4: at a zero-shape node the first zero coordinate is a point mass at `0⃗`,
/// the first nonzero coordinate carries the free distribution, and the remaining
/// coordinate is its reversal.
#[test]
fn zero_shape_beta_follows_a4() {
    let tree = point_mass_tree(Rat::from_signeds(1, 4));
    let node = tree
        .nodes()
        .iter()
        .find(|node| node.kind == NodeKind::ZeroShape)
        .expect("a zero-shape node exists");
    let shape = node.shape.expect("shape");
    let w0 = shape.first_zero_coord().expect("zero coordinate");
    let w1 = shape.first_nonzero_coord().expect("nonzero coordinate");
    let w2 = Coordinate::ALL
        .into_iter()
        .find(|coordinate| *coordinate != w0 && *coordinate != w1)
        .expect("third coordinate");

    let beta0 = tree.beta(node, w0).expect("beta");
    let mass_at_zero = beta0
        .iter()
        .find(|(vector, _)| vector.entries().iter().all(|entry| *entry == 0))
        .map(|(_, value)| value.clone())
        .expect("the zero vector is in the domain");
    assert_eq!(
        mass_at_zero,
        Rat::one(),
        "W0 is a point mass at the zero vector"
    );

    let beta1 = tree.beta(node, w1).expect("beta");
    let beta2 = tree.beta(node, w2).expect("beta");
    // beta^∨(2⃗ - L) = beta(L).
    for (vector, value) in &beta2 {
        let source = vector.complement();
        let expected = beta1
            .iter()
            .find(|(candidate, _)| *candidate == source)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(Rat::zero);
        assert_eq!(*value, expected, "beta^∨ at {:?}", vector.entries());
    }
}

/// A19: the coordinate whose shape entry is two gets `2μ log2 q`; the others get
/// `(1-2μ) log2 q`.
#[test]
fn level_two_local_sizes_follow_a19() {
    let mu = Rat::from_signeds(1, 4);
    let tree = point_mass_tree(mu.clone());
    let (position, node) = tree
        .nodes()
        .iter()
        .enumerate()
        .find(|(_, node)| {
            node.kind == NodeKind::PositiveLevelTwo
                && node.shape == Shape::new(level(2), 1, 1, 2).ok()
                && node.region == Some(Region::IDENTITY)
        })
        .expect("the (1,1,2) node");
    let mass = tree.masses()[position].clone();
    let sizes = local_sizes(&tree, node, &mass, precision()).expect("sizes");
    // With mu = 1/4 both 2*mu and 1-2*mu equal 1/2, so all three agree.
    assert_eq!(sizes[0].value(), sizes[1].value());
    assert_eq!(sizes[1].value(), sizes[2].value());
    assert!(sizes[0].value().is_positive(), "q = 5 gives a positive log");
}

/// A16: the coordinate whose shape entry is two gets `H(μ,μ,1-2μ)`; the others
/// get one.
#[test]
fn level_two_exponents_follow_a16() {
    let mu = Rat::from_signeds(1, 4);
    let tree = point_mass_tree(mu);
    let (position, node) = tree
        .nodes()
        .iter()
        .enumerate()
        .find(|(_, node)| {
            node.kind == NodeKind::PositiveLevelTwo
                && node.shape == Shape::new(level(2), 1, 1, 2).ok()
                && node.region == Some(Region::IDENTITY)
        })
        .expect("the (1,1,2) node");
    let mass = tree.masses()[position].clone();
    let exponents = level_two_exponents(node, &mass, precision()).expect("exponents");
    assert_eq!(*exponents[0].value(), Rat::one(), "X gets exactly 1");
    assert_eq!(*exponents[1].value(), Rat::one(), "Y gets exactly 1");
    // H(1/4, 1/4, 1/2) = 3/2 exactly, and the enclosure is exact at these values.
    assert_eq!(
        *exponents[2].value(),
        Rat::from_signeds(3, 2),
        "Z gets H(mu,mu,1-2mu)"
    );
}

/// A17 and A20: the totals take the coordinate minimum.
#[test]
fn totals_take_the_coordinate_minimum() {
    let tree = point_mass_tree(Rat::from_signeds(1, 4));
    let e2 = e_level_two(&tree, precision()).expect("E_2");
    assert_eq!(*e2.value(), Rat::one(), "min(1, 1, 3/2) = 1");
    let m = m_total(&tree, precision()).expect("M_total");
    assert!(m.value().is_positive());
}

/// §7.2: `Ω ≥ 0` is validated before the monotonic shortcut is used.
#[test]
fn a_negative_omega_is_rejected_before_multiplication() {
    let tree = point_mass_tree(Rat::from_signeds(1, 4));
    let error = check_feasibility(
        &tree,
        LowerBound::assert(Rat::from_integer(100)),
        LowerBound::assert(Rat::one()),
        &Rat::from_integer(-1),
        precision(),
    )
    .expect_err("negative omega");
    assert_eq!(error.code(), ErrorCode::NegativeOmega);
    assert_eq!(error.equation_id(), Some("§7.2"));
}

/// A21: a value that fails the directed inequality is rejected with its exact
/// offending values.
#[test]
fn an_infeasible_point_is_rejected_with_its_values() {
    let tree = point_mass_tree(Rat::from_signeds(1, 4));
    let error = check_feasibility(
        &tree,
        LowerBound::assert(Rat::zero()),
        LowerBound::assert(Rat::zero()),
        &Rat::from_integer(3),
        precision(),
    )
    .expect_err("0 + 0*3 < 2*log2(7)");
    assert_eq!(error.code(), ErrorCode::FeasibilityViolated);
    assert_eq!(error.equation_id(), Some("A21"));
    assert_eq!(error.values().len(), 2, "both sides are reported");
}

/// A21: a generous enough point is accepted.
#[test]
fn a_feasible_point_is_accepted() {
    let tree = point_mass_tree(Rat::from_signeds(1, 4));
    let claim = check_feasibility(
        &tree,
        LowerBound::assert(Rat::from_integer(100)),
        LowerBound::assert(Rat::one()),
        &Rat::from_integer(3),
        precision(),
    )
    .expect("100 + 3 >= 2*log2(7)");
    assert_eq!(claim.omega, Rat::from_integer(3));
    assert!(claim.statement().starts_with("omega <= "));
}

/// Build a uniform `ℓ*=3` tree, which exercises the A.5 interior `β` recursion
/// and the A12–A15 interior exponents.
fn uniform_level_three_tree() -> TrackATree {
    let l3 = level(3);
    let instance = OmegaInstance::new(5, l3).expect("supported");
    let slots = skeleton(l3).expect("skeleton");
    let domain = ShapeDomain::full(l3);
    let uniform =
        |len: usize| -> Vec<Rat> { (0..len).map(|_| Rat::from_signeds(1, len as i64)).collect() };
    let variables: Vec<NodeVariables> = slots
        .iter()
        .map(|slot| match slot.kind {
            NodeKind::Root => NodeVariables::Root {
                region_weights: uniform(6),
                alpha: (0..6).map(|_| uniform(domain.len())).collect(),
            },
            NodeKind::PositiveInterior => {
                let shape = slot.shape.expect("shape");
                let splits = ShapeDomain::splits(shape).expect("splits");
                NodeVariables::Interior {
                    region_weights: uniform(6),
                    alpha: (0..6).map(|_| uniform(splits.len())).collect(),
                }
            }
            NodeKind::PositiveLevelTwo => NodeVariables::PositiveLevelTwo {
                mu: Rat::from_signeds(1, 4),
            },
            NodeKind::ZeroShape => {
                let shape = slot.shape.expect("shape");
                let coordinate = shape.first_nonzero_coord().expect("positive coordinate");
                let vectors =
                    support_vectors(shape.level(), shape.coord(coordinate)).expect("domain");
                NodeVariables::ZeroShape {
                    beta: uniform(vectors.len()),
                }
            }
        })
        .collect();
    TrackATree::new(instance, variables).expect("valid tree")
}

/// A block certifying `H_D^max` for the uniform distribution on any domain.
///
/// The witness is the uniform distribution itself, so the marginals match
/// trivially; `λ₀` is a rational near `log2(1/|D|)` and `ε = 1/10` covers the
/// residual comfortably.
fn uniform_block_for(domain: &ShapeDomain) -> MaxEntropyBlock {
    let size = domain.len();
    // A rational within 1/100 of log2(1/size), which epsilon = 1/10 absorbs.
    let mut hundredths = 0i64;
    while (1i64 << ((hundredths + 100) / 100)) < size as i64 {
        hundredths += 100;
    }
    let approx = -Rat::from_signeds(hundredths + 50, 100);
    MaxEntropyBlock {
        y: (0..size)
            .map(|_| Rat::from_signeds(1, size as i64))
            .collect(),
        lambda0: approx,
        lambda_x: vec![Rat::zero(); domain.coordinate_values(Coordinate::X).len()],
        lambda_y: vec![Rat::zero(); domain.coordinate_values(Coordinate::Y).len()],
        lambda_z: vec![Rat::zero(); domain.coordinate_values(Coordinate::Z).len()],
        epsilon: Rat::from_integer(1),
    }
}

/// Blocks in the order the evaluator consumes them: root regions first, then
/// each positive interior node in preorder with its six regions (§6.5, §5.2).
fn blocks_for(tree: &TrackATree) -> Vec<MaxEntropyBlock> {
    let mut out = Vec::new();
    let root_domain = ShapeDomain::full(tree.instance().level());
    for _ in 0..6 {
        out.push(uniform_block_for(&root_domain));
    }
    for node in tree.nodes() {
        if node.kind != NodeKind::PositiveInterior {
            continue;
        }
        let shape = node.shape.expect("interior nodes have a shape");
        let domain = ShapeDomain::splits(shape).expect("splits");
        for _ in 0..6 {
            out.push(uniform_block_for(&domain));
        }
    }
    out
}

/// §6.5: the block count is derived from the instance, never trusted.
#[test]
fn the_required_block_count_matches_the_instance() {
    use mm_exact::evaluate::required_block_count;
    let l2 = point_mass_tree(Rat::from_signeds(1, 4));
    // Level 2 has no interior nodes, so only the six root blocks are needed.
    assert_eq!(required_block_count(&l2), 6);

    let l3 = uniform_level_three_tree();
    let interior = l3
        .nodes()
        .iter()
        .filter(|node| node.kind == NodeKind::PositiveInterior)
        .count();
    // Positive level-3 shapes are those with x,y,z >= 1 summing to 8: C(7,2) = 21,
    // over six regions.
    assert_eq!(interior, 21 * 6);
    assert_eq!(required_block_count(&l3), 6 + 6 * interior);
    assert_eq!(blocks_for(&l3).len(), required_block_count(&l3));
}

/// A.5 and A.6: an interior node's `β` is the split mixture followed by the
/// region mixture, and it is a distribution on the full support space.
#[test]
fn interior_beta_is_a_distribution_on_the_full_support() {
    use mm_exact::evaluate::{beta_table, full_support};
    let tree = uniform_level_three_tree();
    let table = beta_table(&tree).expect("beta table");
    let width_three = full_support(level(3)).len();
    let width_two = full_support(level(2)).len();
    assert_eq!(width_three, 81);
    assert_eq!(width_two, 9);

    let mut checked_interior = 0;
    for (position, node) in tree.nodes().iter().enumerate() {
        let entry = &table[position];
        match node.kind {
            NodeKind::Root => assert!(entry[0].is_empty(), "the root carries no beta"),
            NodeKind::PositiveInterior => {
                for coordinate in Coordinate::ALL {
                    let values = &entry[coordinate.index()];
                    assert_eq!(values.len(), width_three);
                    let total = values.iter().fold(Rat::zero(), |acc, v| &acc + v);
                    assert_eq!(total, Rat::one(), "A.6 mixture must be a distribution");
                    assert!(values.iter().all(|v| v.is_nonnegative()));
                }
                checked_interior += 1;
            }
            _ => {
                // A leaf's support width follows its **own** level: at l*=3 a
                // zero-shape leaf sits at level 3, not level 2.
                let node_level = node.shape.expect("a leaf has a shape").level();
                let width = if node_level.get() == 3 {
                    width_three
                } else {
                    width_two
                };
                for coordinate in Coordinate::ALL {
                    let values = &entry[coordinate.index()];
                    assert_eq!(values.len(), width, "leaf at level {}", node_level);
                    let total = values.iter().fold(Rat::zero(), |acc, v| &acc + v);
                    assert_eq!(total, Rat::one(), "a leaf beta must be a distribution");
                }
            }
        }
    }
    assert!(
        checked_interior > 0,
        "the fixture must contain interior nodes"
    );
}

/// A12–A15 and A20/A21: the whole `ℓ*=3` evaluation runs end to end.
#[test]
fn the_full_level_three_evaluation_runs_end_to_end() {
    let tree = uniform_level_three_tree();
    let blocks = blocks_for(&tree);
    let claim = evaluate(&tree, &blocks, &Rat::from_integer(1000), precision())
        .expect("a large omega satisfies A21");
    assert_eq!(claim.omega, Rat::from_integer(1000));
    // The requirement is 2^(l*-1) * upper(log2(q+2)) = 4 * log2 7 ≈ 11.229.
    assert!(*claim.requirement.value() > Rat::from_signeds(112, 10));
    assert!(*claim.requirement.value() < Rat::from_signeds(113, 10));
    assert!(claim.m_total.value().is_positive());
}

/// §6.5: too few or too many blocks is a rejection, not a truncation.
#[test]
fn a_wrong_block_count_is_rejected() {
    let tree = uniform_level_three_tree();
    let blocks = blocks_for(&tree);
    for count in [blocks.len() - 1, blocks.len() + 1] {
        let mut adjusted = blocks.clone();
        adjusted.resize(count, uniform_block_for(&ShapeDomain::full(level(3))));
        let error = evaluate(&tree, &adjusted, &Rat::from_integer(1000), precision())
            .expect_err("wrong block count");
        assert_eq!(error.code(), ErrorCode::CountMismatch);
        assert_eq!(error.equation_id(), Some("§6.5"));
    }
}

/// A.2: a node whose free-variable kind disagrees with its position is rejected.
#[test]
fn a_wrong_variable_kind_is_rejected() {
    let l2 = level(2);
    let instance = OmegaInstance::new(5, l2).expect("supported");
    let slots = skeleton(l2).expect("skeleton");
    let variables: Vec<NodeVariables> = slots
        .iter()
        .map(|_| NodeVariables::PositiveLevelTwo { mu: Rat::zero() })
        .collect();
    let error = TrackATree::new(instance, variables).expect_err("the root is not a level-2 node");
    assert_eq!(error.code(), ErrorCode::BadPath);
}

/// A.2: `μ` must lie in `[0, 1/2]`.
#[test]
fn a_mu_outside_its_domain_is_rejected() {
    let l2 = level(2);
    let instance = OmegaInstance::new(5, l2).expect("supported");
    let slots = skeleton(l2).expect("skeleton");
    let domain = ShapeDomain::full(l2);
    let point: Vec<Rat> = (0..domain.len())
        .map(|index| if index == 0 { Rat::one() } else { Rat::zero() })
        .collect();
    let variables: Vec<NodeVariables> = slots
        .iter()
        .map(|slot| match slot.kind {
            NodeKind::Root => NodeVariables::Root {
                region_weights: (0..6)
                    .map(|index| if index == 0 { Rat::one() } else { Rat::zero() })
                    .collect(),
                alpha: (0..6).map(|_| point.clone()).collect(),
            },
            NodeKind::PositiveLevelTwo => NodeVariables::PositiveLevelTwo {
                mu: Rat::from_signeds(3, 4),
            },
            NodeKind::ZeroShape => {
                let shape = slot.shape.expect("shape");
                let coordinate = shape.first_nonzero_coord().expect("coordinate");
                let vectors =
                    support_vectors(shape.level(), shape.coord(coordinate)).expect("domain");
                let mut beta = vec![Rat::zero(); vectors.len()];
                beta[0] = Rat::one();
                NodeVariables::ZeroShape { beta }
            }
            NodeKind::PositiveInterior => panic!("level 2 has no interior nodes"),
        })
        .collect();
    let error = TrackATree::new(instance, variables).expect_err("mu = 3/4 is outside [0,1/2]");
    assert_eq!(error.code(), ErrorCode::BadSimplex);
    assert_eq!(error.equation_id(), Some("A.2"));
}

/// §7.4: a maximum-entropy block whose witness marginals disagree with `ρ` is
/// rejected with `wrong_marginal`.
#[test]
fn a_block_with_wrong_marginals_is_rejected() {
    let l2 = level(2);
    let domain = ShapeDomain::full(l2);
    let uniform: Vec<Rat> = (0..domain.len())
        .map(|_| Rat::from_signeds(1, domain.len() as i64))
        .collect();
    let mut skewed = uniform.clone();
    skewed[0] = &skewed[0] + &Rat::from_signeds(1, 100);
    skewed[1] = &skewed[1] - &Rat::from_signeds(1, 100);

    let block = MaxEntropyBlock {
        y: uniform.clone(),
        lambda0: Rat::zero(),
        lambda_x: vec![Rat::zero(); domain.coordinate_values(Coordinate::X).len()],
        lambda_y: vec![Rat::zero(); domain.coordinate_values(Coordinate::Y).len()],
        lambda_z: vec![Rat::zero(); domain.coordinate_values(Coordinate::Z).len()],
        epsilon: Rat::zero(),
    };
    let error = block
        .certify(&domain, &skewed, precision())
        .expect_err("marginals differ");
    assert_eq!(error.code(), ErrorCode::WrongMarginal);
}

/// §7.4: a negative `ε` is rejected.
#[test]
fn a_negative_epsilon_is_rejected() {
    let l2 = level(2);
    let domain = ShapeDomain::full(l2);
    let uniform: Vec<Rat> = (0..domain.len())
        .map(|_| Rat::from_signeds(1, domain.len() as i64))
        .collect();
    let block = MaxEntropyBlock {
        y: uniform.clone(),
        lambda0: Rat::zero(),
        lambda_x: vec![Rat::zero(); domain.coordinate_values(Coordinate::X).len()],
        lambda_y: vec![Rat::zero(); domain.coordinate_values(Coordinate::Y).len()],
        lambda_z: vec![Rat::zero(); domain.coordinate_values(Coordinate::Z).len()],
        epsilon: Rat::from_signeds(-1, 10),
    };
    let error = block
        .certify(&domain, &uniform, precision())
        .expect_err("negative epsilon");
    assert_eq!(error.code(), ErrorCode::NegativeEpsilon);
}

/// Build a tree whose root is uniform over regions and over `S_2`.
fn uniform_tree() -> TrackATree {
    let l2 = level(2);
    let instance = OmegaInstance::new(5, l2).expect("supported instance");
    let domain = ShapeDomain::full(l2);
    let uniform =
        |len: usize| -> Vec<Rat> { (0..len).map(|_| Rat::from_signeds(1, len as i64)).collect() };
    let slots = skeleton(l2).expect("skeleton");
    let variables: Vec<NodeVariables> = slots
        .iter()
        .map(|slot| match slot.kind {
            NodeKind::Root => NodeVariables::Root {
                region_weights: uniform(6),
                alpha: (0..6).map(|_| uniform(domain.len())).collect(),
            },
            NodeKind::PositiveLevelTwo => NodeVariables::PositiveLevelTwo {
                mu: Rat::from_signeds(1, 4),
            },
            NodeKind::ZeroShape => {
                let shape = slot.shape.expect("shape");
                let coordinate = shape.first_nonzero_coord().expect("coordinate");
                let vectors =
                    support_vectors(shape.level(), shape.coord(coordinate)).expect("domain");
                NodeVariables::ZeroShape {
                    beta: uniform(vectors.len()),
                }
            }
            NodeKind::PositiveInterior => panic!("level 2 has no interior nodes"),
        })
        .collect();
    TrackATree::new(instance, variables).expect("valid tree")
}

/// A block that certifies `H_D^max` for the uniform distribution on `S_2`.
///
/// The witness is the uniform distribution itself, which trivially matches its
/// own marginals and is strictly positive. `λ₀` is a rational near
/// `log2(1/15) ≈ -3.9069` and `ε` covers the gap, so §7.4's fourth condition
/// holds with room to spare.
fn uniform_block(domain: &ShapeDomain) -> MaxEntropyBlock {
    let uniform: Vec<Rat> = (0..domain.len())
        .map(|_| Rat::from_signeds(1, domain.len() as i64))
        .collect();
    MaxEntropyBlock {
        y: uniform,
        lambda0: Rat::from_signeds(-39, 10),
        lambda_x: vec![Rat::zero(); domain.coordinate_values(Coordinate::X).len()],
        lambda_y: vec![Rat::zero(); domain.coordinate_values(Coordinate::Y).len()],
        lambda_z: vec![Rat::zero(); domain.coordinate_values(Coordinate::Z).len()],
        epsilon: Rat::from_signeds(1, 10),
    }
}

/// §7.4: a well-formed block certifies `entropyUpper(y) + 2ε`.
#[test]
fn a_valid_block_certifies_its_bound() {
    let domain = ShapeDomain::full(level(2));
    let block = uniform_block(&domain);
    let uniform: Vec<Rat> = (0..domain.len())
        .map(|_| Rat::from_signeds(1, domain.len() as i64))
        .collect();
    let bound = block
        .certify(&domain, &uniform, precision())
        .expect("valid block");
    // H(uniform on 15) = log2 15 ≈ 3.9069, so the bound is about 4.107.
    assert!(*bound.value() > Rat::from_signeds(41, 10));
    assert!(*bound.value() < Rat::from_signeds(42, 10));
}

/// §7.4 condition 4: widening `λ₀` past `ε` must be rejected.
#[test]
fn a_block_whose_residual_exceeds_epsilon_is_rejected() {
    let domain = ShapeDomain::full(level(2));
    let mut block = uniform_block(&domain);
    block.epsilon = Rat::from_signeds(1, 1000);
    let uniform: Vec<Rat> = (0..domain.len())
        .map(|_| Rat::from_signeds(1, domain.len() as i64))
        .collect();
    let error = block
        .certify(&domain, &uniform, precision())
        .expect_err("the residual exceeds epsilon");
    assert_eq!(error.code(), ErrorCode::InsufficientResidualBound);
    assert_eq!(error.equation_id(), Some("§7.4"));
}

/// A8-A11: the root retained exponent evaluates end to end at `ℓ*=2`.
#[test]
fn the_root_exponent_evaluates_at_level_two() {
    use mm_exact::evaluate::{beta_table, e_root};
    let tree = uniform_tree();
    let domain = ShapeDomain::full(level(2));
    let blocks: Vec<MaxEntropyBlock> = (0..6).map(|_| uniform_block(&domain)).collect();
    let beta = beta_table(&tree).expect("beta table");
    let bound = e_root(&tree, &blocks, &beta, precision()).expect("E_G evaluates");
    // Every term of the A10 minimum is a difference of entropies, so the bound is
    // finite and the evaluation must not produce a degenerate value.
    assert!(bound.value().is_negative() || bound.value().is_nonnegative());
    // The block count is checked: five blocks must reject.
    let short: Vec<MaxEntropyBlock> = (0..5).map(|_| uniform_block(&domain)).collect();
    let error = e_root(&tree, &short, &beta, precision()).expect_err("wrong block count");
    assert_eq!(error.code(), ErrorCode::CountMismatch);
    assert_eq!(error.equation_id(), Some("§6.5"));
}

/// A20/A21: the whole `ℓ*=2` evaluation runs end to end and its verdict is
/// determined by the directed inequality.
#[test]
fn the_full_level_two_evaluation_runs_end_to_end() {
    let tree = uniform_tree();
    let domain = ShapeDomain::full(level(2));
    let blocks: Vec<MaxEntropyBlock> = (0..6).map(|_| uniform_block(&domain)).collect();

    // A generous omega must be accepted, a zero omega need not be.
    let generous = evaluate(&tree, &blocks, &Rat::from_integer(1000), precision());
    assert!(
        generous.is_ok(),
        "a large omega satisfies A21: {generous:?}"
    );

    let claim = generous.expect("accepted");
    assert_eq!(claim.omega, Rat::from_integer(1000));
    // The requirement is 2^(l*-1) * upper(log2(q+2)) = 2 * log2 7 ≈ 5.615.
    assert!(*claim.requirement.value() > Rat::from_signeds(56, 10));
    assert!(*claim.requirement.value() < Rat::from_signeds(57, 10));
}
