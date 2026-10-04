//! The Appendix A tree, free variables, masses, and split distributions.
//!
//! Normative source: `docs/specs/0001_spec.md` A.1–A.9.
//!
//! Every function here names the equation it implements, as §17.8 requires. The
//! node ordering is the canonical depth-first preorder of §5.2, which is what a
//! certificate's dense arrays are indexed by.
//!
//! Scope: the tree, free variables, masses, complete split distributions, and
//! local matrix sizes are implemented for every supported `ℓ*`. The retained
//! exponents are implemented for the root (A.6) and for level 2 (A.8); the
//! interior recursion of A.7 is not yet implemented and is rejected rather than
//! approximated, so an `ℓ* ≥ 3` instance returns a structured
//! `unsupported_instance` instead of a wrong number.

use crate::domain::{ShapeDomain, SupportVector, support_vectors};
use crate::instance::OmegaInstance;
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::level::Level;
use mm_core::path::{NodeKind, Walk, visit_preorder};
use mm_core::region::{Coordinate, Region};
use mm_core::shape::Shape;
use mm_rat::Rat;

extern crate alloc;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::vec::Vec;

/// The free variables one node carries (A.2).
#[derive(Clone, Debug)]
pub enum NodeVariables {
    /// The root `G`: `A_G ∈ Δ([6])` and `α_G^(r) ∈ Δ(S_ℓ*)` for each region.
    Root {
        /// `A_G`, indexed by region `1..=6`.
        region_weights: Vec<Rat>,
        /// `α_G^(r)`, one distribution over `S_ℓ*` per region.
        alpha: Vec<Vec<Rat>>,
    },
    /// A positive node of level at least 3: `A_T` and `α_T^(r) ∈ Δ(Split(s_T))`.
    Interior {
        /// `A_T`, indexed by region `1..=6`.
        region_weights: Vec<Rat>,
        /// `α_T^(r)`, one distribution over `Split(s_T)` per region.
        alpha: Vec<Vec<Rat>>,
    },
    /// A zero-shape node: the free `β_(T,W1)` on `C_(ℓ, s_(T,W1))`.
    ZeroShape {
        /// The free distribution, in canonical support-vector order.
        beta: Vec<Rat>,
    },
    /// A positive level-2 node: `μ_T ∈ [0, 1/2]`.
    PositiveLevelTwo {
        /// The single free parameter.
        mu: Rat,
    },
}

/// One node of the instance tree, with its identity and free variables.
#[derive(Clone, Debug)]
pub struct TreeNode {
    /// Depth-first preorder index (§5.2).
    pub index: u64,
    /// Rendered `NodePath`, for diagnostics (§5.4).
    pub path: alloc::string::String,
    /// The node's shape, or `None` at the root.
    pub shape: Option<Shape>,
    /// The node's region, or `None` at the root.
    pub region: Option<Region>,
    /// The node's kind.
    pub kind: NodeKind,
    /// The parent's preorder index, or `None` at the root.
    pub parent: Option<u64>,
    /// The free variables the certificate supplies for this node.
    pub variables: NodeVariables,
}

/// The complete instance tree with its decoded free variables.
#[derive(Clone, Debug)]
pub struct TrackATree {
    instance: OmegaInstance,
    nodes: Vec<TreeNode>,
    masses: Vec<Rat>,
    /// Child positions of each node, in preorder. Built once, because finding a
    /// child by scanning every node made A.5's recursion O(N^2): at `ℓ*=4` the
    /// scan ran 258,570 times over 1,552,339 nodes.
    children: Vec<Vec<u32>>,
}

/// The skeleton of one node, before free variables are attached.
#[derive(Clone, Debug)]
pub struct NodeSlot {
    /// Preorder index.
    pub index: u64,
    /// Rendered path.
    pub path: alloc::string::String,
    /// The node's shape.
    pub shape: Option<Shape>,
    /// The node's region.
    pub region: Option<Region>,
    /// The node's kind.
    pub kind: NodeKind,
    /// Parent index.
    pub parent: Option<u64>,
}

/// Enumerate the tree skeleton in canonical preorder (§5.2, A.1).
///
/// # Errors
///
/// Propagates split-enumeration failures.
pub fn skeleton(level: Level) -> CoreResult<Vec<NodeSlot>> {
    let mut out: Vec<NodeSlot> = Vec::new();
    // Maps depth to the preorder index of the node currently open at that depth,
    // which gives each node its parent without a second traversal.
    let mut open: BTreeMap<usize, u64> = BTreeMap::new();
    visit_preorder(level, |cursor| {
        let depth = cursor.steps().len();
        let parent = if depth == 0 {
            None
        } else {
            open.get(&(depth - 1)).copied()
        };
        open.insert(depth, cursor.index().get());
        out.push(NodeSlot {
            index: cursor.index().get(),
            path: cursor.to_path().render(),
            shape: cursor.shape(),
            region: cursor.region(),
            kind: cursor.kind(),
            parent,
        });
        Ok(Walk::Continue)
    })?;
    Ok(out)
}

impl TrackATree {
    /// Build a tree from decoded per-node variables in canonical preorder.
    ///
    /// The variable *kind* supplied for each node must match the kind the tree
    /// structure implies; a mismatch is rejected rather than reinterpreted,
    /// because the certificate's arrays are positional (§5.2).
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::CountMismatch`] for a length mismatch and
    /// [`ErrorCode::BadPath`] when a node's variable kind is wrong.
    pub fn new(instance: OmegaInstance, variables: Vec<NodeVariables>) -> CoreResult<Self> {
        let slots = skeleton(instance.level())?;
        if slots.len() != variables.len() {
            return Err(CoreError::new(
                ErrorCode::CountMismatch,
                "the node array length disagrees with the instance tree",
            )
            .equation("§5.2")
            .value(format!(
                "{} nodes, {} entries",
                slots.len(),
                variables.len()
            )));
        }
        let mut nodes = Vec::with_capacity(slots.len());
        for (slot, vars) in slots.into_iter().zip(variables) {
            let matches = matches!(
                (&slot.kind, &vars),
                (NodeKind::Root, NodeVariables::Root { .. })
                    | (NodeKind::PositiveInterior, NodeVariables::Interior { .. })
                    | (NodeKind::ZeroShape, NodeVariables::ZeroShape { .. })
                    | (
                        NodeKind::PositiveLevelTwo,
                        NodeVariables::PositiveLevelTwo { .. }
                    )
            );
            if !matches {
                return Err(CoreError::new(
                    ErrorCode::BadPath,
                    "a node's free-variable kind disagrees with its position in the tree",
                )
                .equation("A.2")
                .value(slot.path.clone()));
            }
            nodes.push(TreeNode {
                index: slot.index,
                path: slot.path,
                shape: slot.shape,
                region: slot.region,
                kind: slot.kind,
                parent: slot.parent,
                variables: vars,
            });
        }
        // `visit_preorder` numbers nodes with a sequential counter and they are
        // pushed in visit order, so a node's `index` equals its position. Every
        // parent lookup below relies on that, and relying on it silently is how
        // it would stop being true: it is checked once here, in O(N), rather
        // than rediscovered as a wrong mass.
        for (position, node) in nodes.iter().enumerate() {
            if node.index != position as u64 {
                return Err(CoreError::new(
                    ErrorCode::BadPath,
                    "node indices are not the preorder positions",
                )
                .equation("§5.2")
                .value(alloc::format!(
                    "position {position} carries index {}",
                    node.index
                )));
            }
        }
        let mut children: Vec<Vec<u32>> = alloc::vec![Vec::new(); nodes.len()];
        for node in &nodes {
            if let Some(parent) = node.parent
                && let Some(slot) = children.get_mut(parent as usize)
                && let Ok(index) = u32::try_from(node.index)
            {
                slot.push(index);
            }
        }
        let mut tree = Self {
            instance,
            nodes,
            masses: Vec::new(),
            children,
        };
        tree.validate_domains()?;
        tree.masses = tree.compute_masses()?;
        Ok(tree)
    }

    /// The instance.
    #[must_use]
    pub const fn instance(&self) -> OmegaInstance {
        self.instance
    }

    /// The nodes, in canonical preorder.
    #[must_use]
    pub fn nodes(&self) -> &[TreeNode] {
        &self.nodes
    }

    /// The preorder positions of a node's children (A.1).
    #[must_use]
    pub fn children_of(&self, index: u64) -> &[u32] {
        self.children
            .get(index as usize)
            .map_or(&[], alloc::vec::Vec::as_slice)
    }

    /// The mass of each node, in canonical preorder (A.4).
    #[must_use]
    pub fn masses(&self) -> &[Rat] {
        &self.masses
    }

    /// The shape domain a node's `α` ranges over: `S_ℓ*` at the root,
    /// `Split(s_T)` at an interior node (A.2).
    ///
    /// # Errors
    ///
    /// Propagates split-enumeration failures.
    pub fn alpha_domain(&self, node: &TreeNode) -> CoreResult<ShapeDomain> {
        match node.kind {
            NodeKind::Root => Ok(ShapeDomain::full(self.instance.level())),
            NodeKind::PositiveInterior => {
                let shape = node.shape.ok_or_else(|| {
                    CoreError::new(ErrorCode::BadPath, "an interior node must have a shape")
                        .equation("A.1")
                })?;
                ShapeDomain::splits(shape)
            }
            _ => Err(CoreError::new(
                ErrorCode::BadPath,
                "only the root and positive interior nodes carry alpha",
            )
            .equation("A.2")),
        }
    }

    /// Validate every free variable against its A.2 domain.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadSimplex`] for a distribution violation and
    /// [`ErrorCode::CountMismatch`] for a length mismatch.
    fn validate_domains(&self) -> CoreResult<()> {
        for node in &self.nodes {
            match &node.variables {
                NodeVariables::Root {
                    region_weights,
                    alpha,
                }
                | NodeVariables::Interior {
                    region_weights,
                    alpha,
                } => {
                    if region_weights.len() != 6 {
                        return Err(self.count_error(node, "A_T must have six entries"));
                    }
                    mm_rat::entropy::validate_simplex(region_weights)
                        .map_err(|error| error.value(node.path.clone()))?;
                    if alpha.len() != 6 {
                        return Err(self.count_error(node, "alpha must have one entry per region"));
                    }
                    let domain = self.alpha_domain(node)?;
                    for distribution in alpha {
                        if distribution.len() != domain.len() {
                            return Err(self.count_error(
                                node,
                                "an alpha distribution disagrees with its domain size",
                            ));
                        }
                        mm_rat::entropy::validate_simplex(distribution)
                            .map_err(|error| error.value(node.path.clone()))?;
                    }
                }
                NodeVariables::ZeroShape { beta } => {
                    let domain = self.beta_domain(node)?;
                    if beta.len() != domain.len() {
                        return Err(self.count_error(
                            node,
                            "a beta distribution disagrees with its support-vector domain",
                        ));
                    }
                    mm_rat::entropy::validate_simplex(beta)
                        .map_err(|error| error.value(node.path.clone()))?;
                }
                NodeVariables::PositiveLevelTwo { mu } => {
                    // A.2 fixes the domain as the closed interval [0, 1/2].
                    if mu.is_negative() || *mu > Rat::from_signeds(1, 2) {
                        return Err(CoreError::new(
                            ErrorCode::BadSimplex,
                            "a level-2 mu must lie in [0, 1/2]",
                        )
                        .equation("A.2")
                        .value(node.path.clone())
                        .value(format!("{mu}")));
                    }
                }
            }
        }
        Ok(())
    }

    fn count_error(&self, node: &TreeNode, message: &str) -> CoreError {
        CoreError::new(
            ErrorCode::CountMismatch,
            alloc::string::String::from(message),
        )
        .equation("A.2")
        .value(node.path.clone())
    }

    /// The support-vector domain a zero-shape node's `β` ranges over (A.2).
    ///
    /// `W` is the first coordinate in `X < Y < Z` order with `s_(T,W) > 0`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] when the node is not zero-shape.
    pub fn beta_domain(&self, node: &TreeNode) -> CoreResult<Vec<SupportVector>> {
        let shape = node.shape.ok_or_else(|| {
            CoreError::new(ErrorCode::BadPath, "a zero-shape node must have a shape")
                .equation("A.2")
        })?;
        let coordinate = shape.first_nonzero_coord().ok_or_else(|| {
            CoreError::new(
                ErrorCode::BadPath,
                "a zero-shape node with no positive coordinate cannot occur for a positive level",
            )
            .equation("A.2")
        })?;
        support_vectors(shape.level(), shape.coord(coordinate))
    }

    /// Masses in canonical preorder, computed top-down (A2, A3).
    ///
    /// `m_G = 1`; `m_(G[s,r]) = A_G^(r) α_G^(r)(s)`; and for a positive parent of
    /// level at least 3, `m_(T[u,r]) = m_T A_T^(r) (α_T^(r)(u) + α_T^(r)(s_T-u))`.
    ///
    /// # Errors
    ///
    /// Propagates domain failures.
    fn compute_masses(&self) -> CoreResult<Vec<Rat>> {
        let mut masses = alloc::vec![Rat::zero(); self.nodes.len()];
        for (position, node) in self.nodes.iter().enumerate() {
            match node.parent {
                None => {
                    if let Some(slot) = masses.get_mut(position) {
                        *slot = Rat::one();
                    }
                }
                Some(parent_index) => {
                    // Direct, not a scan: index is position. The scan made
                    // compute_masses O(N^2) -- 3.4e7 element visits at l*=3,
                    // which is invisible, and 2.4e12 at l*=4, which is not.
                    let parent = self.nodes.get(parent_index as usize).ok_or_else(|| {
                        CoreError::new(ErrorCode::BadPath, "a node names a missing parent")
                            .equation("§5.2")
                    })?;
                    let region = node.region.ok_or_else(|| {
                        CoreError::new(ErrorCode::BadPath, "a non-root node must have a region")
                            .equation("§5.2")
                    })?;
                    let shape = node.shape.ok_or_else(|| {
                        CoreError::new(ErrorCode::BadPath, "a non-root node must have a shape")
                            .equation("§5.2")
                    })?;
                    let (weights, alpha) = match &parent.variables {
                        NodeVariables::Root {
                            region_weights,
                            alpha,
                        }
                        | NodeVariables::Interior {
                            region_weights,
                            alpha,
                        } => (region_weights, alpha),
                        _ => {
                            return Err(CoreError::new(
                                ErrorCode::BadPath,
                                "a leaf cannot be a parent",
                            )
                            .equation("A.1"));
                        }
                    };
                    let region_index = usize::from(region.get() - 1);
                    let weight = weights
                        .get(region_index)
                        .ok_or_else(|| self.count_error(parent, "A_T is missing a region entry"))?;
                    let domain = self.alpha_domain(parent)?;
                    let distribution = alpha.get(region_index).ok_or_else(|| {
                        self.count_error(parent, "alpha is missing a region entry")
                    })?;
                    let shape_index = domain
                        .shapes()
                        .iter()
                        .position(|candidate| *candidate == shape)
                        .ok_or_else(|| {
                            CoreError::new(
                                ErrorCode::BadPath,
                                "a child's shape is not in its parent's alpha domain",
                            )
                            .equation("A.1")
                            .value(node.path.clone())
                        })?;
                    let alpha_value = distribution.get(shape_index).ok_or_else(|| {
                        self.count_error(parent, "alpha is shorter than its domain")
                    })?;

                    let parent_mass = masses
                        .get(parent_index as usize)
                        .cloned()
                        .unwrap_or_else(Rat::zero);

                    let mass = if parent.kind == NodeKind::Root {
                        // A2: the root contributes no mass factor of its own.
                        weight * alpha_value
                    } else {
                        // A3: the complementary split shares the child's weight.
                        let parent_shape = parent.shape.ok_or_else(|| {
                            CoreError::new(ErrorCode::BadPath, "an interior node must have a shape")
                                .equation("A.1")
                        })?;
                        let complement = parent_shape.complement(shape)?;
                        let complement_index = domain
                            .shapes()
                            .iter()
                            .position(|candidate| *candidate == complement)
                            .ok_or_else(|| {
                                CoreError::new(
                                    ErrorCode::BadPath,
                                    "a complementary split is not in the alpha domain",
                                )
                                .equation("A.1")
                            })?;
                        let complement_value =
                            distribution.get(complement_index).ok_or_else(|| {
                                self.count_error(parent, "alpha is shorter than its domain")
                            })?;
                        &(&parent_mass * weight) * &(alpha_value + complement_value)
                    };
                    if let Some(slot) = masses.get_mut(position) {
                        *slot = mass;
                    }
                }
            }
        }
        Ok(masses)
    }

    /// The complete split distribution `β_(T,W)` of a **level-2** node (A4, A7).
    ///
    /// For a positive level-2 node the shape is exactly `(1,1,2)`, `(1,2,1)`, or
    /// `(2,1,1)`; the `μ` distribution sits on the coordinate whose value is 2
    /// and the half/half distributions on the other two (A7).
    ///
    /// For a zero-shape node, `β_(T,W0)` is the point mass at `0⃗`, `β_(T,W1)` is
    /// the free distribution, and `β_(T,W2) = β_(T,W1)^∨` with
    /// `β^∨(2⃗-L) = β(L)` (A4).
    ///
    /// The returned vector is indexed by the canonical support-vector order of
    /// `C_(2, ·)` for the coordinate's own total.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] for a node that is not a level-2 leaf.
    pub fn beta(
        &self,
        node: &TreeNode,
        coordinate: Coordinate,
    ) -> CoreResult<Vec<(SupportVector, Rat)>> {
        let shape = node.shape.ok_or_else(|| {
            CoreError::new(ErrorCode::BadPath, "a leaf must have a shape").equation("A.5")
        })?;
        match &node.variables {
            NodeVariables::PositiveLevelTwo { mu } => {
                let vectors = support_vectors(shape.level(), shape.coord(coordinate))?;
                let mut out = Vec::with_capacity(vectors.len());
                if shape.coord(coordinate) == 2 {
                    // A7: mu * delta_(0,2) + mu * delta_(2,0) + (1-2mu) * delta_(1,1).
                    let one_minus = &Rat::one() - &(&Rat::from_integer(2) * mu);
                    for vector in vectors {
                        let value = match vector.entries() {
                            [0, 2] | [2, 0] => mu.clone(),
                            [1, 1] => one_minus.clone(),
                            _ => Rat::zero(),
                        };
                        out.push((vector, value));
                    }
                } else {
                    // A7: the half/half distribution on the unit coordinates.
                    for vector in vectors {
                        let value = match vector.entries() {
                            [0, 1] | [1, 0] => Rat::from_signeds(1, 2),
                            _ => Rat::zero(),
                        };
                        out.push((vector, value));
                    }
                }
                Ok(out)
            }
            NodeVariables::ZeroShape { beta } => {
                let zero_coord = shape.first_zero_coord().ok_or_else(|| {
                    CoreError::new(ErrorCode::BadPath, "a zero-shape node has a zero coordinate")
                        .equation("A.5")
                })?;
                let free_coord = shape.first_nonzero_coord().ok_or_else(|| {
                    CoreError::new(
                        ErrorCode::BadPath,
                        "a zero-shape node with no positive coordinate cannot occur",
                    )
                    .equation("A.5")
                })?;
                let vectors = support_vectors(shape.level(), shape.coord(coordinate))?;
                if coordinate == zero_coord {
                    // beta_(T,W0) = point mass at the zero vector.
                    let mut out = Vec::with_capacity(vectors.len());
                    for vector in vectors {
                        let value = if vector.entries().iter().all(|entry| *entry == 0) {
                            Rat::one()
                        } else {
                            Rat::zero()
                        };
                        out.push((vector, value));
                    }
                    Ok(out)
                } else if coordinate == free_coord {
                    let free_vectors = support_vectors(shape.level(), shape.coord(free_coord))?;
                    Ok(free_vectors.into_iter().zip(beta.iter().cloned()).collect())
                } else {
                    // beta_(T,W2) = beta^∨ with beta^∨(2⃗ - L) = beta(L)  (A4).
                    let free_vectors = support_vectors(shape.level(), shape.coord(free_coord))?;
                    let mut out = Vec::with_capacity(vectors.len());
                    for vector in vectors {
                        let source = vector.complement();
                        let value = free_vectors
                            .iter()
                            .position(|candidate| *candidate == source)
                            .and_then(|index| beta.get(index))
                            .cloned()
                            .unwrap_or_else(Rat::zero);
                        out.push((vector, value));
                    }
                    Ok(out)
                }
            }
            _ => Err(CoreError::new(
                ErrorCode::BadPath,
                "beta is defined here only for level-2 leaves; A.5's interior recursion is not implemented",
            )
            .equation("A.5")
            .value(node.path.clone())),
        }
    }
}
