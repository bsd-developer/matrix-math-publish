//! Node identity and canonical tree traversal (spec §5.2, A.1).
//!
//! A node is identified by its **complete root-to-node path**, not by level,
//! shape, or region alone: two nodes with the same level, shape, and region but
//! different ancestors are genuinely distinct and carry independent free
//! variables (A.1). Collapsing them would silently merge constraints.
//!
//! Every dense certificate array indexed by nodes uses the depth-first preorder
//! of [`visit_preorder`]. Diagnostics print both the traversal index and the
//! rendered `NodePath` (§5.2).

use crate::codes::ErrorCode;
use crate::error::{CoreError, CoreResult};
use crate::level::Level;
use crate::region::Region;
use crate::shape::Shape;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// Depth-first preorder index of a node within one instance's tree (§5.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TreeIndex(u64);

impl TreeIndex {
    /// The index of the root, which is always zero.
    pub const ROOT: Self = Self(0);

    /// Wrap a raw preorder index.
    #[must_use]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    /// The raw preorder index.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

impl fmt::Display for TreeIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// One step down the tree.
///
/// The root step names a shape in `S_ℓ*`; every later step names a split of its
/// parent's shape. In both cases the recorded shape is the **child node's own
/// shape**, which is what `A_T` and `α_T` are indexed by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Step {
    shape: Shape,
    region: Region,
}

impl Step {
    /// Build a step from a shape and region.
    #[must_use]
    pub const fn new(shape: Shape, region: Region) -> Self {
        Self { shape, region }
    }

    /// The node's own shape.
    #[must_use]
    pub const fn shape(self) -> Shape {
        self.shape
    }

    /// The region chosen at this step.
    #[must_use]
    pub const fn region(self) -> Region {
        self.region
    }

    /// The canonical sort key `(region, shape)` used by the traversal (§5.2).
    #[must_use]
    pub fn canonical_key(self) -> (u8, (u16, u16, u16)) {
        (self.region.get(), self.shape.canonical_key())
    }
}

impl fmt::Display for Step {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{},r{}]", self.shape, self.region)
    }
}

/// The root step of a path (§5.2).
pub type RootStep = Step;
/// A non-root step of a path (§5.2).
pub type ChildStep = Step;

/// What kind of node a path denotes, which fixes which free variables it carries
/// (A.2) and whether it has children (A.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeKind {
    /// The root `G`, which has no level, shape, or region.
    Root,
    /// A zero-shape node: a leaf carrying `β_(T,W)` (A.2).
    ZeroShape,
    /// A positive level-2 node: a leaf carrying `μ_T ∈ [0,1/2]` (A.2).
    PositiveLevelTwo,
    /// A positive node of level at least 3, carrying `A_T` and `α_T^(r)` (A.2).
    PositiveInterior,
}

impl NodeKind {
    /// Whether nodes of this kind have children (A.1).
    #[must_use]
    pub const fn has_children(self) -> bool {
        matches!(self, Self::Root | Self::PositiveInterior)
    }
}

/// Classify a node from its shape, or [`NodeKind::Root`] when there is no shape.
#[must_use]
pub fn classify(shape: Option<Shape>) -> NodeKind {
    match shape {
        None => NodeKind::Root,
        Some(shape) if shape.is_zero_shape() => NodeKind::ZeroShape,
        Some(shape) if shape.level().get() == 2 => NodeKind::PositiveLevelTwo,
        Some(_) => NodeKind::PositiveInterior,
    }
}

/// The complete identity of a tree node (§5.2).
///
/// An empty step list denotes the root `G`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodePath(Vec<Step>);

impl NodePath {
    /// The root path.
    #[must_use]
    pub const fn root() -> Self {
        Self(Vec::new())
    }

    /// Build a path from steps, validating it against the instance's `ℓ*`.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] when any step is inconsistent with its
    /// parent: a wrong level, a split that is not coordinatewise below its
    /// parent, or a child of a leaf.
    pub fn new(root_level: Level, steps: Vec<Step>) -> CoreResult<Self> {
        let path = Self(steps);
        path.validate(root_level)?;
        Ok(path)
    }

    /// The steps of the path, root first.
    #[must_use]
    pub fn steps(&self) -> &[Step] {
        &self.0
    }

    /// Whether this is the root path.
    #[must_use]
    pub fn is_root(&self) -> bool {
        self.0.is_empty()
    }

    /// The node's shape, or `None` for the root.
    #[must_use]
    pub fn shape(&self) -> Option<Shape> {
        self.0.last().map(|step| step.shape())
    }

    /// The node's region, or `None` for the root.
    #[must_use]
    pub fn region(&self) -> Option<Region> {
        self.0.last().map(|step| step.region())
    }

    /// The node's level, or `None` for the root.
    #[must_use]
    pub fn level(&self) -> Option<Level> {
        self.shape().map(Shape::level)
    }

    /// The node's kind (A.1, A.2).
    #[must_use]
    pub fn kind(&self) -> NodeKind {
        classify(self.shape())
    }

    /// Extend the path by one step, validating it against this node.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] when this node is a leaf, or when `shape`
    /// is not an admissible child shape.
    pub fn child(&self, root_level: Level, shape: Shape, region: Region) -> CoreResult<Self> {
        let mut steps = self.0.clone();
        steps.push(Step::new(shape, region));
        Self::new(root_level, steps)
    }

    /// Validate every step against `ℓ*` and its parent (§5.2).
    ///
    /// The level and child shape are **recomputed** from the path; redundant
    /// data supplied elsewhere must agree or be rejected.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadPath`] on the first inconsistency.
    pub fn validate(&self, root_level: Level) -> CoreResult<()> {
        let mut parent: Option<Shape> = None;
        for (depth, step) in self.0.iter().enumerate() {
            match parent {
                None => {
                    if step.shape().level() != root_level {
                        return Err(self
                            .bad_path(depth, "the root step must name a shape in S_(l*)")
                            .value(format!("{}", step.shape())));
                    }
                }
                Some(parent_shape) => {
                    if classify(Some(parent_shape)) != NodeKind::PositiveInterior {
                        return Err(
                            self.bad_path(depth, "only a positive node of level >= 3 has children")
                        );
                    }
                    // `complement` re-derives the child level and rejects a split
                    // that is not coordinatewise below the parent.
                    parent_shape.complement(step.shape())?;
                }
            }
            parent = Some(step.shape());
        }
        Ok(())
    }

    fn bad_path(&self, depth: usize, message: &str) -> CoreError {
        CoreError::new(ErrorCode::BadPath, alloc::string::String::from(message))
            .equation("§5.2")
            .at(crate::error::Location::NodePath(self.render()))
            .value(format!("step {depth}"))
    }

    /// Render the canonical textual form used in diagnostics (§5.2).
    ///
    /// The root is `G`; each step appends `[shape,rN]`.
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::from("G");
        for step in &self.0 {
            out.push_str(&format!("{step}"));
        }
        out
    }
}

impl fmt::Display for NodePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render())
    }
}

/// A borrowed view of the node the traversal is currently visiting.
#[derive(Clone, Copy, Debug)]
pub struct NodeCursor<'a> {
    index: TreeIndex,
    steps: &'a [Step],
}

impl<'a> NodeCursor<'a> {
    /// The depth-first preorder index of this node.
    #[must_use]
    pub const fn index(self) -> TreeIndex {
        self.index
    }

    /// The path steps, root first.
    #[must_use]
    pub const fn steps(self) -> &'a [Step] {
        self.steps
    }

    /// The node's shape, or `None` at the root.
    #[must_use]
    pub fn shape(self) -> Option<Shape> {
        self.steps.last().map(|step| step.shape())
    }

    /// The node's region, or `None` at the root.
    #[must_use]
    pub fn region(self) -> Option<Region> {
        self.steps.last().map(|step| step.region())
    }

    /// The node's level, or `None` at the root.
    #[must_use]
    pub fn level(self) -> Option<Level> {
        self.shape().map(Shape::level)
    }

    /// The node's kind.
    #[must_use]
    pub fn kind(self) -> NodeKind {
        classify(self.shape())
    }

    /// The parent's shape, or `None` when the parent is the root.
    #[must_use]
    pub fn parent_shape(self) -> Option<Shape> {
        let len = self.steps.len();
        if len < 2 {
            None
        } else {
            self.steps.get(len - 2).map(|step| step.shape())
        }
    }

    /// Materialize an owned [`NodePath`].
    #[must_use]
    pub fn to_path(self) -> NodePath {
        NodePath(self.steps.to_vec())
    }
}

/// Whether a traversal should continue or stop early.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Walk {
    /// Keep traversing.
    Continue,
    /// Stop the traversal and return successfully.
    Stop,
}

/// Visit every node of the instance tree in canonical depth-first preorder
/// (§5.2), calling `visit` once per node including the root.
///
/// The traversal allocates one shared step buffer rather than one path per node,
/// so it is usable at `ℓ*=4` scale where materializing every `NodePath` would be
/// prohibitive.
///
/// Child order is region `1..=6` outermost, then shape (root) or split
/// (interior) in lexicographic order.
///
/// # Errors
///
/// Propagates the first error returned by `visit`, or any error from split
/// enumeration.
pub fn visit_preorder<F>(root_level: Level, mut visit: F) -> CoreResult<()>
where
    F: FnMut(NodeCursor<'_>) -> CoreResult<Walk>,
{
    let mut steps: Vec<Step> = Vec::new();
    let mut next_index: u64 = 0;
    let mut stopped = false;
    walk(
        root_level,
        &mut steps,
        &mut next_index,
        &mut visit,
        &mut stopped,
    )
}

fn walk<F>(
    root_level: Level,
    steps: &mut Vec<Step>,
    next_index: &mut u64,
    visit: &mut F,
    stopped: &mut bool,
) -> CoreResult<()>
where
    F: FnMut(NodeCursor<'_>) -> CoreResult<Walk>,
{
    if *stopped {
        return Ok(());
    }
    let index = TreeIndex::new(*next_index);
    *next_index += 1;
    let cursor = NodeCursor {
        index,
        steps: steps.as_slice(),
    };
    let kind = cursor.kind();
    if visit(cursor)? == Walk::Stop {
        *stopped = true;
        return Ok(());
    }
    if !kind.has_children() {
        return Ok(());
    }
    let child_shapes = match steps.last() {
        None => Shape::enumerate(root_level),
        Some(step) => step.shape().splits()?,
    };
    for region in Region::all() {
        for shape in &child_shapes {
            steps.push(Step::new(*shape, region));
            walk(root_level, steps, next_index, visit, stopped)?;
            steps.pop();
            if *stopped {
                return Ok(());
            }
        }
    }
    Ok(())
}

/// Count the nodes in the instance tree, including the root (§5.2).
///
/// # Errors
///
/// Propagates split-enumeration errors.
pub fn node_count(root_level: Level) -> CoreResult<u64> {
    let mut count = 0u64;
    visit_preorder(root_level, |_| {
        count += 1;
        Ok(Walk::Continue)
    })?;
    Ok(count)
}

/// Collect every node path in canonical preorder.
///
/// This materializes one [`NodePath`] per node and is intended for tests and
/// small instances; large instances use [`visit_preorder`].
///
/// # Errors
///
/// Propagates split-enumeration errors.
pub fn collect_paths(root_level: Level) -> CoreResult<Vec<NodePath>> {
    let mut out = Vec::new();
    visit_preorder(root_level, |cursor| {
        out.push(cursor.to_path());
        Ok(Walk::Continue)
    })?;
    Ok(out)
}
