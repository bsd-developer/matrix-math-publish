import MatrixMath.Spec.Omega

/-!
# The Appendix A combination-loss problem

Normative source: `docs/specs/0001_spec.md` A.1–A.10.

This module transcribes the S1 optimization problem of A.10 into Lean, for every
`ℓ*`, and defines `MatrixMath.CombinationLossFeasible` as its feasible set. That
definition is what `AX1_combination_loss` is stated about, so the axiom now
relates `ω` to a written-down mathematical object rather than to a black box.

## Why the tree is a rose tree and not a dependent family

A.1 says two nodes with the same level, shape, and region but different ancestors
are *distinct*. A dependent family indexed by `(level, shape)` would identify
them. A rose tree whose children carry their own region, shape, and parental
`α` weight keeps them apart by construction: the node *is* its position.

## Why everything is stated over `ℚ` except entropies

A2, A3, A4, A5, A6, and A7 are built from the free variables by addition and
multiplication only, so every mass and every split distribution is an exact
rational. Real numbers enter Appendix A in exactly three places — `H(·)`,
`log2 q`, and `H_D^max` — which is what makes the §7.2 directed evaluation sound
rather than merely plausible.

## Scope of the accompanying proofs

The definitions here are general in `ℓ*`. The *checker* proved sound against them
(`MatrixMath.Certificate.OmegaCheck`) covers `ℓ* = 2`, where A.7's interior
recursion is vacuous. §3.4 forbids a reduced Lean instance from certifying a
larger Rust-checked one, so the checker rejects `ℓ* ≥ 3` instead of assuming it.
-/

namespace MatrixMath.Spec

open scoped List

/-! ## Shapes and splits (A.1) -/

/-- A shape `(i, j, k)`, written in `X, Y, Z` order (§5.1). -/
abbrev AShape := ℕ × ℕ × ℕ

/-- `s ∈ S_ℓ`: the shape entries sum to `2^ℓ` (A.1). -/
def AShape.atLevel (s : AShape) (ℓ : ℕ) : Prop := s.1 + s.2.1 + s.2.2 = 2 ^ ℓ

instance (s : AShape) (ℓ : ℕ) : Decidable (s.atLevel ℓ) := by
  unfold AShape.atLevel; infer_instance

/-- The shape is positive when all three coordinates are (A.1). -/
def AShape.positive (s : AShape) : Prop := 0 < s.1 ∧ 0 < s.2.1 ∧ 0 < s.2.2

instance (s : AShape) : Decidable s.positive := by unfold AShape.positive; infer_instance

/-- Componentwise `u ≤ s`, the constraint defining `Split(s_T)` (A.1). -/
def AShape.le (u s : AShape) : Prop := u.1 ≤ s.1 ∧ u.2.1 ≤ s.2.1 ∧ u.2.2 ≤ s.2.2

instance (u s : AShape) : Decidable (u.le s) := by unfold AShape.le; infer_instance

/-- `s_T - u`, the complementary split (A.1, A3). -/
def AShape.sub (s u : AShape) : AShape := (s.1 - u.1, s.2.1 - u.2.1, s.2.2 - u.2.2)

/-- One coordinate of a shape, in `X < Y < Z` order (§5.1). -/
def AShape.coord (s : AShape) : Coordinate → ℕ
  | .X => s.1
  | .Y => s.2.1
  | .Z => s.2.2

/-- The first coordinate whose entry is zero (A.5 `W0`). -/
def AShape.firstZero (s : AShape) : Coordinate :=
  if s.1 = 0 then .X else if s.2.1 = 0 then .Y else .Z

/-- The first coordinate whose entry is positive (A.5 `W1`). -/
def AShape.firstPos (s : AShape) : Coordinate :=
  if s.1 ≠ 0 then .X else if s.2.1 ≠ 0 then .Y else .Z

/-- The remaining coordinate (A.5 `W2`). -/
def AShape.other (s : AShape) : Coordinate :=
  match s.firstZero, s.firstPos with
  | .X, .Y => .Z
  | .X, .Z => .Y
  | .Y, .X => .Z
  | .Y, .Z => .X
  | .Z, .X => .Y
  | .Z, .Y => .X
  | _, _ => .Z

/-! ## Finitely supported rational distributions

A `Dist κ` is an association list. Its *value* as a distribution is the total
weight it assigns to each key, so duplicate keys are summed rather than treated
as distinct atoms: A.6 mixes distributions whose supports overlap, and entropy is
a function of the merged weights.
-/

/-- A finitely supported rational assignment, as key/weight pairs. -/
abbrev Dist (κ : Type) := List (κ × ℚ)

namespace Dist

variable {κ : Type} [DecidableEq κ]

/-- The total weight assigned to one key. -/
def at' (d : Dist κ) (k : κ) : ℚ := ((d.filter fun p => p.1 = k).map Prod.snd).sum

/-- The distinct keys, in first-appearance order. -/
def keys (d : Dist κ) : List κ := (d.map Prod.fst).dedup

/-- The merged distribution: one entry per distinct key. -/
def collect (d : Dist κ) : Dist κ := d.keys.map fun k => (k, d.at' k)

/-- The merged weights, which is what `H(·)` is a function of. -/
def weights (d : Dist κ) : List ℚ := d.collect.map Prod.snd

/-- The total weight. -/
def total (d : Dist κ) : ℚ := (d.map Prod.snd).sum

/-- `d ∈ Δ(support)`: nonnegative weights summing to one (A.2). -/
def IsProb (d : Dist κ) : Prop := (∀ p ∈ d, 0 ≤ p.2) ∧ d.total = 1

instance (d : Dist κ) : Decidable (IsProb d) := by unfold IsProb; infer_instance

/-- Scale every weight. -/
def smul (c : ℚ) (d : Dist κ) : Dist κ := d.map fun p => (p.1, c * p.2)

/-- The mixture of a weighted family, as concatenation of scaled parts. -/
def mix (parts : List (ℚ × Dist κ)) : Dist κ :=
  parts.flatMap fun p => smul p.1 p.2

end Dist

/-- A support vector `L ∈ {0,1,2}^(2^(ℓ-1))` (A.2). -/
abbrev SupportVec := List ℕ

/-- `L ∈ C_(ℓ,a)`: length `2^(ℓ-1)`, entries at most two, total `a` (A.2). -/
def SupportVec.mem (L : SupportVec) (ℓ a : ℕ) : Prop :=
  L.length = 2 ^ (ℓ - 1) ∧ (∀ x ∈ L, x ≤ 2) ∧ L.sum = a

instance (L : SupportVec) (ℓ a : ℕ) : Decidable (L.mem ℓ a) := by
  unfold SupportVec.mem; infer_instance

/-- Vectors of a given length over `{0,1,2}` summing to `a`, lexicographically. -/
def supportListLen : ℕ → ℕ → List SupportVec
  | 0, a => if a = 0 then [[]] else []
  | n + 1, a =>
    (List.range 3).flatMap fun x =>
      if x ≤ a then (supportListLen n (a - x)).map fun rest => x :: rest else []

/-- `C_(ℓ,a)` in canonical lexicographic order (A.2).

A producer and a checker that disagree about this order pair the same
probabilities with different support vectors, so it is written once and used by
the byte decoder rather than reconstructed per call site. -/
def supportList (ℓ a : ℕ) : List SupportVec := supportListLen (2 ^ (ℓ - 1)) a

/-- `2⃗ - L`, the involution behind `β^∨` (A4). -/
def SupportVec.dual (L : SupportVec) : SupportVec := L.map fun x => 2 - x

/-- `|{p : L_p = 1}|`, the count A18 multiplies by `log2 q`. -/
def SupportVec.ones (L : SupportVec) : ℕ := (L.filter fun x => x = 1).length

/-- `L₁ × L₂`, the concatenation of A.5. -/
def SupportVec.concat (L₁ L₂ : SupportVec) : SupportVec := L₁ ++ L₂

/-- The `×` product of two split distributions (A.5). -/
def betaProduct (d₁ d₂ : Dist SupportVec) : Dist SupportVec :=
  d₁.flatMap fun p => d₂.map fun r => (p.1.concat r.1, p.2 * r.2)

end MatrixMath.Spec

namespace MatrixMath.Spec

/-! ## Enumerations (A.1) -/

/-- `S_ℓ` in lexicographic order (A.1). -/
def shapeList (ℓ : ℕ) : List AShape :=
  (List.range (2 ^ ℓ + 1)).flatMap fun i =>
    (List.range (2 ^ ℓ + 1 - i)).filterMap fun j =>
      if i + j ≤ 2 ^ ℓ then some (i, j, 2 ^ ℓ - i - j) else none

/-- `Split(s)` at a parent of level `ℓ`, in lexicographic order (A.1). -/
def splitList (ℓ : ℕ) (s : AShape) : List AShape :=
  (List.range (s.1 + 1)).flatMap fun i =>
    (List.range (s.2.1 + 1)).flatMap fun j =>
      (List.range (s.2.2 + 1)).filterMap fun k =>
        if i + j + k = 2 ^ (ℓ - 1) then some (i, j, k) else none

theorem mem_shapeList {ℓ : ℕ} {s : AShape} (h : s ∈ shapeList ℓ) : s.atLevel ℓ := by
  simp only [shapeList, List.mem_flatMap, List.mem_filterMap, List.mem_range] at h
  obtain ⟨i, hi, j, hj, hcond⟩ := h
  split at hcond
  · rename_i hle
    simp only [Option.some.injEq] at hcond
    subst hcond
    show i + j + (2 ^ ℓ - i - j) = 2 ^ ℓ
    omega
  · simp at hcond

theorem mem_splitList {ℓ : ℕ} {s u : AShape} (h : u ∈ splitList ℓ s) :
    u.atLevel (ℓ - 1) ∧ u.le s := by
  simp only [splitList, List.mem_flatMap, List.mem_filterMap, List.mem_range] at h
  obtain ⟨i, hi, j, hj, k, hk, hcond⟩ := h
  split at hcond
  · rename_i hsum
    simp only [Option.some.injEq] at hcond
    subst hcond

    exact ⟨show i + j + k = 2 ^ (ℓ - 1) from hsum,
      show i ≤ s.1 from by omega, show j ≤ s.2.1 from by omega,
      show k ≤ s.2.2 from by omega⟩
  · simp at hcond

/-- Positive interior nodes in the subtree rooted at a level-`ℓ` node of shape
`s` (A.1).

§6.5 derives the maximum-entropy block count from the instance rather than
trusting the certificate, and this is the derivation. -/
def interiorNodes : ℕ → AShape → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | 2, _ => 0
  | ℓ + 3, s =>
    if AShape.positive s then
      1 + 6 * (((splitList (ℓ + 3) s).map fun u => interiorNodes (ℓ + 2) u).sum)
    else 0
  termination_by ℓ _ => ℓ
  decreasing_by omega

/-- The number of §7.4 blocks an `ℓ*` instance requires: one per region at the
root, plus one per positive interior node per region (§6.5). -/
def blockCount (levels : ℕ) : ℕ :=
  6 + 6 * (6 * (((shapeList levels).map fun s => interiorNodes levels s).sum))

/-! ## The tree (A.1, A.2)

A node value carries the data its parent chose for it: the region, its own shape,
and its `α` weight. Nothing is shared between siblings, so two nodes agreeing on
level, shape, and region but sitting under different ancestors are *different
values*, which is what A.1 demands.
-/

/-- A non-root node of the Appendix A tree, with its free variables (A.1, A.2). -/
inductive ANode where
  /-- A zero-shape leaf carrying the free `β_(T,W1) ∈ Δ(C_(ℓ,s_(T,W1)))`. -/
  | zeroLeaf (region : ℕ) (shape : AShape) (alpha : ℚ) (beta : Dist SupportVec)
  /-- A positive level-2 leaf carrying the free `μ_T ∈ [0, 1/2]`. -/
  | posTwo (region : ℕ) (shape : AShape) (alpha : ℚ) (mu : ℚ)
  /-- A positive node of level at least three carrying `A_T ∈ Δ([6])` and its
  children, one per region and split. -/
  | posBranch (region : ℕ) (shape : AShape) (alpha : ℚ) (A : List ℚ) (kids : List ANode)
  deriving Inhabited

namespace ANode

/-- The region the parent chose for this node. -/
def region : ANode → ℕ
  | .zeroLeaf r _ _ _ => r
  | .posTwo r _ _ _ => r
  | .posBranch r _ _ _ _ => r

/-- The node's own shape. -/
def shape : ANode → AShape
  | .zeroLeaf _ s _ _ => s
  | .posTwo _ s _ _ => s
  | .posBranch _ s _ _ _ => s

/-- The `α` weight the parent assigned to this node. -/
def alpha : ANode → ℚ
  | .zeroLeaf _ _ a _ => a
  | .posTwo _ _ a _ => a
  | .posBranch _ _ a _ _ => a

/-- The children of the node in a region, in the order they were given. -/
def kidsIn (n : ANode) (r : ℕ) : List ANode :=
  match n with
  | .posBranch _ _ _ _ kids => kids.filter fun k => k.region = r
  | _ => []

end ANode

end MatrixMath.Spec

namespace MatrixMath.Spec

namespace ANode

/-! ## Well-formedness (A.1, A.2)

Every constraint A.2 lists appears here, and nothing else does. Children are
required in the canonical `splitList` order: an instance is a *witness*, and any
witness can be reordered into canonical order without changing a single mass,
distribution, or entropy, so the requirement costs no generality and removes
permutation reasoning from every proof below.
-/

/-- The node is a well-formed level-`ℓ` subtree (A.1, A.2). -/
def WF : ℕ → ANode → Prop
  | ℓ, .zeroLeaf r s a b =>
      r < 6 ∧ AShape.atLevel s ℓ ∧ ¬ AShape.positive s ∧ 0 ≤ a ∧ Dist.IsProb b ∧
        ∀ p ∈ b, SupportVec.mem p.1 ℓ (AShape.coord s (AShape.firstPos s))
  | ℓ, .posTwo r s a mu =>
      ℓ = 2 ∧ r < 6 ∧ AShape.atLevel s 2 ∧ AShape.positive s ∧ 0 ≤ a ∧
        0 ≤ mu ∧ mu ≤ 1 / 2
  | ℓ, .posBranch r s a A kids =>
      3 ≤ ℓ ∧ r < 6 ∧ AShape.atLevel s ℓ ∧ AShape.positive s ∧ 0 ≤ a ∧
        A.length = 6 ∧ (∀ x ∈ A, 0 ≤ x) ∧ A.sum = 1 ∧
        (∀ rr, rr < 6 →
          ((kids.filter fun k => k.region = rr).map ANode.shape) = splitList ℓ s) ∧
        (∀ rr, rr < 6 →
          ((kids.filter fun k => k.region = rr).map ANode.alpha).sum = 1) ∧
        (∀ k ∈ kids, WF (ℓ - 1) k)
  termination_by _ n => sizeOf n
  decreasing_by
    have h := List.sizeOf_lt_of_mem ‹_ ∈ kids›
    simp only [ANode.posBranch.sizeOf_spec]
    omega

end ANode

/-- The root `G` together with its free variables (A.1, A.2).

The root has no level, shape, or region. `levels` is `ℓ*`. -/
structure AInstance where
  /-- The field size `q ≥ 1` (A.1). -/
  q : ℕ
  /-- The recursion depth `ℓ* ≥ 2` (A.1). -/
  levels : ℕ
  /-- `A_G ∈ Δ([6])` (A.2). -/
  A : List ℚ
  /-- The root's children, one per region and shape in `S_ℓ*` (A.1). -/
  kids : List ANode

namespace AInstance

/-- The root's children in one region, in the order given. -/
def kidsIn (I : AInstance) (r : ℕ) : List ANode :=
  I.kids.filter fun k => k.region = r

/-- The instance satisfies every constraint of A.1 and A.2. -/
def WF (I : AInstance) : Prop :=
  1 ≤ I.q ∧ 2 ≤ I.levels ∧
    I.A.length = 6 ∧ (∀ x ∈ I.A, 0 ≤ x) ∧ I.A.sum = 1 ∧
    (∀ r, r < 6 → ((I.kidsIn r).map ANode.shape) = shapeList I.levels) ∧
    (∀ r, r < 6 → ((I.kidsIn r).map ANode.alpha).sum = 1) ∧
    (∀ k ∈ I.kids, ANode.WF I.levels k)

end AInstance

end MatrixMath.Spec

namespace MatrixMath.Spec

/-! ## Masses and split distributions (A2–A7) -/

/-- `α_T^(r)(u)`: the weight the parent gave the region-`r` child of shape `u`.

Summing rather than selecting means a malformed duplicate cannot silently pick
one of two values; well-formedness rules duplicates out, and this definition is
total without it. -/
def alphaAt (kids : List ANode) (r : ℕ) (u : AShape) : ℚ :=
  ((kids.filter fun k => k.region = r && k.shape = u).map ANode.alpha).sum

/-- The coordinate carrying the `μ_T` distribution of a positive level-2 node,
namely the one whose shape entry is two (A7). -/
def muCoord (s : AShape) : Coordinate :=
  if s.1 = 2 then .X else if s.2.1 = 2 then .Y else .Z

mutual

/-- `β_(T,W)`, the complete split distribution of a node (A4, A5, A6, A7).

The mixture over regions and splits is written as a concatenation of scaled
association lists; `Dist.collect` merges keys wherever a weight is read. -/
def betaOf : ℕ → ANode → Coordinate → Dist SupportVec
  | ℓ, .zeroLeaf _ s _ b, W =>
      -- A4: point mass on `0⃗` at the first zero coordinate, the free
      -- distribution at the first nonzero one, and its `2⃗ - L` reflection at
      -- the remaining coordinate.
      if W = AShape.firstZero s then [(List.replicate (2 ^ (ℓ - 1)) 0, 1)]
      else if W = AShape.firstPos s then b
      else b.map fun p => (SupportVec.dual p.1, p.2)
  | _, .posTwo _ s _ mu, W =>
      -- A7.
      if W = muCoord s then [([0, 2], mu), ([2, 0], mu), ([1, 1], 1 - 2 * mu)]
      else [([0, 1], 1 / 2), ([1, 0], 1 / 2)]
  | ℓ, .posBranch _ _ _ A kids, W =>
      -- A5 then A6. Region-`r` children are `Split(s_T)` in canonical order, and
      -- `u ↦ s_T - u` reverses that order, so the complementary child of the
      -- `m`-th is the `m`-th from the end.
      Dist.mix ((List.range 6).map fun r =>
        let pr := (kids.zip (betaListOf (ℓ - 1) kids W)).filter fun p => p.1.region = r
        (A.getD r 0,
          Dist.mix ((pr.zip pr.reverse).map fun pq =>
            (alphaAt kids r pq.1.1.shape, betaProduct pq.1.2 pq.2.2))))

  termination_by _ n _ => sizeOf n

/-- `β_(T,W)` of each node in a list, in order. -/
def betaListOf : ℕ → List ANode → Coordinate → List (Dist SupportVec)
  | _, [], _ => []
  | ℓ, k :: rest, W => betaOf ℓ k W :: betaListOf ℓ rest W
  termination_by _ ns _ => sizeOf ns

end

end MatrixMath.Spec

namespace MatrixMath.Spec

open MatrixMath.Numeric

/-! ## Masses (A2, A3) -/

/-- The masses A3 assigns to the children of a positive node.

`m_(T[u,r]) = m_T A_T^(r) (α_T^(r)(u) + α_T^(r)(s_T - u))`: the complementary
split contributes to the same child, which is why the two `α` lookups are added
rather than the shape appearing twice. -/
def childMasses (m : ℚ) (s : AShape) (A : List ℚ) (kids : List ANode) : List ℚ :=
  kids.map fun k =>
    m * A.getD k.region 0 *
      (alphaAt kids k.region k.shape + alphaAt kids k.region (AShape.sub s k.shape))

/-- The masses A2 assigns to the root's children: `m_(G[s,r]) = A_G^(r) α_G^(r)(s)`. -/
def rootMasses (A : List ℚ) (kids : List ANode) : List ℚ :=
  kids.map fun k => A.getD k.region 0 * k.alpha

mutual

/-- Every node of a subtree as `(level, mass, node)`, root of the subtree first. -/
def nodesOf : ℕ → ℚ → ANode → List (ℕ × ℚ × ANode)
  | ℓ, m, .posBranch r s a A kids =>
      (ℓ, m, .posBranch r s a A kids) ::
        nodesListOf (ℓ - 1) (childMasses m s A kids) kids
  | ℓ, m, n => [(ℓ, m, n)]
  termination_by _ _ n => sizeOf n

/-- Every node of a list of subtrees, with the masses given in the same order. -/
def nodesListOf : ℕ → List ℚ → List ANode → List (ℕ × ℚ × ANode)
  | _, _, [] => []
  | ℓ, ms, k :: rest => nodesOf ℓ (ms.headD 0) k ++ nodesListOf ℓ ms.tail rest
  termination_by _ _ ns => sizeOf ns

end

namespace AInstance

/-- Every non-root node of the instance as `(level, mass, node)` (A2, A3). -/
def nodes (I : AInstance) : List (ℕ × ℚ × ANode) :=
  nodesListOf I.levels (rootMasses I.A I.kids) I.kids

/-- The leaves: zero-shape nodes at any level and positive level-2 nodes (A.1). -/
def leaves (I : AInstance) : List (ℕ × ℚ × ANode) :=
  I.nodes.filter fun t =>
    match t.2.2 with
    | .posBranch _ _ _ _ _ => false
    | _ => true

/-- `Trees_2^+`, the positive level-2 nodes (A.8). -/
def posTwoNodes (I : AInstance) : List (ℕ × ℚ × ANode) :=
  I.nodes.filter fun t =>
    match t.2.2 with
    | .posTwo _ _ _ _ => true
    | _ => false

/-- `Trees_ℓ^+`, the positive nodes at one level at least three (A.7). -/
def posNodesAt (I : AInstance) (ℓ : ℕ) : List (ℕ × ℚ × ANode) :=
  I.nodes.filter fun t =>
    t.1 = ℓ && (match t.2.2 with | .posBranch _ _ _ _ _ => true | _ => false)

/-- The root's children in one region, in canonical shape order. -/
def rootKids (I : AInstance) (r : ℕ) : List ANode := I.kidsIn r

end AInstance

/-! ## Entropies (A.3) -/

/-- `H(d)` of a finitely supported rational assignment (A.3). -/
noncomputable def hDist {κ : Type} [DecidableEq κ] (d : Dist κ) : ℝ :=
  hReal (Dist.weights d)

/-- `w · H(ν / w)` for an unnormalized mixture `ν` of total weight `w`, with the
§7.6 convention that a zero-weight conditional term contributes nothing.

Division by zero is never evaluated: the guard is on the total, and the branch
that divides is only entered when the total is nonzero. -/
noncomputable def condH {κ : Type} [DecidableEq κ] (nu : Dist κ) : ℝ :=
  if nu.total = 0 then 0
  else (nu.total : ℝ) * hReal ((Dist.weights nu).map fun v => v / nu.total)

/-- The image of a distribution under a map on keys. -/
def Dist.push {κ κ' : Type} (f : κ → κ') (d : Dist κ) : Dist κ' :=
  d.map fun p => (f p.1, p.2)

end MatrixMath.Spec

namespace MatrixMath.Spec

open MatrixMath.Numeric

/-! ## Local matrix sizes (A18, A19) -/

/-- The distribution whose entropy enters one leaf's local size (A18).

Only the first zero coordinate of a zero-shape node carries an entropy term; the
other five cases carry none, and an empty list has entropy zero. -/
def localEntropyList (ℓ : ℕ) (n : ANode) (W : Coordinate) : List ℚ :=
  match n with
  | .zeroLeaf _ s _ _ =>
      if W = AShape.firstZero s then Dist.weights (betaOf ℓ n (AShape.firstPos s))
      else []
  | _ => []

/-- The exact rational multiple of `log2 q` in one leaf's local size (A18, A19).

For a zero-shape node this is `Σ_L β(L) |{p : L_p = 1}|`; for a positive level-2
node it is `2 μ_T` on the `μ` coordinate and `1 - 2 μ_T` on the other two. -/
def localLogCoeff (ℓ : ℕ) (n : ANode) (W : Coordinate) : ℚ :=
  match n with
  | .zeroLeaf _ s _ _ =>
      if W = AShape.firstZero s then
        ((Dist.collect (betaOf ℓ n (AShape.firstPos s))).map fun p =>
          p.2 * (SupportVec.ones p.1 : ℚ)).sum
      else 0
  | .posTwo _ s _ mu => if W = muCoord s then 2 * mu else 1 - 2 * mu
  | .posBranch _ _ _ _ _ => 0

/-- `M_(T,W)` of one leaf, at every coordinate (A18, A19). -/
noncomputable def localSize (q ℓ : ℕ) (m : ℚ) (n : ANode) (W : Coordinate) : ℝ :=
  (m : ℝ) * (hReal (localEntropyList ℓ n W) +
    ((localLogCoeff ℓ n W : ℚ) : ℝ) * Real.logb 2 (q : ℝ))

/-! ## Level-2 retained exponents (A16, A17) -/

/-- The distribution whose entropy enters a level-2 retained exponent (A16). -/
def levelTwoList (s : AShape) (mu : ℚ) (W : Coordinate) : List ℚ :=
  if W = muCoord s then [mu, mu, 1 - 2 * mu] else []

/-- The exact rational constant of a level-2 retained exponent (A16). -/
def levelTwoConst (s : AShape) (W : Coordinate) : ℚ :=
  if W = muCoord s then 0 else 1

/-- `E_(T,W)` of a positive level-2 node (A16). -/
noncomputable def levelTwoExponent (m : ℚ) (s : AShape) (mu : ℚ) (W : Coordinate) : ℝ :=
  (m : ℝ) * (hReal (levelTwoList s mu W) + ((levelTwoConst s W : ℚ) : ℝ))

/-! ## Retained exponents (A8, A9, A12, A13) -/

/-- `βbar_(·,W,*,*,*)`, the unconditioned mixture of the children's `β`s (A.6). -/
def betaBar (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode) (W : Coordinate) :
    Dist SupportVec :=
  Dist.mix (kids.map fun k => (w k, betaOf ℓc k W))

/-- The children whose `β` enters `η`'s unconditioned term (A8, A12). -/
def etaYPlain (kids : List ANode) (cZ : Coordinate) : List ANode :=
  kids.filter fun k => AShape.coord k.shape cZ = 0

/-- `Σ_(u : u_Y = j, u_Z > 0) w(u) β_(·,Y)`, the unnormalized conditional
mixture of A8 and A12. -/
def etaYMix (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode) (cY cZ : Coordinate)
    (j : ℕ) : Dist SupportVec :=
  Dist.mix ((kids.filter fun k =>
    AShape.coord k.shape cY = j && 0 < AShape.coord k.shape cZ).map fun k =>
      (w k, betaOf ℓc k cY))

/-- `η_(·,Y)^(r)` (A8, A12).

`bound` may exceed the largest attainable coordinate: a conditional term whose
selecting set is empty has total weight zero, and §7.6 makes that term zero, so a
generous range changes nothing. -/
noncomputable def etaY (ℓc bound : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cY cZ : Coordinate) : ℝ :=
  ((etaYPlain kids cZ).map fun k => (w k : ℝ) * hDist (betaOf ℓc k cY)).sum +
    ((List.range (bound + 1)).map fun j =>
      condH (etaYMix ℓc w kids cY cZ j)).sum

/-- The children whose `β` enters `η_Z`'s unconditioned term (A9, A13). -/
def etaZPlain (kids : List ANode) (cX cY : Coordinate) : List ANode :=
  kids.filter fun k => AShape.coord k.shape cX = 0 || AShape.coord k.shape cY = 0

/-- `Σ_(u : u_X > 0, u_Y > 0, u_Z = k) w(u) β_(·,Z)` (A9, A13). -/
def etaZMix (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode) (cX cY cZ : Coordinate)
    (kk : ℕ) : Dist SupportVec :=
  Dist.mix ((kids.filter fun k =>
    0 < AShape.coord k.shape cX && 0 < AShape.coord k.shape cY &&
      AShape.coord k.shape cZ = kk).map fun k => (w k, betaOf ℓc k cZ))

/-- `η_(·,Z)^(r)` (A9, A13). -/
noncomputable def etaZ (ℓc bound : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cX cY cZ : Coordinate) : ℝ :=
  ((etaZPlain kids cX cY).map fun k => (w k : ℝ) * hDist (betaOf ℓc k cZ)).sum +
    ((List.range (bound + 1)).map fun kk =>
      condH (etaZMix ℓc w kids cX cY cZ kk)).sum

/-- The default entry used when reading past the end of a domain list. -/
def padShape : AShape × ℚ := ((0, 0, 0), 0)

/-- `P_D(ρ) = H_D^max(ρ) - H(ρ)` over a domain paired with its weights (A1).

The domain and the distribution travel together as one list so that no
downstream definition has to assume the two are the same length or in the same
order. -/
noncomputable def penalty (z : Dist AShape) : ℝ :=
  hMaxOf z.length
      (fun a => AShape.coord (z.getD a padShape).1 .X)
      (fun a => AShape.coord (z.getD a padShape).1 .Y)
      (fun a => AShape.coord (z.getD a padShape).1 .Z)
      (fun a => (((z.getD a padShape).2 : ℚ) : ℝ)) -
    hReal (z.map Prod.snd)

end MatrixMath.Spec

namespace MatrixMath.Spec

open MatrixMath.Numeric

/-- A node list paired with its `α` weights, the domain `P_D` is taken over. -/
def alphaZip (kids : List ANode) : Dist AShape := kids.map fun k => (k.shape, k.alpha)

/-- `β_(T,W)^(r)`, the region-`r` split mixture of A5.

Region-`r` children are `Split(s_T)` in canonical order and `u ↦ s_T - u` reverses
that order, so the complementary child of the `m`-th is the `m`-th from the end. -/
def betaRegion (ℓc : ℕ) (kids : List ANode) (r : ℕ) (W : Coordinate) :
    Dist SupportVec :=
  let pr := (kids.zip (betaListOf ℓc kids W)).filter fun p => p.1.region = r
  Dist.mix ((pr.zip pr.reverse).map fun pq =>
    (alphaAt kids r pq.1.1.shape, betaProduct pq.1.2 pq.2.2))

/-- A6 is exactly the region mixture of A5, by definition rather than by
restatement: the two cannot drift apart. -/
theorem betaOf_posBranch (ℓ r : ℕ) (s : AShape) (a : ℚ) (A : List ℚ)
    (kids : List ANode) (W : Coordinate) :
    betaOf ℓ (.posBranch r s a A kids) W =
      Dist.mix ((List.range 6).map fun rr => (A.getD rr 0, betaRegion (ℓ - 1) kids rr W)) := by
  rw [betaOf]
  rfl

namespace ANode

/-- The free `μ_T` of a positive level-2 node; zero elsewhere. -/
def mu : ANode → ℚ
  | .posTwo _ _ _ m => m
  | _ => 0

end ANode

/-- `π_r` for a zero-based region index (§5.1). -/
def permOf (r : ℕ) : Coordinate → Coordinate := (Region.all.getD r .r1).permute

/-- The minimum of the three coordinate candidates (A10, A15, A17, A20). -/
noncomputable def min3 (a b c : ℝ) : ℝ := min a (min b c)

namespace AInstance

/-- The `α^(r)` weights of the root's region-`r` children, in canonical order. -/
def rootAlphas (I : AInstance) (r : ℕ) : List ℚ := (I.kidsIn r).map ANode.alpha

/-- `E_G^(r)`, the root contribution for one region (A10). -/
noncomputable def eRootRegion (I : AInstance) (r : ℕ) : ℝ :=
  let kidsR := I.kidsIn r
  let w : ANode → ℚ := ANode.alpha
  let cX := permOf r .X
  let cY := permOf r .Y
  let cZ := permOf r .Z
  let bound := 2 ^ I.levels
  let z := alphaZip kidsR
  min3
    (hDist (Dist.push (fun s => AShape.coord s cX) z) - penalty z)
    (hDist (betaBar I.levels w kidsR cY) - etaY I.levels bound w kidsR cY cZ)
    (hDist (betaBar I.levels w kidsR cZ) - etaZ I.levels bound w kidsR cX cY cZ)

/-- `E_G = Σ_r A_G^(r) E_G^(r)` (A11). -/
noncomputable def eRoot (I : AInstance) : ℝ :=
  ((List.range 6).map fun r => ((I.A.getD r 0 : ℚ) : ℝ) * I.eRootRegion r).sum

/-- `E_(T,W)^(r)` of one positive interior node, at the three construction labels
`X`, `Y`, `Z` (A14). -/
noncomputable def eInteriorRegion (ℓ : ℕ) (m : ℚ) (s : AShape) (A : List ℚ)
    (kids : List ANode) (r : ℕ) : ℝ × ℝ × ℝ :=
  let kidsR := kids.filter fun k => k.region = r
  let w : ANode → ℚ := fun k =>
    alphaAt kids r k.shape + alphaAt kids r (AShape.sub s k.shape)
  let cX := permOf r .X
  let cY := permOf r .Y
  let cZ := permOf r .Z
  let scale := (m : ℝ) * ((A.getD r 0 : ℚ) : ℝ)
  let bound := 2 ^ ℓ
  let z := alphaZip kidsR
  (scale * (hDist (Dist.push (fun t => AShape.coord t cX) z) - penalty z),
   scale * (hDist (betaRegion (ℓ - 1) kids r cY) - etaY (ℓ - 1) bound w kidsR cY cZ),
   scale * (hDist (betaRegion (ℓ - 1) kids r cZ) -
     etaZ (ℓ - 1) bound w kidsR cX cY cZ))

/-- `E_ℓ` for one level at least three (A15). -/
noncomputable def eLevel (I : AInstance) (ℓ : ℕ) : ℝ :=
  ((List.range 6).map fun r =>
    let per := (I.posNodesAt ℓ).map fun t =>
      match t.2.2 with
      | .posBranch _ s _ A kids => eInteriorRegion ℓ t.2.1 s A kids r
      | _ => (0, 0, 0)
    min3 ((per.map fun p => p.1).sum) ((per.map fun p => p.2.1).sum)
      ((per.map fun p => p.2.2).sum)).sum

/-- `Σ_(T ∈ Trees_2^+) E_(T,W)` at one coordinate (A17). -/
noncomputable def eTwoSum (I : AInstance) (W : Coordinate) : ℝ :=
  (I.posTwoNodes.map fun t => levelTwoExponent t.2.1 t.2.2.shape t.2.2.mu W).sum

/-- `E_2` (A17). -/
noncomputable def eTwo (I : AInstance) : ℝ :=
  min3 (I.eTwoSum .X) (I.eTwoSum .Y) (I.eTwoSum .Z)

/-- `E_total = E_G + E_2 + Σ_(ℓ=3..ℓ*) E_ℓ` (A20). -/
noncomputable def eTotal (I : AInstance) : ℝ :=
  I.eRoot + I.eTwo +
    (((List.range (I.levels + 1)).filter fun ℓ => 3 ≤ ℓ).map I.eLevel).sum

/-- `Σ_(T ∈ Leaves) M_(T,W)` at one coordinate (A20). -/
noncomputable def mTotalSum (I : AInstance) (W : Coordinate) : ℝ :=
  (I.leaves.map fun t => localSize I.q t.1 t.2.1 t.2.2 W).sum

/-- `M_total`, the coordinate minimum of the summed local sizes (A20). -/
noncomputable def mTotal (I : AInstance) : ℝ :=
  min3 (I.mTotalSum .X) (I.mTotalSum .Y) (I.mTotalSum .Z)

/-- `2^(ℓ*-1) log2(q+2)`, the right-hand side of A21. -/
noncomputable def requirement (I : AInstance) : ℝ :=
  (2 : ℝ) ^ (I.levels - 1) * Real.logb 2 ((I.q : ℝ) + 2)

/-- The A21 inequality at value `Ω`. -/
def Feasible (I : AInstance) (Ω : ℝ) : Prop :=
  I.requirement ≤ I.eTotal + I.mTotal * Ω

end AInstance

end MatrixMath.Spec

namespace MatrixMath

/-- **The S1 combination-loss problem is feasible at `(q, ℓ*)` with value `Ω`**
(A.10).

This is the *cited* problem: the constraints are exactly A.1's tree, A.2's
domains, and the A21 inequality. Version 1's extra `Ω ≥ 0` restriction is **not**
part of it — §A.10 says that restriction only narrows the feasible set, and it
appears in `MatrixMath.Certificate` where the directed evaluator needs it, not
here. -/
def CombinationLossFeasible (q levels : ℕ) (Ω : ℝ) : Prop :=
  ∃ I : Spec.AInstance, I.q = q ∧ I.levels = levels ∧ I.WF ∧ I.Feasible Ω

end MatrixMath
