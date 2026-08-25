import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Canonical domains

Normative source: `docs/specs/0001_spec.md` §5.1–§5.3 and A.1.

The orderings here are normative, not conventional. §5.1 says no library
permutation order may be substituted implicitly, so the six regions are written
out literally and the fact that each is a bijection is proved rather than
assumed. §5.2 says a node is identified by its complete root-to-node path, so
`NodePath` carries the whole path and `level`, `shape`, and `region` are derived
from it.

This module mirrors `crates/mm-core` deliberately rather than sharing code with
it: §4.1 chooses independence over DRY, so a mistake in one is caught by the
other instead of duplicated.
-/

namespace MatrixMath.Spec

/-! ## Coordinates and regions (§5.1) -/

/-- A tensor coordinate. Coordinates are ordered `X < Y < Z` (§5.1). -/
inductive Coordinate where
  /-- The first coordinate. -/
  | X
  /-- The second coordinate. -/
  | Y
  /-- The third coordinate. -/
  | Z
  deriving DecidableEq, Repr

namespace Coordinate

/-- All coordinates in canonical `X < Y < Z` order. -/
def all : List Coordinate := [X, Y, Z]

/-- The zero-based index. -/
def index : Coordinate → Nat
  | X => 0
  | Y => 1
  | Z => 2

@[simp] theorem index_lt_three (c : Coordinate) : c.index < 3 := by
  cases c <;> simp [index]

theorem index_injective {a b : Coordinate} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

end Coordinate

/-- A region identifier in `1..=6` (§5.1). -/
inductive Region where
  /-- `(X,Y,Z)`. -/
  | r1
  /-- `(X,Z,Y)`. -/
  | r2
  /-- `(Y,X,Z)`. -/
  | r3
  /-- `(Y,Z,X)`. -/
  | r4
  /-- `(Z,X,Y)`. -/
  | r5
  /-- `(Z,Y,X)`. -/
  | r6
  deriving DecidableEq, Repr

namespace Region

/-- All six regions in canonical numeric order (§5.1). -/
def all : List Region := [r1, r2, r3, r4, r5, r6]

/-- The numeric identifier `1..=6`. -/
def id : Region → Nat
  | r1 => 1 | r2 => 2 | r3 => 3 | r4 => 4 | r5 => 5 | r6 => 6

/-- The normative permutation table of §5.1: `region ↦ (π(X), π(Y), π(Z))`.

Written out literally. §5.1 forbids substituting a library permutation order,
and a generated table would be exactly that substitution. -/
def permute : Region → Coordinate → Coordinate
  | r1, c => c
  | r2, .X => .X | r2, .Y => .Z | r2, .Z => .Y
  | r3, .X => .Y | r3, .Y => .X | r3, .Z => .Z
  | r4, .X => .Y | r4, .Y => .Z | r4, .Z => .X
  | r5, .X => .Z | r5, .Y => .X | r5, .Z => .Y
  | r6, .X => .Z | r6, .Y => .Y | r6, .Z => .X

/-- Every region acts as a bijection on the three coordinates. -/
theorem permute_injective (r : Region) {a b : Coordinate}
    (h : r.permute a = r.permute b) : a = b := by
  cases r <;> cases a <;> cases b <;> simp_all [permute]

/-- Every region's action is surjective, hence a permutation. -/
theorem permute_surjective (r : Region) (c : Coordinate) :
    ∃ a, r.permute a = c := by
  cases r <;> cases c <;>
    first
      | exact ⟨.X, rfl⟩
      | exact ⟨.Y, rfl⟩
      | exact ⟨.Z, rfl⟩

end Region

/-! ## Levels and shapes (§5.3, A.1) -/

/-- A recursion level in `2..=4` (§0.2). -/
structure Level where
  /-- The underlying value. -/
  value : Nat
  /-- Version 1 accepts `2 ≤ ℓ* ≤ 4` (§0.2). -/
  lower : 2 ≤ value
  /-- Version 1 accepts `2 ≤ ℓ* ≤ 4` (§0.2). -/
  upper : value ≤ 4
  deriving DecidableEq, Repr

namespace Level

/-- `2^ℓ`, the sum a level-`ℓ` shape's coordinates must reach (A.1). -/
def shapeSum (l : Level) : Nat := 2 ^ l.value

/-- `2^(ℓ-1)`, the support-vector length of `C_(ℓ,a)` (A.2). -/
def supportLen (l : Level) : Nat := 2 ^ (l.value - 1)

theorem shapeSum_pos (l : Level) : 0 < l.shapeSum := by
  unfold shapeSum
  positivity

theorem supportLen_pos (l : Level) : 0 < l.supportLen := by
  unfold supportLen
  positivity

/-- `2^ℓ = 2 * 2^(ℓ-1)` for every supported level. -/
theorem shapeSum_eq (l : Level) : l.shapeSum = 2 * l.supportLen := by
  unfold shapeSum supportLen
  obtain ⟨k, hk⟩ : ∃ k, l.value = k + 1 := ⟨l.value - 1, by have := l.lower; omega⟩
  rw [hk]
  simp [pow_succ]
  exact Nat.mul_comm _ _

end Level

/-- A level-`ℓ` shape `(x,y,z)` with `x + y + z = 2^ℓ` (A.1).

The invariant is carried by the structure, so no downstream definition re-checks
the sum (§5.3). -/
structure Shape (l : Level) where
  /-- The `X` coordinate. -/
  x : Nat
  /-- The `Y` coordinate. -/
  y : Nat
  /-- The `Z` coordinate. -/
  z : Nat
  /-- A.1: the coordinates sum to `2^ℓ`. -/
  sums : x + y + z = l.shapeSum
  deriving DecidableEq, Repr

namespace Shape

variable {l : Level}

/-- One coordinate of the shape. -/
def coord (s : Shape l) : Coordinate → Nat
  | .X => s.x
  | .Y => s.y
  | .Z => s.z

/-- A shape is positive when all three coordinates are positive (A.1). -/
def IsPositive (s : Shape l) : Prop := 0 < s.x ∧ 0 < s.y ∧ 0 < s.z

instance (s : Shape l) : Decidable s.IsPositive := by
  unfold IsPositive; infer_instance

/-- A shape is a zero-shape when some coordinate is zero (A.1). -/
def IsZeroShape (s : Shape l) : Prop := ¬ s.IsPositive

/-- The three coordinates always sum to the level total, whatever the order. -/
theorem coord_sum (s : Shape l) :
    s.coord .X + s.coord .Y + s.coord .Z = l.shapeSum := s.sums

/-- A positive shape has every coordinate at least one, so the level total is at
least three: there is no positive shape below level 2. -/
theorem three_le_shapeSum_of_positive (s : Shape l) (h : s.IsPositive) :
    3 ≤ l.shapeSum := by
  obtain ⟨hx, hy, hz⟩ := h
  have := s.sums
  omega

/-- A shape is either positive or a zero-shape, never both (A.1). -/
theorem positive_or_zero (s : Shape l) : s.IsPositive ∨ s.IsZeroShape := by
  unfold IsZeroShape
  exact em _

end Shape

/-! ## Node identity (§5.2) -/

/-- One step down the tree: the child's own shape and the region chosen (§5.2). -/
structure Step (l : Level) where
  /-- The node's own shape. At the root step this ranges over `S_ℓ*`; later it
  ranges over `Split(parent)`. -/
  shape : Shape l
  /-- The region chosen at this step. -/
  region : Region
  deriving DecidableEq, Repr

/-- The complete identity of a tree node (§5.2).

An empty step list denotes the root `G`. §5.2 is explicit that two nodes with the
same level, shape, and region but different ancestors are **distinct**, which is
why identity is the whole path rather than the last step. -/
structure NodePath (l : Level) where
  /-- The steps, root first. -/
  steps : List (Step l)
  deriving DecidableEq, Repr

namespace NodePath

variable {l : Level}

/-- The root path. -/
def root : NodePath l := ⟨[]⟩

/-- Whether this is the root. -/
def isRoot (p : NodePath l) : Bool := p.steps.isEmpty

/-- The node's own shape, or `none` at the root. -/
def shape (p : NodePath l) : Option (Shape l) := p.steps.getLast?.map Step.shape

/-- The node's region, or `none` at the root. -/
def region (p : NodePath l) : Option Region := p.steps.getLast?.map Step.region

/-- Extend a path by one step. -/
def child (p : NodePath l) (s : Step l) : NodePath l := ⟨p.steps ++ [s]⟩

@[simp] theorem root_isRoot : (root : NodePath l).isRoot = true := rfl

@[simp] theorem child_not_root (p : NodePath l) (s : Step l) :
    (p.child s).isRoot = false := by
  simp [child, isRoot]

/-- Distinct paths are distinct nodes, even when the last step agrees.

This is the §5.2 property that makes the whole path the identity: two nodes may
share level, shape, and region and still be different nodes. -/
theorem distinct_paths_same_last {p q : NodePath l} {s : Step l}
    (h : p ≠ q) : p.child s ≠ q.child s := by
  intro hc
  apply h
  have : p.steps ++ [s] = q.steps ++ [s] := congrArg NodePath.steps hc
  have hsteps := List.append_cancel_right this
  cases p; cases q; simp_all

/-- Extending is injective in the step too. -/
theorem child_injective {p : NodePath l} {s t : Step l}
    (h : p.child s = p.child t) : s = t := by
  have : p.steps ++ [s] = p.steps ++ [t] := congrArg NodePath.steps h
  have := List.append_cancel_left this
  simpa using this

end NodePath

end MatrixMath.Spec
