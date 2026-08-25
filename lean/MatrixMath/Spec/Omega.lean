import MatrixMath.Numeric.EntropyBounds
import MatrixMath.Spec.Basic
import MatrixMath.Spec.Entropy

/-!
# Appendix A quantities at `ℓ* = 2`

Normative source: `docs/specs/0001_spec.md` A.1–A.10.

This module states the Appendix A objective in Lean for `ℓ* = 2`, where the root's
children are all leaves and the interior recursion of A.7 does not arise. §3.4 is
explicit that a reduced Lean instance does not certify a larger Rust-checked one,
so the checker built on this rejects `ℓ* ≥ 3` rather than pretending.

## Why the split into exact and real is where it is

Every free variable is an exact rational, and so is every mass, weight, and split
distribution: A2, A4, and A7 involve no irrational quantity at all. The only real
numbers in Appendix A enter through `H(·)`, `log2 q`, and `H_D^max`. So each
retained exponent and local size has the shape

```text
Σ (exact rational weight) · H(exact rational distribution)  ±  (exact rational) · log2 q
```

which is exactly the shape the §7.2 directed rules bound. That is why the
soundness proof decomposes into the `Numeric` lemmas rather than needing new
analysis.
-/

namespace MatrixMath.Spec

open Finset MatrixMath.Numeric

/-! ## Level-2 domains -/

/-- `S_2`, the level-2 shapes, in canonical lexicographic order (§5.1, A.1). -/
def shapes2 : List (ℕ × ℕ × ℕ) :=
  [(0,0,4), (0,1,3), (0,2,2), (0,3,1), (0,4,0),
   (1,0,3), (1,1,2), (1,2,1), (1,3,0),
   (2,0,2), (2,1,1), (2,2,0),
   (3,0,1), (3,1,0),
   (4,0,0)]

theorem shapes2_length : shapes2.length = 15 := by decide

theorem shapes2_sums : ∀ s ∈ shapes2, s.1 + s.2.1 + s.2.2 = 4 := by decide

/-- `{0,1,2}^2`, the full level-2 support space, lexicographically.

A.6's mixtures combine `β` distributions whose totals differ, so they must share
an index set; this is it. -/
def support2 : List (ℕ × ℕ) :=
  [(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]

theorem support2_length : support2.length = 9 := by decide

/-- `C_(2,a)`, the support vectors summing to `a`, lexicographically (A.2). -/
def supportTotal2 (a : ℕ) : List (ℕ × ℕ) :=
  support2.filter (fun v => v.1 + v.2 = a)

/-- One coordinate of a shape, in `X < Y < Z` order (§5.1). -/
def coordOf (s : ℕ × ℕ × ℕ) : Coordinate → ℕ
  | .X => s.1
  | .Y => s.2.1
  | .Z => s.2.2

/-- The first coordinate whose shape entry is zero, if any (A.5 `W0`). -/
def firstZero (s : ℕ × ℕ × ℕ) : Option Coordinate :=
  if s.1 = 0 then some .X else if s.2.1 = 0 then some .Y
  else if s.2.2 = 0 then some .Z else none

/-- The first coordinate whose shape entry is positive, if any (A.5 `W1`). -/
def firstNonzero (s : ℕ × ℕ × ℕ) : Option Coordinate :=
  if s.1 ≠ 0 then some .X else if s.2.1 ≠ 0 then some .Y
  else if s.2.2 ≠ 0 then some .Z else none

/-- A shape is positive when all three coordinates are (A.1). -/
def isPositive (s : ℕ × ℕ × ℕ) : Bool := s.1 ≠ 0 && s.2.1 ≠ 0 && s.2.2 ≠ 0

/-! ## Certificate data (§6.5) -/

/-- The free variables of one level-2 leaf (A.2). -/
inductive LeafVars where
  /-- A positive level-2 node carries `μ_T ∈ [0, 1/2]`. -/
  | levelTwo (mu : ℚ)
  /-- A zero-shape node carries the free `β_(T,W1)` on `C_(2, s_(T,W1))`. -/
  | zeroShape (beta : List ℚ)
  deriving Repr, DecidableEq

/-- One maximum-entropy block (§7.4).

`λ_X`, `λ_Y`, and `λ_Z` are indexed by the ascending distinct coordinate values
of the domain, which at the root is `S_2`, so each has five entries for the
values `0..4`. -/
structure Block where
  /-- The strictly positive witness `y ∈ Δ(S_2)`. -/
  y : List ℚ
  /-- The additive constant `λ₀`. -/
  lambda0 : ℚ
  /-- `λ_X`, indexed by the coordinate values `0..4`. -/
  lambdaX : List ℚ
  /-- `λ_Y`, likewise. -/
  lambdaY : List ℚ
  /-- `λ_Z`, likewise. -/
  lambdaZ : List ℚ
  /-- The slack `ε ≥ 0`. -/
  epsilon : ℚ
  deriving Repr, DecidableEq

/-- A decoded `ℓ* = 2` omega certificate (§6.5). -/
structure OmegaData where
  /-- The instance parameter `q`. -/
  q : ℕ
  /-- `A_G ∈ Δ([6])`, six entries in region order. -/
  regionWeights : List ℚ
  /-- `α_G^(r) ∈ Δ(S_2)`, one list of fifteen per region. -/
  alpha : List (List ℚ)
  /-- The ninety leaves, region-major then shape-lexicographic (§5.2). -/
  leaves : List LeafVars
  /-- One block per region, for `P_(S_2)(α_G^(r))` (§6.5). -/
  blocks : List Block
  /-- The claimed nonnegative rational `Ω`. -/
  omega : ℚ
  deriving Repr

/-- The leaf at region `r` (one-based) and shape index `i` (§5.2). -/
def OmegaData.leafAt (d : OmegaData) (r i : ℕ) : Option LeafVars :=
  d.leaves[(r - 1) * 15 + i]?

/-- `α_G^(r)(s)` at region `r` (one-based) and shape index `i` (A.2). -/
def OmegaData.alphaAt (d : OmegaData) (r i : ℕ) : ℚ :=
  match d.alpha[r - 1]? with
  | none => 0
  | some row => row.getD i 0

/-- `A_G^(r)` at region `r` (one-based) (A.2). -/
def OmegaData.regionWeight (d : OmegaData) (r : ℕ) : ℚ :=
  d.regionWeights.getD (r - 1) 0

/-- `m_(G[s,r]) = A_G^(r) α_G^(r)(s)` (A2).

`m_G = 1`, so the root contributes no factor of its own. -/
def OmegaData.mass (d : OmegaData) (r i : ℕ) : ℚ :=
  d.regionWeight r * d.alphaAt r i

/-! ## Split distributions (A4, A7)

Every `β` here is an exact rational distribution on `support2`, so nothing in
this section is approximate. -/

/-- `β_(T,W)` of a positive level-2 node (A7).

The `μ` distribution sits on the coordinate whose shape entry is two; the other
two coordinates carry the half/half distribution. -/
def betaLevelTwo (s : ℕ × ℕ × ℕ) (mu : ℚ) (w : Coordinate) : List ℚ :=
  if coordOf s w = 2 then
    support2.map fun v =>
      if v = (0,2) || v = (2,0) then mu else if v = (1,1) then 1 - 2 * mu else 0
  else
    support2.map fun v => if v = (0,1) || v = (1,0) then 1/2 else 0

/-- `β_(T,W)` of a zero-shape level-2 node (A4).

`β_(T,W0)` is the point mass at `0⃗`; `β_(T,W1)` is the free distribution laid
onto `C_(2, s_(T,W1))`; and `β_(T,W2) = β_(T,W1)^∨` with `β^∨(2⃗-L) = β(L)`. -/
def betaZeroShape (s : ℕ × ℕ × ℕ) (free : List ℚ) (w : Coordinate) : List ℚ :=
  match firstZero s, firstNonzero s with
  | some w0, some w1 =>
    let onFree : List ℚ :=
      let domain := supportTotal2 (coordOf s w1)
      support2.map fun v =>
        match domain.idxOf? v with
        | some k => free.getD k 0
        | none => 0
    if w = w0 then support2.map fun v => if v = (0,0) then 1 else 0
    else if w = w1 then onFree
    else
      -- β^∨(2⃗ - L) = β(L): read the entry at the complementary vector.
      support2.map fun v =>
        match support2.idxOf? (2 - v.1, 2 - v.2) with
        | some k => onFree.getD k 0
        | none => 0
  | _, _ => support2.map fun _ => 0

/-- `β_(T,W)` of any level-2 leaf. -/
def leafBeta (s : ℕ × ℕ × ℕ) (vars : LeafVars) (w : Coordinate) : List ℚ :=
  match vars with
  | .levelTwo mu => betaLevelTwo s mu w
  | .zeroShape free => betaZeroShape s free w

end MatrixMath.Spec

namespace MatrixMath.Spec

open MatrixMath.Numeric

/-! ## Entropy over a rational list

Appendix A's distributions are lists of exact rationals, so the `Numeric` bounds
are lifted to lists here. Every proof below is a list induction on
`entropyTermLower_le` / `le_entropyTermUpper`; no new analysis is involved.
-/

/-- `H(p)` for a rational distribution given as a list (A.3). -/
noncomputable def hReal (p : List ℚ) : ℝ :=
  (p.map fun v => entropyTerm ((v : ℚ) : ℝ)).sum

/-- A value known to be at most `H(p)` (§7.2). -/
def hLower (p : List ℚ) (n : ℕ) : ℚ := (p.map fun v => entropyTermLower v n).sum

/-- A value known to be at least `H(p)` (§7.2). -/
def hUpper (p : List ℚ) (n : ℕ) : ℚ := (p.map fun v => entropyTermUpper v n).sum

theorem hLower_le {p : List ℚ} (hp : ∀ v ∈ p, 0 ≤ v) (n : ℕ) :
    ((hLower p n : ℚ) : ℝ) ≤ hReal p := by
  unfold hLower hReal
  induction p with
  | nil => simp
  | cons a rest ih =>
      have ha : (0 : ℚ) ≤ a := hp a (by simp)
      have hrest : ∀ v ∈ rest, 0 ≤ v := fun v hv => hp v (by simp [hv])
      have := entropyTermLower_le ha n
      simp only [List.map_cons, List.sum_cons]
      push_cast
      have := ih hrest
      push_cast at this
      linarith [entropyTermLower_le ha n]

theorem le_hUpper {p : List ℚ} (hp : ∀ v ∈ p, 0 ≤ v) (n : ℕ) :
    hReal p ≤ ((hUpper p n : ℚ) : ℝ) := by
  unfold hUpper hReal
  induction p with
  | nil => simp
  | cons a rest ih =>
      have ha : (0 : ℚ) ≤ a := hp a (by simp)
      have hrest : ∀ v ∈ rest, 0 ≤ v := fun v hv => hp v (by simp [hv])
      simp only [List.map_cons, List.sum_cons]
      push_cast
      have := ih hrest
      push_cast at this
      linarith [le_entropyTermUpper ha n]

/-- A nonnegatively weighted sum of entropies (A.6, A.8, A.9). -/
noncomputable def weightedHReal (terms : List (ℚ × List ℚ)) : ℝ :=
  (terms.map fun t => ((t.1 : ℚ) : ℝ) * hReal t.2).sum

/-- The directed lower bound of a nonnegatively weighted sum of entropies (§7.2). -/
def weightedHLower (terms : List (ℚ × List ℚ)) (n : ℕ) : ℚ :=
  (terms.map fun t => t.1 * hLower t.2 n).sum

/-- The directed upper bound of a nonnegatively weighted sum of entropies (§7.2). -/
def weightedHUpper (terms : List (ℚ × List ℚ)) (n : ℕ) : ℚ :=
  (terms.map fun t => t.1 * hUpper t.2 n).sum

theorem weightedHLower_le {terms : List (ℚ × List ℚ)}
    (hw : ∀ t ∈ terms, 0 ≤ t.1) (hp : ∀ t ∈ terms, ∀ v ∈ t.2, 0 ≤ v) (n : ℕ) :
    ((weightedHLower terms n : ℚ) : ℝ) ≤ weightedHReal terms := by
  unfold weightedHLower weightedHReal
  induction terms with
  | nil => simp
  | cons t rest ih =>
      have hw0 : (0 : ℚ) ≤ t.1 := hw t (by simp)
      have hp0 : ∀ v ∈ t.2, 0 ≤ v := hp t (by simp)
      have hwr : ∀ u ∈ rest, 0 ≤ u.1 := fun u hu => hw u (by simp [hu])
      have hpr : ∀ u ∈ rest, ∀ v ∈ u.2, 0 ≤ v := fun u hu => hp u (by simp [hu])
      have hstep : ((t.1 * hLower t.2 n : ℚ) : ℝ) ≤ ((t.1 : ℚ) : ℝ) * hReal t.2 := by
        push_cast
        have hw0' : (0 : ℝ) ≤ ((t.1 : ℚ) : ℝ) := by exact_mod_cast hw0
        exact mul_le_mul_of_nonneg_left (hLower_le hp0 n) hw0'
      simp only [List.map_cons, List.sum_cons]
      push_cast
      have := ih hwr hpr
      push_cast at this
      push_cast at hstep
      linarith

theorem le_weightedHUpper {terms : List (ℚ × List ℚ)}
    (hw : ∀ t ∈ terms, 0 ≤ t.1) (hp : ∀ t ∈ terms, ∀ v ∈ t.2, 0 ≤ v) (n : ℕ) :
    weightedHReal terms ≤ ((weightedHUpper terms n : ℚ) : ℝ) := by
  unfold weightedHUpper weightedHReal
  induction terms with
  | nil => simp
  | cons t rest ih =>
      have hw0 : (0 : ℚ) ≤ t.1 := hw t (by simp)
      have hp0 : ∀ v ∈ t.2, 0 ≤ v := hp t (by simp)
      have hwr : ∀ u ∈ rest, 0 ≤ u.1 := fun u hu => hw u (by simp [hu])
      have hpr : ∀ u ∈ rest, ∀ v ∈ u.2, 0 ≤ v := fun u hu => hp u (by simp [hu])
      have hstep : ((t.1 : ℚ) : ℝ) * hReal t.2 ≤ ((t.1 * hUpper t.2 n : ℚ) : ℝ) := by
        push_cast
        have hw0' : (0 : ℝ) ≤ ((t.1 : ℚ) : ℝ) := by exact_mod_cast hw0
        exact mul_le_mul_of_nonneg_left (le_hUpper hp0 n) hw0'
      simp only [List.map_cons, List.sum_cons]
      push_cast
      have := ih hwr hpr
      push_cast at this
      push_cast at hstep
      linarith

end MatrixMath.Spec

namespace MatrixMath.Spec

open Finset MatrixMath.Numeric

/-! ## The maximum entropy `H_D^max` (A1, A.11)

`H_D^max(ρ)` is a genuine supremum over the distributions matching `ρ`'s three
marginals, defined here as such rather than as "whatever the certificate says".
A block bounds it above; A22 is what turns the block's data into that bound.
-/

/-- The set of distributions on `Finset.range n` matching `ρ`'s three marginals,
where the coordinate maps are given by `key` applied to the index (A1). -/
def FeasibleSet (n : ℕ) (kx ky kz : ℕ → ℕ) (rho : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {p | IsDistribution (range n) p ∧ SameMarginal (range n) kx rho p
        ∧ SameMarginal (range n) ky rho p ∧ SameMarginal (range n) kz rho p}

/-- `H_D^max(ρ)`, the supremum of A1. -/
noncomputable def hMaxOf (n : ℕ) (kx ky kz : ℕ → ℕ) (rho : ℕ → ℝ) : ℝ :=
  sSup ((fun p => entropy (range n) p) '' FeasibleSet n kx ky kz rho)

/-- `ρ` is feasible for itself, so the supremum is over a nonempty set. -/
theorem rho_mem_feasible {n : ℕ} {kx ky kz : ℕ → ℕ} {rho : ℕ → ℝ}
    (h : IsDistribution (range n) rho) : rho ∈ FeasibleSet n kx ky kz rho := by
  refine ⟨h, ?_, ?_, ?_⟩ <;> intro v <;> rfl

/-- **A block bounds the maximum entropy** (A1, A22).

Given that every feasible distribution has entropy at most `bound`, so does the
supremum. This is the step that turns A22 — a statement about one distribution at
a time — into a statement about `H_D^max`. -/
theorem hMaxOf_le {n : ℕ} {kx ky kz : ℕ → ℕ} {rho : ℕ → ℝ} {bound : ℝ}
    (hrho : IsDistribution (range n) rho)
    (h : ∀ p ∈ FeasibleSet n kx ky kz rho, entropy (range n) p ≤ bound) :
    hMaxOf n kx ky kz rho ≤ bound := by
  refine csSup_le ⟨_, ⟨rho, rho_mem_feasible hrho, rfl⟩⟩ ?_
  rintro x ⟨p, hp, rfl⟩
  exact h p hp

/-- `H(ρ) ≤ H_D^max(ρ)`: the witness is feasible for itself (A1). -/
theorem le_hMaxOf {n : ℕ} {kx ky kz : ℕ → ℕ} {rho : ℕ → ℝ} {bound : ℝ}
    (hrho : IsDistribution (range n) rho)
    (h : ∀ p ∈ FeasibleSet n kx ky kz rho, entropy (range n) p ≤ bound) :
    entropy (range n) rho ≤ hMaxOf n kx ky kz rho := by
  refine le_csSup ⟨bound, ?_⟩ ⟨rho, rho_mem_feasible hrho, rfl⟩
  rintro x ⟨p, hp, rfl⟩
  exact h p hp

end MatrixMath.Spec

namespace MatrixMath.Spec

open Finset MatrixMath.Numeric

/-! ## Quantities of the Appendix A shape

Every local size and level-2 exponent has the same shape: a nonnegatively
weighted sum of entropies, plus a nonnegative multiple of `log2 q`, plus an exact
rational constant. Capturing that shape once means each of A16, A18, and A19
needs a builder rather than a proof.
-/

/-- A quantity of the Appendix A shape. -/
structure Quantity where
  /-- Nonnegatively weighted entropy terms. -/
  terms : List (ℚ × List ℚ)
  /-- A nonnegative multiple of `log2 q`. -/
  logCoeff : ℚ
  /-- An exact rational constant. -/
  const : ℚ

/-- The real value of a quantity. -/
noncomputable def Quantity.real (Q : Quantity) (q : ℕ) : ℝ :=
  weightedHReal Q.terms + (Q.logCoeff : ℝ) * Real.logb 2 (q : ℝ) + (Q.const : ℝ)

/-- A value known to be at most the quantity (§7.2). -/
def Quantity.lower (Q : Quantity) (q : ℕ) (n : ℕ) : ℚ :=
  weightedHLower Q.terms n + Q.logCoeff * log2Lower (q : ℚ) n + Q.const

/-- Well-formedness: nonnegative weights, nonnegative probabilities, and a
nonnegative `log2 q` coefficient. §7.2's monotonic shortcut needs all three. -/
def Quantity.Valid (Q : Quantity) : Prop :=
  (∀ t ∈ Q.terms, 0 ≤ t.1) ∧ (∀ t ∈ Q.terms, ∀ v ∈ t.2, 0 ≤ v) ∧ 0 ≤ Q.logCoeff

theorem Quantity.lower_le {Q : Quantity} (hQ : Q.Valid) {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ((Q.lower q n : ℚ) : ℝ) ≤ Q.real q := by
  obtain ⟨hw, hp, hlog⟩ := hQ
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hlogbound := log2Lower_le hqpos n
  have hlog' : (0 : ℝ) ≤ ((Q.logCoeff : ℚ) : ℝ) := by exact_mod_cast hlog
  have hentropy := weightedHLower_le hw hp n
  have hscaled :
      ((Q.logCoeff : ℚ) : ℝ) * ((log2Lower (q : ℚ) n : ℚ) : ℝ)
        ≤ ((Q.logCoeff : ℚ) : ℝ) * Real.logb 2 ((q : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlogbound hlog'
  unfold Quantity.lower Quantity.real
  push_cast
  push_cast at hentropy hscaled
  linarith

end MatrixMath.Spec

namespace MatrixMath.Spec

open Finset MatrixMath.Numeric

/-- **A valid §7.4 block bounds `H_D^max`** (A1, A22).

Every distribution feasible for `ρ` shares `ρ`'s marginals, hence `y`'s, hence
gives the additive `g` the same expectation as `y` does. A22 then bounds its
entropy by `H(y) + 2ε`, and taking the supremum gives the result.

This is the whole content of §7.4: the four conditions it lists are exactly the
hypotheses below. -/
theorem hMaxOf_le_of_block {n : ℕ} {kx ky kz : ℕ → ℕ} {t : Finset ℕ}
    (hkx : ∀ a ∈ range n, kx a ∈ t) (hky : ∀ a ∈ range n, ky a ∈ t)
    (hkz : ∀ a ∈ range n, kz a ∈ t)
    {rho y : ℕ → ℝ} {l0 : ℝ} {lx ly lz : ℕ → ℝ} {ε : ℝ}
    (hyPos : ∀ a ∈ range n, 0 < y a)
    (hySum : ∑ a ∈ range n, y a = 1)
    (hRho : IsDistribution (range n) rho)
    (hmx : SameMarginal (range n) kx rho y)
    (hmy : SameMarginal (range n) ky rho y)
    (hmz : SameMarginal (range n) kz rho y)
    (hClose : ∀ a ∈ range n,
      |Real.logb 2 (y a) - (l0 + lx (kx a) + ly (ky a) + lz (kz a))| ≤ ε) :
    hMaxOf n kx ky kz rho ≤ entropy (range n) y + 2 * ε := by
  refine hMaxOf_le hRho ?_
  rintro p ⟨hpDist, hpx, hpy, hpz⟩
  -- p shares rho's marginals, and so does y, so p and y share each other's.
  have hexp :
      ∑ a ∈ range n, p a * (l0 + lx (kx a) + ly (ky a) + lz (kz a))
        = ∑ a ∈ range n, y a * (l0 + lx (kx a) + ly (ky a) + lz (kz a)) := by
    refine sum_additive_of_marginals hkx hky hkz l0 lx ly lz p y ?_ ?_ ?_ ?_
    · rw [hpDist.2, hySum]
    · intro v; rw [← hpx v, hmx v]
    · intro v; rw [← hpy v, hmy v]
    · intro v; rw [← hpz v, hmz v]
  exact entropy_le_of_close hyPos hySum hpDist.1 hpDist.2 hexp hClose

end MatrixMath.Spec
