import MatrixMath.Certificate.Omega
import MatrixMath.Spec.Omega

/-!
# The Track A checker and its soundness

Normative source: `docs/specs/0001_spec.md` §7.2, §7.4, A.1–A.10.

`MatrixMath.Spec.AInstance` writes down the Appendix A problem; this module
decides a **rational, directed** sufficient condition for a given instance to be
feasible, and proves that deciding it establishes feasibility of the real problem.

Composing that with `AX1_combination_loss` yields `ω ≤ Ω` with no residual
hypothesis: feasibility of the cited A.10 problem is *proved* here rather than
assumed.

## Scope

`check` covers every `ℓ*` the specification admits. The root contribution
(A10, A11), the level-2 exponent (A16, A17), and the local sizes (A18–A20) are
bounded directly; the interior levels (A12–A15) recurse through
`eInteriorRegionLower`, and `blockOffset` assigns each §7.4 block to the node and
region that A.10's level-by-level sum consumes it at — an order that is *not* the
preorder once `ℓ* ≥ 4`.

Nothing here assumes a size. What a given `ℓ*` costs to decide is a separate
question, answered by running it.

## Where each bound comes from

The real objective is a sum of `H(·)` terms, `log2 q` multiples, exact rationals,
and — through `P_D` — one supremum `H_D^max` per region. The first three are
bounded by the §7.3 constructions in `MatrixMath.Numeric`. The supremum is
bounded by A22 through the §7.4 blocks the certificate carries, which is why
`Block` is part of the checker's input and not an afterthought.
-/

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## Reading a list as a function on `Finset.range` -/

/-- A `Finset.range` sum of a list's entries is the list's mapped sum, provided
the padding value contributes nothing. -/
theorem sum_range_getD {α : Type*} {β : Type*} [AddCommMonoid β]
    (l : List α) (d : α) (f : α → β) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.sum_cons]
    rw [ih]
    exact add_comm _ _

/-- `H` of a list, read as a distribution on `Finset.range`. -/
theorem entropy_range_eq_hReal (l : List ℚ) :
    entropy (Finset.range l.length) (fun i => ((l.getD i 0 : ℚ) : ℝ)) = hReal l := by
  unfold entropy hReal
  exact sum_range_getD l 0 fun v => entropyTerm ((v : ℚ) : ℝ)

/-- Casting commutes with a list sum. -/
theorem cast_list_sum (l : List ℚ) :
    (l.map fun v => ((v : ℚ) : ℝ)).sum = ((l.sum : ℚ) : ℝ) := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.sum_cons, List.sum_cons, Rat.cast_add, ih]

/-- A `Finset.range` sum of rationals read out of a list. -/
theorem sum_range_getD_rat (l : List ℚ) :
    ∑ i ∈ Finset.range l.length, ((l.getD i 0 : ℚ) : ℝ) = ((l.sum : ℚ) : ℝ) := by
  rw [sum_range_getD l 0 fun v => ((v : ℚ) : ℝ)]
  exact cast_list_sum l

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## `Finset.range` sums as list sums -/

/-- A `Finset.range` sum is the sum of the mapped `List.range`. -/
theorem sum_range_eq_list {β : Type*} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

/-- Casting commutes with a mapped list sum. -/
theorem cast_list_sum_map {α : Type*} (l : List α) (f : α → ℚ) :
    (l.map fun x => ((f x : ℚ) : ℝ)).sum = (((l.map f).sum : ℚ) : ℝ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Rat.cast_add, ih]

/-! ## Maximum-entropy blocks (§7.4, A22) -/

/-- The ascending distinct values a coordinate takes on a domain (§7.4).

§7.4 indexes `λ_W` by these, not by the raw coordinate value. The two coincide
on `S_ℓ*`, where every value from zero to `2^ℓ*` occurs, and differ on a
`Split(s_T)` domain — which is exactly where an implementation that assumed they
were the same would start reading the wrong entry. -/
def coordValues (z : Spec.Dist AShape) (c : Coordinate) : List ℕ :=
  (List.range 17).filter fun v => z.any fun p => AShape.coord p.1 c = v

/-- The position of a coordinate value among the domain's distinct values. -/
def coordIndex (z : Spec.Dist AShape) (c : Coordinate) (v : ℕ) : ℕ :=
  (coordValues z c).idxOf v

/-- One `λ_W` entry, read at the position §7.4 assigns it. -/
def lambdaOf (blk : Block) (z : Spec.Dist AShape) (c : Coordinate) (v : ℕ) : ℚ :=
  (match c with
    | .X => blk.lambdaX
    | .Y => blk.lambdaY
    | .Z => blk.lambdaZ).getD (coordIndex z c v) 0

/-- `g(a) = λ₀ + λ_X(a_X) + λ_Y(a_Y) + λ_Z(a_Z)` (A.11). -/
def blockG (blk : Block) (z : Spec.Dist AShape) (s : AShape) : ℚ :=
  blk.lambda0 + lambdaOf blk z .X (AShape.coord s .X) +
    lambdaOf blk z .Y (AShape.coord s .Y) + lambdaOf blk z .Z (AShape.coord s .Z)

/-- One coordinate marginal of a weight list laid over a shape domain (A.3). -/
def marginalIdx (z : Spec.Dist AShape) (vals : List ℚ) (c : Coordinate) (v : ℕ) : ℚ :=
  ((List.range z.length).map fun a =>
    if AShape.coord (z.getD a padShape).1 c = v then vals.getD a 0 else 0).sum

/-- The rational marginal is the real fibre sum. -/
theorem marginal_bridge (z : Spec.Dist AShape) (vals : List ℚ) (c : Coordinate) (v : ℕ) :
    ∑ a ∈ (Finset.range z.length).filter
        (fun a => AShape.coord (z.getD a padShape).1 c = v),
      ((vals.getD a 0 : ℚ) : ℝ) = ((marginalIdx z vals c v : ℚ) : ℝ) := by
  rw [Finset.sum_filter, sum_range_eq_list]
  unfold marginalIdx
  rw [← cast_list_sum_map]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  split <;> simp

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-- Reading the weight column agrees with reading the pair and projecting. -/
theorem getD_map_snd (z : Spec.Dist AShape) (a : ℕ) :
    (z.map Prod.snd).getD a 0 = (z.getD a padShape).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : z[a]? <;> simp [padShape]

/-- An in-range read lands in the list. -/
theorem getD_mem {α : Type*} {z : List α} {a : ℕ} (h : a < z.length) (d : α) :
    z.getD a d ∈ z := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- **A §7.4 block, checked** (§7.4, A.11).

Every condition A.11 requires of a valid block appears here, and the closeness
condition is checked through the §7.3 directed logarithm bounds rather than by
evaluating a real logarithm. -/
def blockOk (prec : ℕ) (z : Spec.Dist AShape) (blk : Block) : Bool :=
  decide (blk.y.length = z.length) &&
    decide (0 ≤ blk.epsilon) &&
    blk.y.all (fun v => decide (0 < v)) &&
    decide (blk.y.sum = 1) &&
    z.all (fun p => decide (0 ≤ p.2)) &&
    decide ((z.map Prod.snd).sum = 1) &&
    z.all (fun p => decide (AShape.coord p.1 .X < 17) &&
      decide (AShape.coord p.1 .Y < 17) && decide (AShape.coord p.1 .Z < 17)) &&
    decide (blk.lambdaX.length = (coordValues z .X).length) &&
    decide (blk.lambdaY.length = (coordValues z .Y).length) &&
    decide (blk.lambdaZ.length = (coordValues z .Z).length) &&
    ((List.range 17).all fun v =>
      decide (marginalIdx z (z.map Prod.snd) .X v = marginalIdx z blk.y .X v) &&
      decide (marginalIdx z (z.map Prod.snd) .Y v = marginalIdx z blk.y .Y v) &&
      decide (marginalIdx z (z.map Prod.snd) .Z v = marginalIdx z blk.y .Z v)) &&
    ((List.range z.length).all fun a =>
      decide (blockG blk z (z.getD a padShape).1 - blk.epsilon
        ≤ log2Lower (blk.y.getD a 0) prec) &&
      decide (log2Upper (blk.y.getD a 0) prec
        ≤ blockG blk z (z.getD a padShape).1 + blk.epsilon))

/-- A rational upper bound for `P_D(ρ)` supplied by a block (§7.4, A22). -/
def penaltyUpper (prec : ℕ) (z : Spec.Dist AShape) (blk : Block) : ℚ :=
  hUpper blk.y prec + 2 * blk.epsilon - hLower (z.map Prod.snd) prec

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-- **A checked block bounds the penalty** (§7.4, A22).

This is the only place a supremum is discharged. Everything else in Track A is a
weighted sum of entropies of *explicit* rational distributions; `H_D^max` is not,
and A22 is what replaces it by something a certificate can carry. -/
theorem penalty_le_of_blockOk {prec : ℕ} {z : Spec.Dist AShape} {blk : Block}
    (h : blockOk prec z blk = true) :
    penalty z ≤ ((penaltyUpper prec z blk : ℚ) : ℝ) := by
  simp only [blockOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, heps⟩, hypos⟩, hysum⟩, hrnn⟩, hrsum⟩, hcoord⟩, _hlx⟩, _hly⟩,
    _hlz⟩, hmarg⟩, hclose⟩ := h
  have hypos' : ∀ v ∈ blk.y, 0 < v := hypos
  have hrnn' : ∀ p ∈ z, 0 ≤ p.2 := hrnn
  have hcoord' : ∀ p ∈ z, AShape.coord p.1 .X < 17 ∧ AShape.coord p.1 .Y < 17 ∧
      AShape.coord p.1 .Z < 17 := fun p hp => by
    have hp' := hcoord p hp
    exact ⟨hp'.1.1, hp'.1.2, hp'.2⟩
  -- The three coordinate maps and the two distributions, as functions on indices.
  set kx : ℕ → ℕ := fun a => AShape.coord (z.getD a padShape).1 .X with hkxdef
  set ky : ℕ → ℕ := fun a => AShape.coord (z.getD a padShape).1 .Y with hkydef
  set kz : ℕ → ℕ := fun a => AShape.coord (z.getD a padShape).1 .Z with hkzdef
  set rho : ℕ → ℝ := fun a => (((z.getD a padShape).2 : ℚ) : ℝ) with hrhodef
  set y : ℕ → ℝ := fun a => ((blk.y.getD a 0 : ℚ) : ℝ) with hydef
  have hrho_eq : ∀ a, rho a = (((z.map Prod.snd).getD a 0 : ℚ) : ℝ) := by
    intro a; rw [hrhodef, getD_map_snd]
  -- Each coordinate value of an in-range shape is below five.
  have hkxmem : ∀ a ∈ Finset.range z.length, kx a ∈ Finset.range 17 := by
    intro a ha
    simp only [Finset.mem_range] at ha ⊢
    exact (hcoord' _ (getD_mem ha padShape)).1
  have hkymem : ∀ a ∈ Finset.range z.length, ky a ∈ Finset.range 17 := by
    intro a ha
    simp only [Finset.mem_range] at ha ⊢
    exact (hcoord' _ (getD_mem ha padShape)).2.1
  have hkzmem : ∀ a ∈ Finset.range z.length, kz a ∈ Finset.range 17 := by
    intro a ha
    simp only [Finset.mem_range] at ha ⊢
    exact (hcoord' _ (getD_mem ha padShape)).2.2
  -- `y` is a strictly positive distribution.
  have hyPos : ∀ a ∈ Finset.range z.length, 0 < y a := by
    intro a ha
    simp only [Finset.mem_range] at ha
    have : blk.y.getD a 0 ∈ blk.y := getD_mem (by omega) 0
    have hp := hypos' _ this
    simp only [hydef]
    exact_mod_cast hp
  have hySum : ∑ a ∈ Finset.range z.length, y a = 1 := by
    rw [hydef, ← hlen, sum_range_getD_rat blk.y, hysum]
    norm_num
  have hRho : IsDistribution (Finset.range z.length) rho := by
    constructor
    · intro a ha
      simp only [Finset.mem_range] at ha
      have hp := hrnn' _ (getD_mem ha padShape)
      simp only [hrhodef]
      exact_mod_cast hp
    · have : ∑ a ∈ Finset.range z.length, rho a
          = ∑ a ∈ Finset.range (z.map Prod.snd).length,
              (((z.map Prod.snd).getD a 0 : ℚ) : ℝ) := by
        rw [List.length_map]
        exact Finset.sum_congr rfl fun a _ => hrho_eq a
      rw [this, sum_range_getD_rat, hrsum]
      norm_num
  -- Marginal equality, first for the checked values and then trivially beyond.
  have hmarg' : ∀ (k : ℕ → ℕ) (c : Coordinate),
      (k = fun a => AShape.coord (z.getD a padShape).1 c) →
      (∀ v, v < 17 → marginalIdx z (z.map Prod.snd) c v = marginalIdx z blk.y c v) →
      (∀ a ∈ Finset.range z.length, k a ∈ Finset.range 17) →
      SameMarginal (Finset.range z.length) k rho y := by
    intro k c hkc hcheck _ v
    subst hkc
    have hL : ∑ a ∈ (Finset.range z.length).filter
        (fun a => AShape.coord (z.getD a padShape).1 c = v), rho a
        = ((marginalIdx z (z.map Prod.snd) c v : ℚ) : ℝ) := by
      rw [← marginal_bridge z (z.map Prod.snd) c v]
      exact Finset.sum_congr rfl fun a _ => hrho_eq a
    have hR : ∑ a ∈ (Finset.range z.length).filter
        (fun a => AShape.coord (z.getD a padShape).1 c = v), y a
        = ((marginalIdx z blk.y c v : ℚ) : ℝ) := by
      rw [← marginal_bridge z blk.y c v]
    rw [hL, hR]
    by_cases hv : v < 17
    · rw [hcheck v hv]
    · -- No shape in the domain has a coordinate value this large.
      have hempty : ∀ a, a < z.length → AShape.coord (z.getD a padShape).1 c ≠ v := by
        intro a ha
        obtain ⟨h1, h2, h3⟩ := hcoord' _ (getD_mem ha padShape)
        simp only [AShape.coord] at h1 h2 h3
        cases c <;> simp only [AShape.coord] <;> omega
      have hzero : ∀ (vals : List ℚ), marginalIdx z vals c v = 0 := by
        intro vals
        unfold marginalIdx
        have : ((List.range z.length).map fun a =>
            if AShape.coord (z.getD a padShape).1 c = v then vals.getD a 0 else 0)
            = (List.range z.length).map fun _ => (0 : ℚ) :=
          List.map_congr_left fun a hain => by
            rw [if_neg (hempty a (List.mem_range.mp hain))]
        rw [this]
        simp
      rw [hzero, hzero]
  have hmx := hmarg' kx .X hkxdef (fun v hv => (hmarg v hv).1.1) hkxmem
  have hmy := hmarg' ky .Y hkydef (fun v hv => (hmarg v hv).1.2) hkymem
  have hmz := hmarg' kz .Z hkzdef (fun v hv => (hmarg v hv).2) hkzmem
  -- Closeness, through the §7.3 directed logarithm bounds.
  have hClose : ∀ a ∈ Finset.range z.length,
      |Real.logb 2 (y a) - (((blk.lambda0 : ℚ) : ℝ) +
        ((lambdaOf blk z .X (kx a) : ℚ) : ℝ) + ((lambdaOf blk z .Y (ky a) : ℚ) : ℝ) +
        ((lambdaOf blk z .Z (kz a) : ℚ) : ℝ))| ≤ ((blk.epsilon : ℚ) : ℝ) := by
    intro a ha
    simp only [Finset.mem_range] at ha
    have hpos : (0 : ℚ) < blk.y.getD a 0 := hypos' _ (getD_mem (by omega) 0)
    have hlow := log2Lower_le hpos prec
    have hhigh := le_log2Upper hpos prec
    obtain ⟨hc1, hc2⟩ := hclose a ha
    have hc1' : ((blockG blk z (z.getD a padShape).1 - blk.epsilon : ℚ) : ℝ)
        ≤ ((log2Lower (blk.y.getD a 0) prec : ℚ) : ℝ) := by exact_mod_cast hc1
    have hc2' : ((log2Upper (blk.y.getD a 0) prec : ℚ) : ℝ)
        ≤ ((blockG blk z (z.getD a padShape).1 + blk.epsilon : ℚ) : ℝ) := by exact_mod_cast hc2
    have hg : ((blk.lambda0 : ℚ) : ℝ) + ((lambdaOf blk z .X (kx a) : ℚ) : ℝ) +
        ((lambdaOf blk z .Y (ky a) : ℚ) : ℝ) + ((lambdaOf blk z .Z (kz a) : ℚ) : ℝ)
        = ((blockG blk z (z.getD a padShape).1 : ℚ) : ℝ) := by
      unfold blockG
      push_cast
      ring
    rw [hg, abs_le]
    simp only [hydef]
    push_cast at hc1' hc2' ⊢
    constructor <;> linarith
  -- A22, then the two directed entropy bounds.
  have hmax := hMaxOf_le_of_block (t := Finset.range 17)
    (l0 := ((blk.lambda0 : ℚ) : ℝ))
    (lx := fun v => ((lambdaOf blk z .X v : ℚ) : ℝ))
    (ly := fun v => ((lambdaOf blk z .Y v : ℚ) : ℝ))
    (lz := fun v => ((lambdaOf blk z .Z v : ℚ) : ℝ))
    (ε := ((blk.epsilon : ℚ) : ℝ))
    hkxmem hkymem hkzmem hyPos hySum hRho hmx hmy hmz hClose
  have hyent : entropy (Finset.range z.length) y = hReal blk.y := by
    rw [hydef, ← hlen]
    exact entropy_range_eq_hReal blk.y
  have hyU : hReal blk.y ≤ ((hUpper blk.y prec : ℚ) : ℝ) :=
    le_hUpper (fun v hv => le_of_lt (hypos' v hv)) prec
  have hrL : ((hLower (z.map Prod.snd) prec : ℚ) : ℝ) ≤ hReal (z.map Prod.snd) :=
    hLower_le (fun v hv => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact hrnn' p hp) prec
  rw [hyent] at hmax
  unfold penalty penaltyUpper
  push_cast
  linarith

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## Directed bounds for the remaining shapes

Everything left in Appendix A is built from four operations: a list sum, a
coordinate minimum, a nonnegatively weighted entropy, and a §7.6 conditional
entropy. Each gets a rational bound here, together with the decidable side
condition that makes the bound valid. -/

/-- Termwise domination lifts to list sums. -/
theorem list_sum_le {α : Type*} {l : List α} {f g : α → ℝ}
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- The rational coordinate minimum. -/
def min3q (a b c : ℚ) : ℚ := min a (min b c)

/-- A coordinate minimum of lower bounds is a lower bound on the minimum. -/
theorem min3q_le {a b c : ℚ} {x y w : ℝ} (ha : (a : ℝ) ≤ x) (hb : (b : ℝ) ≤ y)
    (hc : (c : ℝ) ≤ w) : ((min3q a b c : ℚ) : ℝ) ≤ min3 x y w := by
  unfold min3q min3
  push_cast
  exact le_min (le_trans (min_le_left _ _) ha)
    (le_min (le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) hb)
      (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hc))

/-- Every entry of a list is nonnegative. -/
def nonnegList (l : List ℚ) : Bool := l.all fun v => decide (0 ≤ v)

theorem nonnegList_sound {l : List ℚ} (h : nonnegList l = true) : ∀ v ∈ l, 0 ≤ v := by
  simpa [nonnegList] using h

/-- A rational upper bound for the §7.6 conditional entropy term. -/
def condHUpper {κ : Type} [DecidableEq κ] (prec : ℕ) (nu : Spec.Dist κ) : ℚ :=
  if nu.total = 0 then 0
  else nu.total * hUpper ((Dist.weights nu).map fun v => v / nu.total) prec

/-- The side condition under which `condHUpper` is valid. -/
def condHOk {κ : Type} [DecidableEq κ] (nu : Spec.Dist κ) : Bool :=
  decide (0 ≤ nu.total) &&
    nonnegList ((Dist.weights nu).map fun v => v / nu.total)

theorem condH_le {κ : Type} [DecidableEq κ] {prec : ℕ} {nu : Spec.Dist κ}
    (h : condHOk nu = true) : condH nu ≤ ((condHUpper prec nu : ℚ) : ℝ) := by
  simp only [condHOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨htot, hnn⟩ := h
  unfold condH condHUpper
  by_cases hz : nu.total = 0
  · rw [if_pos hz, if_pos hz]; norm_num
  · rw [if_neg hz, if_neg hz]
    have hpos : (0 : ℝ) ≤ ((nu.total : ℚ) : ℝ) := by exact_mod_cast htot
    have := le_hUpper (nonnegList_sound hnn) (n := prec)
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) hpos

/-- A rational lower bound for a nonnegatively weighted entropy. -/
def weightedHLowerOne (prec : ℕ) (c : ℚ) (l : List ℚ) : ℚ := c * hLower l prec

/-- A rational upper bound for a nonnegatively weighted entropy. -/
def weightedHUpperOne (prec : ℕ) (c : ℚ) (l : List ℚ) : ℚ := c * hUpper l prec

theorem weightedH_le_upper {prec : ℕ} {c : ℚ} {l : List ℚ} (hc : 0 ≤ c)
    (hl : ∀ v ∈ l, 0 ≤ v) :
    (c : ℝ) * hReal l ≤ ((weightedHUpperOne prec c l : ℚ) : ℝ) := by
  have hc' : (0 : ℝ) ≤ ((c : ℚ) : ℝ) := by exact_mod_cast hc
  have := le_hUpper hl (n := prec)
  unfold weightedHUpperOne
  push_cast
  exact mul_le_mul_of_nonneg_left this hc'

theorem lower_le_weightedH {prec : ℕ} {c : ℚ} {l : List ℚ} (hc : 0 ≤ c)
    (hl : ∀ v ∈ l, 0 ≤ v) :
    ((weightedHLowerOne prec c l : ℚ) : ℝ) ≤ (c : ℝ) * hReal l := by
  have hc' : (0 : ℝ) ≤ ((c : ℚ) : ℝ) := by exact_mod_cast hc
  have := hLower_le hl (n := prec)
  unfold weightedHLowerOne
  push_cast
  exact mul_le_mul_of_nonneg_left this hc'

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## Directed bounds for `η` (A8, A9, A12, A13) -/

/-- A rational upper bound for `η_(·,Y)^(r)`. -/
def etaYUpper (prec ℓc bound : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cY cZ : Coordinate) : ℚ :=
  ((etaYPlain kids cZ).map fun k =>
      weightedHUpperOne prec (w k) (Dist.weights (betaOf ℓc k cY))).sum +
    ((List.range (bound + 1)).map fun j =>
      condHUpper prec (etaYMix ℓc w kids cY cZ j)).sum

/-- The side condition under which `etaYUpper` is valid. -/
def etaYOk (ℓc bound : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cY cZ : Coordinate) : Bool :=
  ((etaYPlain kids cZ).all fun k =>
      decide (0 ≤ w k) && nonnegList (Dist.weights (betaOf ℓc k cY))) &&
    ((List.range (bound + 1)).all fun j => condHOk (etaYMix ℓc w kids cY cZ j))

theorem etaY_le {prec ℓc bound : ℕ} {w : ANode → ℚ} {kids : List ANode}
    {cY cZ : Coordinate} (h : etaYOk ℓc bound w kids cY cZ = true) :
    etaY ℓc bound w kids cY cZ ≤ ((etaYUpper prec ℓc bound w kids cY cZ : ℚ) : ℝ) := by
  simp only [etaYOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨hplain, hcond⟩ := h
  unfold etaY etaYUpper
  push_cast
  simp only [List.map_map, Function.comp_def]
  refine add_le_add (list_sum_le fun k hk => ?_) (list_sum_le fun j hj => ?_)
  · obtain ⟨hw, hnn⟩ := hplain k hk
    exact weightedH_le_upper hw (nonnegList_sound hnn)
  · exact condH_le (hcond j (List.mem_range.mp hj))

/-- A rational upper bound for `η_(·,Z)^(r)`. -/
def etaZUpper (prec ℓc bound : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cX cY cZ : Coordinate) : ℚ :=
  ((etaZPlain kids cX cY).map fun k =>
      weightedHUpperOne prec (w k) (Dist.weights (betaOf ℓc k cZ))).sum +
    ((List.range (bound + 1)).map fun kk =>
      condHUpper prec (etaZMix ℓc w kids cX cY cZ kk)).sum

/-- The side condition under which `etaZUpper` is valid. -/
def etaZOk (ℓc bound : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cX cY cZ : Coordinate) : Bool :=
  ((etaZPlain kids cX cY).all fun k =>
      decide (0 ≤ w k) && nonnegList (Dist.weights (betaOf ℓc k cZ))) &&
    ((List.range (bound + 1)).all fun kk =>
      condHOk (etaZMix ℓc w kids cX cY cZ kk))

theorem etaZ_le {prec ℓc bound : ℕ} {w : ANode → ℚ} {kids : List ANode}
    {cX cY cZ : Coordinate} (h : etaZOk ℓc bound w kids cX cY cZ = true) :
    etaZ ℓc bound w kids cX cY cZ
      ≤ ((etaZUpper prec ℓc bound w kids cX cY cZ : ℚ) : ℝ) := by
  simp only [etaZOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨hplain, hcond⟩ := h
  unfold etaZ etaZUpper
  push_cast
  simp only [List.map_map, Function.comp_def]
  refine add_le_add (list_sum_le fun k hk => ?_) (list_sum_le fun kk hkk => ?_)
  · obtain ⟨hw, hnn⟩ := hplain k hk
    exact weightedH_le_upper hw (nonnegList_sound hnn)
  · exact condH_le (hcond kk (List.mem_range.mp hkk))

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## The root contribution (A10, A11) -/

/-- The out-of-range default block. It satisfies nothing, so reading it can only
make `checkOmega` fail. -/
def defaultBlock : Block := ⟨[], 0, [], [], [], 0⟩

/-- A rational lower bound for `E_G^(r)` (A10). -/
def eRootRegionLower (prec : ℕ) (I : AInstance) (r : ℕ) (blk : Block) : ℚ :=
  let kidsR := I.kidsIn r
  let z := alphaZip kidsR
  min3q
    (hLower (Dist.weights (Dist.push (fun s => AShape.coord s (permOf r .X)) z)) prec -
      penaltyUpper prec z blk)
    (hLower (Dist.weights (betaBar I.levels ANode.alpha kidsR (permOf r .Y))) prec -
      etaYUpper prec I.levels (2 ^ I.levels) ANode.alpha kidsR (permOf r .Y) (permOf r .Z))
    (hLower (Dist.weights (betaBar I.levels ANode.alpha kidsR (permOf r .Z))) prec -
      etaZUpper prec I.levels (2 ^ I.levels) ANode.alpha kidsR (permOf r .X) (permOf r .Y)
        (permOf r .Z))

/-- The side condition under which `eRootRegionLower` is valid. -/
def eRootRegionOk (prec : ℕ) (I : AInstance) (r : ℕ) (blk : Block) : Bool :=
  let kidsR := I.kidsIn r
  let z := alphaZip kidsR
  blockOk prec z blk &&
    nonnegList (Dist.weights (Dist.push (fun s => AShape.coord s (permOf r .X)) z)) &&
    nonnegList (Dist.weights (betaBar I.levels ANode.alpha kidsR (permOf r .Y))) &&
    nonnegList (Dist.weights (betaBar I.levels ANode.alpha kidsR (permOf r .Z))) &&
    etaYOk I.levels (2 ^ I.levels) ANode.alpha kidsR (permOf r .Y) (permOf r .Z) &&
    etaZOk I.levels (2 ^ I.levels) ANode.alpha kidsR (permOf r .X) (permOf r .Y)
      (permOf r .Z)

theorem eRootRegion_ge {prec : ℕ} {I : AInstance} {r : ℕ} {blk : Block}
    (h : eRootRegionOk prec I r blk = true) :
    ((eRootRegionLower prec I r blk : ℚ) : ℝ) ≤ I.eRootRegion r := by
  simp only [eRootRegionOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hblk, hn1⟩, hn2⟩, hn3⟩, hy⟩, hz⟩ := h
  unfold AInstance.eRootRegion eRootRegionLower
  refine min3q_le ?_ ?_ ?_
  · have h1 := hLower_le (nonnegList_sound hn1) (n := prec)
    have h2 := penalty_le_of_blockOk hblk
    unfold hDist
    push_cast
    linarith
  · have h1 := hLower_le (nonnegList_sound hn2) (n := prec)
    have h2 := etaY_le (prec := prec) hy
    unfold hDist
    push_cast
    linarith
  · have h1 := hLower_le (nonnegList_sound hn3) (n := prec)
    have h2 := etaZ_le (prec := prec) hz
    unfold hDist
    push_cast
    linarith

/-- A rational lower bound for `E_G` (A11). -/
def eRootLower (prec : ℕ) (I : AInstance) (blks : List Block) : ℚ :=
  ((List.range 6).map fun r =>
    I.A.getD r 0 * eRootRegionLower prec I r (blks.getD r defaultBlock)).sum

/-- The side condition under which `eRootLower` is valid. -/
def eRootOk (prec : ℕ) (I : AInstance) (blks : List Block) : Bool :=
  (List.range 6).all fun r =>
    decide (0 ≤ I.A.getD r 0) && eRootRegionOk prec I r (blks.getD r defaultBlock)

theorem eRoot_ge {prec : ℕ} {I : AInstance} {blks : List Block}
    (h : eRootOk prec I blks = true) :
    ((eRootLower prec I blks : ℚ) : ℝ) ≤ I.eRoot := by
  simp only [eRootOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  unfold AInstance.eRoot eRootLower
  push_cast
  simp only [List.map_map, Function.comp_def]
  refine list_sum_le fun r hr => ?_
  obtain ⟨hA, hok⟩ := h r (List.mem_range.mp hr)
  have hA' : (0 : ℝ) ≤ ((I.A.getD r 0 : ℚ) : ℝ) := by exact_mod_cast hA
  push_cast
  exact mul_le_mul_of_nonneg_left (eRootRegion_ge hok) hA'

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## The level-2 exponent and the local sizes (A17, A18, A19, A20) -/

/-- A rational lower bound for `Σ_T E_(T,W)` (A16, A17). -/
def eTwoSumLower (prec : ℕ) (I : AInstance) (W : Coordinate) : ℚ :=
  (I.posTwoNodes.map fun t =>
    t.2.1 * (hLower (levelTwoList t.2.2.shape t.2.2.mu W) prec +
      levelTwoConst t.2.2.shape W)).sum

/-- The side condition under which `eTwoSumLower` is valid. -/
def eTwoSumOk (I : AInstance) (W : Coordinate) : Bool :=
  I.posTwoNodes.all fun t =>
    decide (0 ≤ t.2.1) && nonnegList (levelTwoList t.2.2.shape t.2.2.mu W)

theorem eTwoSum_ge {prec : ℕ} {I : AInstance} {W : Coordinate}
    (h : eTwoSumOk I W = true) :
    ((eTwoSumLower prec I W : ℚ) : ℝ) ≤ I.eTwoSum W := by
  simp only [eTwoSumOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold AInstance.eTwoSum eTwoSumLower levelTwoExponent
  push_cast
  simp only [List.map_map, Function.comp_def]
  refine list_sum_le fun t ht => ?_
  obtain ⟨hm, hnn⟩ := h t ht
  have hm' : (0 : ℝ) ≤ ((t.2.1 : ℚ) : ℝ) := by exact_mod_cast hm
  have := hLower_le (nonnegList_sound hnn) (n := prec)
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) hm'

/-- A rational lower bound for `Σ_T M_(T,W)` (A18, A19, A20). -/
def mTotalSumLower (prec : ℕ) (I : AInstance) (W : Coordinate) : ℚ :=
  (I.leaves.map fun t =>
    t.2.1 * (hLower (localEntropyList t.1 t.2.2 W) prec +
      localLogCoeff t.1 t.2.2 W * log2Lower (I.q : ℚ) prec)).sum

/-- The side condition under which `mTotalSumLower` is valid. -/
def mTotalSumOk (I : AInstance) (W : Coordinate) : Bool :=
  decide (1 ≤ I.q) &&
    I.leaves.all fun t =>
      decide (0 ≤ t.2.1) && nonnegList (localEntropyList t.1 t.2.2 W) &&
        decide (0 ≤ localLogCoeff t.1 t.2.2 W)

theorem mTotalSum_ge {prec : ℕ} {I : AInstance} {W : Coordinate}
    (h : mTotalSumOk I W = true) :
    ((mTotalSumLower prec I W : ℚ) : ℝ) ≤ I.mTotalSum W := by
  simp only [mTotalSumOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hq, hleaf⟩ := h
  have hqpos : (0 : ℚ) < (I.q : ℚ) := by exact_mod_cast hq
  have hlog := log2Lower_le hqpos (precision := prec)
  unfold AInstance.mTotalSum mTotalSumLower localSize
  push_cast
  simp only [List.map_map, Function.comp_def]
  refine list_sum_le fun t ht => ?_
  obtain ⟨⟨hm, hnn⟩, hc⟩ := hleaf t ht
  have hm' : (0 : ℝ) ≤ ((t.2.1 : ℚ) : ℝ) := by exact_mod_cast hm
  have hc' : (0 : ℝ) ≤ ((localLogCoeff t.1 t.2.2 W : ℚ) : ℝ) := by exact_mod_cast hc
  have hent := hLower_le (nonnegList_sound hnn) (n := prec)
  have hscaled := mul_le_mul_of_nonneg_left hlog hc'
  push_cast at hscaled ⊢
  exact mul_le_mul_of_nonneg_left (by linarith) hm'

/-! ## The requirement (A21) -/

/-- A rational upper bound for `2^(ℓ*-1) log2(q+2)` (A21). -/
def requirementUpper (prec : ℕ) (I : AInstance) : ℚ :=
  2 ^ (I.levels - 1) * log2Upper ((I.q : ℚ) + 2) prec

theorem requirement_le {prec : ℕ} {I : AInstance} :
    I.requirement ≤ ((requirementUpper prec I : ℚ) : ℝ) := by
  have hpos : (0 : ℚ) < (I.q : ℚ) + 2 := by positivity
  have hlog := le_log2Upper hpos (precision := prec)
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (I.levels - 1) := by positivity
  unfold AInstance.requirement requirementUpper
  push_cast
  push_cast at hlog
  exact mul_le_mul_of_nonneg_left hlog hpow

end MatrixMath.Certificate


namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## Well-formedness at any level (A.1, A.2)

`wfNode2` decides `ANode.WF 2`, where the recursion is vacuous. This decides
`ANode.WF ℓ` for every `ℓ`, by the same recursion `WF` itself uses.
-/

/-- Decidable transcription of `ANode.WF`, at any level. -/
def wfNode : ℕ → ANode → Bool
  | ℓ, .zeroLeaf r s a b =>
      decide (r < 6) && decide (AShape.atLevel s ℓ) &&
        decide (¬ AShape.positive s) && decide (0 ≤ a) &&
        decide (Dist.IsProb b) &&
        decide (∀ p ∈ b, SupportVec.mem p.1 ℓ (AShape.coord s (AShape.firstPos s)))
  | ℓ, .posTwo r s a mu =>
      decide (ℓ = 2) && decide (r < 6) && decide (AShape.atLevel s 2) &&
        decide (AShape.positive s) && decide (0 ≤ a) && decide (0 ≤ mu) &&
        decide (mu ≤ 1 / 2)
  | ℓ, .posBranch r s a A kids =>
      decide (3 ≤ ℓ) && decide (r < 6) && decide (AShape.atLevel s ℓ) &&
        decide (AShape.positive s) && decide (0 ≤ a) &&
        decide (A.length = 6) && decide (∀ x ∈ A, 0 ≤ x) && decide (A.sum = 1) &&
        ((List.range 6).all fun rr =>
          decide ((kids.filter fun k => k.region = rr).map ANode.shape
            = splitList ℓ s)) &&
        ((List.range 6).all fun rr =>
          decide (((kids.filter fun k => k.region = rr).map ANode.alpha).sum = 1)) &&
        kids.attach.all (fun k => wfNode (ℓ - 1) k.1)
  termination_by _ n => sizeOf n
  decreasing_by
    have h := List.sizeOf_lt_of_mem k.2
    simp only [ANode.posBranch.sizeOf_spec]
    omega

theorem wfNode_sound : ∀ {ℓ : ℕ} {k : ANode}, wfNode ℓ k = true → ANode.WF ℓ k
  | ℓ, .zeroLeaf r s a b, h => by
    simp only [wfNode, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ANode.WF]
    exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  | ℓ, .posTwo r s a mu, h => by
    simp only [wfNode, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ANode.WF]
    exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  | ℓ, .posBranch r s a A kids, h => by
    simp only [wfNode, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, List.mem_attach, forall_const] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hs⟩, hpos⟩, ha⟩, hA6⟩, hAnn⟩, hA1⟩, hshape⟩, halpha⟩, hkids⟩ := h
    rw [ANode.WF]
    refine ⟨hl, hr, hs, hpos, ha, hA6, hAnn, hA1, hshape, halpha, ?_⟩
    intro k hk
    exact wfNode_sound (hkids ⟨k, hk⟩)
  termination_by ℓ k => sizeOf k
  decreasing_by
    have hlt := List.sizeOf_lt_of_mem hk
    simp only [ANode.posBranch.sizeOf_spec]
    omega

/-- Decidable transcription of `AInstance.WF`, at any level. -/
def wfInstance (I : AInstance) : Bool :=
  decide (1 ≤ I.q) && decide (2 ≤ I.levels) &&
    decide (I.A.length = 6) && decide (∀ x ∈ I.A, 0 ≤ x) && decide (I.A.sum = 1) &&
    ((List.range 6).all fun r =>
      decide ((I.kidsIn r).map ANode.shape = shapeList I.levels)) &&
    ((List.range 6).all fun r =>
      decide (((I.kidsIn r).map ANode.alpha).sum = 1)) &&
    I.kids.all (wfNode I.levels)

theorem wfInstance_sound {I : AInstance} (h : wfInstance I = true) : I.WF := by
  simp only [wfInstance, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hq, hl⟩, hA6⟩, hAnn⟩, hA1⟩, hshape⟩, halpha⟩, hkids⟩ := h
  exact ⟨hq, hl, hA6, hAnn, hA1, hshape, halpha,
    fun k hk => wfNode_sound (hkids k hk)⟩

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## The interior levels (A12–A15)

Structurally identical to the root: three candidates, a coordinate minimum, and
one §7.4 block for the penalty. The differences are that the weights are
`α(u) + α(s_T - u)` rather than `α(s)`, that the domain is `Split(s_T)` rather
than `S_ℓ*`, and that everything is scaled by `m_T A_T^(r)`.
-/

/-- Reading a list positionally and reading it directly agree. -/
theorem map_range_getD {α : Type*} {β : Type*} [AddCommMonoid β]
    (l : List α) (d : α) (f : α → β) :
    ((List.range l.length).map fun i => f (l.getD i d)).sum = (l.map f).sum := by
  rw [← sum_range_eq_list, sum_range_getD]

/-- The out-of-range default node, used only where a positional read cannot
occur for a well-formed instance. -/
def defaultEntry : ℕ × ℚ × ANode := (0, 0, .posTwo 0 (0, 0, 0) 0 0)

/-- Rational lower bounds for the three A14 candidates of one interior node. -/
def eInteriorRegionLower (prec ℓ : ℕ) (m : ℚ) (s : AShape) (A : List ℚ)
    (kids : List ANode) (r : ℕ) (blk : Block) : ℚ × ℚ × ℚ :=
  let kidsR := kids.filter fun k => k.region = r
  let w : ANode → ℚ := fun k =>
    alphaAt kids r k.shape + alphaAt kids r (AShape.sub s k.shape)
  let z := alphaZip kidsR
  let scale := m * A.getD r 0
  (scale * (hLower (Dist.weights (Dist.push (fun t => AShape.coord t (permOf r .X)) z)) prec -
      penaltyUpper prec z blk),
   scale * (hLower (Dist.weights (betaRegion (ℓ - 1) kids r (permOf r .Y))) prec -
      etaYUpper prec (ℓ - 1) (2 ^ ℓ) w kidsR (permOf r .Y) (permOf r .Z)),
   scale * (hLower (Dist.weights (betaRegion (ℓ - 1) kids r (permOf r .Z))) prec -
      etaZUpper prec (ℓ - 1) (2 ^ ℓ) w kidsR (permOf r .X) (permOf r .Y) (permOf r .Z)))

/-- The side condition under which `eInteriorRegionLower` is valid. -/
def eInteriorRegionOk (prec ℓ : ℕ) (m : ℚ) (s : AShape) (A : List ℚ)
    (kids : List ANode) (r : ℕ) (blk : Block) : Bool :=
  let kidsR := kids.filter fun k => k.region = r
  let w : ANode → ℚ := fun k =>
    alphaAt kids r k.shape + alphaAt kids r (AShape.sub s k.shape)
  let z := alphaZip kidsR
  decide (0 ≤ m) && decide (0 ≤ A.getD r 0) &&
    blockOk prec z blk &&
    nonnegList (Dist.weights (Dist.push (fun t => AShape.coord t (permOf r .X)) z)) &&
    nonnegList (Dist.weights (betaRegion (ℓ - 1) kids r (permOf r .Y))) &&
    nonnegList (Dist.weights (betaRegion (ℓ - 1) kids r (permOf r .Z))) &&
    etaYOk (ℓ - 1) (2 ^ ℓ) w kidsR (permOf r .Y) (permOf r .Z) &&
    etaZOk (ℓ - 1) (2 ^ ℓ) w kidsR (permOf r .X) (permOf r .Y) (permOf r .Z)

theorem eInteriorRegion_ge {prec ℓ : ℕ} {m : ℚ} {s : AShape} {A : List ℚ}
    {kids : List ANode} {r : ℕ} {blk : Block}
    (h : eInteriorRegionOk prec ℓ m s A kids r blk = true) :
    let lower := eInteriorRegionLower prec ℓ m s A kids r blk
    let real := AInstance.eInteriorRegion ℓ m s A kids r
    ((lower.1 : ℚ) : ℝ) ≤ real.1 ∧ ((lower.2.1 : ℚ) : ℝ) ≤ real.2.1 ∧
      ((lower.2.2 : ℚ) : ℝ) ≤ real.2.2 := by
  simp only [eInteriorRegionOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hm, hA⟩, hblk⟩, hn1⟩, hn2⟩, hn3⟩, hy⟩, hz⟩ := h
  have hscale : (0 : ℝ) ≤ ((m : ℚ) : ℝ) * ((A.getD r 0 : ℚ) : ℝ) := by
    have hm' : (0 : ℝ) ≤ ((m : ℚ) : ℝ) := by exact_mod_cast hm
    have hA' : (0 : ℝ) ≤ ((A.getD r 0 : ℚ) : ℝ) := by exact_mod_cast hA
    exact mul_nonneg hm' hA' 
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [eInteriorRegionLower, AInstance.eInteriorRegion, hDist]
  · have h1 := hLower_le (nonnegList_sound hn1) (n := prec)
    have h2 := penalty_le_of_blockOk hblk
    push_cast
    exact mul_le_mul_of_nonneg_left (by push_cast at h1 h2 ⊢; linarith) hscale
  · have h1 := hLower_le (nonnegList_sound hn2) (n := prec)
    have h2 := etaY_le (prec := prec) hy
    push_cast
    exact mul_le_mul_of_nonneg_left (by push_cast at h1 h2 ⊢; linarith) hscale
  · have h1 := hLower_le (nonnegList_sound hn3) (n := prec)
    have h2 := etaZ_le (prec := prec) hz
    push_cast
    exact mul_le_mul_of_nonneg_left (by push_cast at h1 h2 ⊢; linarith) hscale

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-- Blocks consumed before level `ℓ` (§6.5).

The root's six, then six for every positive interior node at every level below
`ℓ` from three upward. A.10 sums `E_ℓ` level by level, so this is the order the
evaluator consumes them in — which is *not* the preorder once `ℓ* ≥ 4`, because
the preorder reaches a level-4 node before its level-3 children. -/
def blockOffset (I : AInstance) (ℓ : ℕ) : ℕ :=
  6 + 6 * ((((List.range ℓ).filter fun k => 3 ≤ k)).map fun k =>
    (I.posNodesAt k).length).sum

/-- A rational lower bound for `E_ℓ` at one interior level (A15). -/
def eLevelLower (prec : ℕ) (I : AInstance) (ℓ offset : ℕ) (blocks : List Block) : ℚ :=
  let nodes := I.posNodesAt ℓ
  ((List.range 6).map fun r =>
    let per := (List.range nodes.length).map fun j =>
      let t := nodes.getD j defaultEntry
      match t.2.2 with
      | .posBranch _ s _ A kids =>
        eInteriorRegionLower prec ℓ t.2.1 s A kids r
          (blocks.getD (offset + 6 * j + r) defaultBlock)
      | _ => (0, 0, 0)
    min3q ((per.map fun p => p.1).sum) ((per.map fun p => p.2.1).sum)
      ((per.map fun p => p.2.2).sum)).sum

/-- The side condition under which `eLevelLower` is valid. -/
def eLevelOk (prec : ℕ) (I : AInstance) (ℓ offset : ℕ) (blocks : List Block) : Bool :=
  let nodes := I.posNodesAt ℓ
  (List.range 6).all fun r =>
    (List.range nodes.length).all fun j =>
      let t := nodes.getD j defaultEntry
      match t.2.2 with
      | .posBranch _ s _ A kids =>
        eInteriorRegionOk prec ℓ t.2.1 s A kids r
          (blocks.getD (offset + 6 * j + r) defaultBlock)
      | _ => true

theorem eLevel_ge {prec : ℕ} {I : AInstance} {ℓ offset : ℕ} {blocks : List Block}
    (h : eLevelOk prec I ℓ offset blocks = true) :
    ((eLevelLower prec I ℓ offset blocks : ℚ) : ℝ) ≤ I.eLevel ℓ := by
  simp only [eLevelOk, List.all_eq_true, List.mem_range] at h
  unfold AInstance.eLevel eLevelLower
  push_cast
  simp only [List.map_map, Function.comp_def]
  refine list_sum_le fun r hr => ?_
  have hr' := List.mem_range.mp hr
  push_cast
  refine min3q_le ?_ ?_ ?_ <;>
    (rw [← map_range_getD (I.posNodesAt ℓ) defaultEntry]
     push_cast
     simp only [List.map_map, Function.comp_def]
     refine list_sum_le fun j hj => ?_
     have hok := h r hr' j (List.mem_range.mp hj)
     revert hok
     cases hnode : (I.posNodesAt ℓ).getD j defaultEntry with
     | mk lvl rest =>
       cases hrest : rest with
       | mk mass node =>
         cases node with
         | posBranch rr ss aa AA kk =>
           intro hok
           first
             | exact (eInteriorRegion_ge hok).1
             | exact (eInteriorRegion_ge hok).2.1
             | exact (eInteriorRegion_ge hok).2.2
         | zeroLeaf _ _ _ _ => intro _; simp
         | posTwo _ _ _ _ => intro _; simp)

end MatrixMath.Certificate

namespace MatrixMath.Certificate

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

/-! ## The whole check (A20, A21, §7.2) -/

/-- The Track A certificate payload the checker consumes.

`blocks` supplies one §7.4 maximum-entropy block per region, which is what makes
`P_(S_2)` bounded rather than merely asserted. -/
structure TrackACert where
  /-- The Appendix A instance, with every free variable as an exact rational. -/
  inst : AInstance
  /-- One block per region, in region order. -/
  blocks : List Block
  /-- The claimed `Ω`. -/
  omega : ℚ
  /-- The §7.3 series precision used for every directed bound. -/
  precision : ℕ

namespace TrackACert

/-- The interior levels of an instance, three and above (A20). -/
def interiorLevels (I : AInstance) : List ℕ :=
  (List.range (I.levels + 1)).filter fun ℓ => 3 ≤ ℓ

/-- A rational lower bound for `Σ_(ℓ=3..ℓ*) E_ℓ` (A15, A20). -/
def interiorLower (prec : ℕ) (I : AInstance) (blocks : List Block) : ℚ :=
  ((interiorLevels I).map fun ℓ =>
    eLevelLower prec I ℓ (blockOffset I ℓ) blocks).sum

/-- The side condition under which `interiorLower` is valid. -/
def interiorOk (prec : ℕ) (I : AInstance) (blocks : List Block) : Bool :=
  (interiorLevels I).all fun ℓ => eLevelOk prec I ℓ (blockOffset I ℓ) blocks

theorem interior_ge {prec : ℕ} {I : AInstance} {blocks : List Block}
    (h : interiorOk prec I blocks = true) :
    ((interiorLower prec I blocks : ℚ) : ℝ)
      ≤ ((interiorLevels I).map I.eLevel).sum := by
  simp only [interiorOk, List.all_eq_true] at h
  unfold interiorLower
  push_cast
  simp only [List.map_map, Function.comp_def]
  exact list_sum_le fun ℓ hl => eLevel_ge (h ℓ hl)

/-- A rational lower bound for `E_total` (A20). -/
def eTotalLower (c : TrackACert) : ℚ :=
  eRootLower c.precision c.inst c.blocks +
    min3q (eTwoSumLower c.precision c.inst .X) (eTwoSumLower c.precision c.inst .Y)
      (eTwoSumLower c.precision c.inst .Z) +
    interiorLower c.precision c.inst c.blocks

/-- A rational lower bound for `M_total` (A20). -/
def mTotalLower (c : TrackACert) : ℚ :=
  min3q (mTotalSumLower c.precision c.inst .X) (mTotalSumLower c.precision c.inst .Y)
    (mTotalSumLower c.precision c.inst .Z)

/-- **The checker** (§7.2, A21).

Everything is decidable: well-formedness at `ℓ* = 2`, the side conditions that
make each directed bound valid, `Ω ≥ 0`, and the rational inequality itself. -/
def check (c : TrackACert) : Bool :=
  wfInstance c.inst &&
    decide (0 ≤ c.omega) &&
    eRootOk c.precision c.inst c.blocks &&
    interiorOk c.precision c.inst c.blocks &&
    eTwoSumOk c.inst .X && eTwoSumOk c.inst .Y &&
    eTwoSumOk c.inst .Z &&
    mTotalSumOk c.inst .X && mTotalSumOk c.inst .Y &&
    mTotalSumOk c.inst .Z &&
    decide (requirementUpper c.precision c.inst
      ≤ c.eTotalLower + c.mTotalLower * c.omega)

theorem eTotalLower_le {c : TrackACert}
    (hroot : eRootOk c.precision c.inst c.blocks = true)
    (hinterior : interiorOk c.precision c.inst c.blocks = true)
    (hx : eTwoSumOk c.inst .X = true)
    (hy : eTwoSumOk c.inst .Y = true)
    (hz : eTwoSumOk c.inst .Z = true) :
    ((c.eTotalLower : ℚ) : ℝ) ≤ c.inst.eTotal := by
  unfold TrackACert.eTotalLower AInstance.eTotal AInstance.eTwo
  push_cast
  refine add_le_add (add_le_add (eRoot_ge hroot)
    (min3q_le (eTwoSum_ge hx) (eTwoSum_ge hy) (eTwoSum_ge hz))) ?_
  have := interior_ge (prec := c.precision) (I := c.inst) (blocks := c.blocks) hinterior
  unfold interiorLevels at this
  exact this

theorem mTotalLower_le {c : TrackACert}
    (hx : mTotalSumOk c.inst .X = true)
    (hy : mTotalSumOk c.inst .Y = true)
    (hz : mTotalSumOk c.inst .Z = true) :
    ((c.mTotalLower : ℚ) : ℝ) ≤ c.inst.mTotal := by
  unfold TrackACert.mTotalLower AInstance.mTotal
  exact min3q_le (mTotalSum_ge hx) (mTotalSum_ge hy) (mTotalSum_ge hz)

/-- **The checker is sound** (A.10, §7.2).

Deciding `check` establishes feasibility of the A.1–A.10 problem itself, with no
residual hypothesis: the instance the existential asks for is the one the
certificate carries. -/
theorem check_sound {c : TrackACert} (h : check c = true) :
    CombinationLossFeasible c.inst.q c.inst.levels ((c.omega : ℚ) : ℝ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwf, homega⟩, hroot⟩, hinterior⟩, hex⟩, hey⟩, hez⟩, hmx⟩, hmy⟩, hmz⟩,
    hfinal⟩ := h
  refine ⟨c.inst, rfl, rfl, wfInstance_sound hwf, ?_⟩
  exact directed_implies_real (eTotalLower_le hroot hinterior hex hey hez)
    (mTotalLower_le hmx hmy hmz) requirement_le homega hfinal

/-- **The Track A conclusion at `ℓ* = 2`** (A.10, §3.2).

`AX1_combination_loss` is the only project axiom involved, and its hypothesis is
supplied by `check_sound` rather than assumed: `#print axioms` on this theorem
lists Lean's standard three plus `AX1_combination_loss`, and nothing else. -/
theorem omega_le_of_check {c : TrackACert} (h : check c = true) :
    omegaExponent ≤ ((c.omega : ℚ) : ℝ) :=
  AX1_combination_loss (check_sound h)

end TrackACert

end MatrixMath.Certificate
