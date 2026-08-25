import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Appendix B tensor semantics

Normative source: `docs/specs/0001_spec.md` §10.1–§10.2 and Appendix B.1–B.3.

The third tensor mode is the **dual** output coordinate `(j,i)`, never the
ordinary output coordinate `(i,j)` (§10.1). The point of this file is to make
that choice explicit and then prove, once, that a reconstruction of
`T_{n,m,p}` really does compute `C = A * B` under the dual unflattening (B.3).

Everything here is mathematical specification. The executable checker lives in
`MatrixMath.Certificate.Decomposition`; `MatrixMath.Certificate.Sound` connects
the two.
-/

namespace MatrixMath.Spec

open Finset

variable {R : Type*}

/-! ## Flattening (§10.1) -/

/-- `flatA(i,k) = i*m + k` for `0 ≤ i < n`, `0 ≤ k < m` (§10.1). -/
def flatA (m i k : ℕ) : ℕ := i * m + k

/-- `flatB(k,j) = k*p + j` for `0 ≤ k < m`, `0 ≤ j < p` (§10.1). -/
def flatB (p k j : ℕ) : ℕ := k * p + j

/-- `flatCdual(j,i) = j*n + i` for `0 ≤ j < p`, `0 ≤ i < n` (§10.1).

The argument order is `(j,i)`: this is the dual output coordinate. -/
def flatCdual (n j i : ℕ) : ℕ := j * n + i

theorem flatA_div {m i k : ℕ} (hk : k < m) : flatA m i k / m = i := by
  unfold flatA
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < m),
    Nat.div_eq_of_lt hk, Nat.zero_add]

theorem flatA_mod {m i k : ℕ} (hk : k < m) : flatA m i k % m = k := by
  unfold flatA
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

theorem flatA_lt {n m i k : ℕ} (hi : i < n) (hk : k < m) : flatA m i k < n * m := by
  unfold flatA
  have h1 : i * m + k < i * m + m := by omega
  have h2 : i * m + m = (i + 1) * m := by ring
  have h3 : (i + 1) * m ≤ n * m := Nat.mul_le_mul_right m hi
  omega

theorem flatB_div {p k j : ℕ} (hj : j < p) : flatB p k j / p = k := flatA_div hj
theorem flatB_mod {p k j : ℕ} (hj : j < p) : flatB p k j % p = j := flatA_mod hj
theorem flatB_lt {m p k j : ℕ} (hk : k < m) (hj : j < p) : flatB p k j < m * p :=
  flatA_lt hk hj

theorem flatCdual_div {n j i : ℕ} (hi : i < n) : flatCdual n j i / n = j := flatA_div hi
theorem flatCdual_mod {n j i : ℕ} (hi : i < n) : flatCdual n j i % n = i := flatA_mod hi
theorem flatCdual_lt {n p j i : ℕ} (hj : j < p) (hi : i < n) : flatCdual n j i < p * n :=
  flatA_lt hj hi

/-- The flattenings are injective on their declared ranges, so a coordinate
determines its index pair (§10.3 round-trip requirement). -/
theorem flatA_injective {m i k i' k' : ℕ} (hk : k < m) (hk' : k' < m)
    (h : flatA m i k = flatA m i' k') : i = i' ∧ k = k' := by
  constructor
  · have := congrArg (· / m) h
    simpa [flatA_div hk, flatA_div hk'] using this
  · have := congrArg (· % m) h
    simpa [flatA_mod hk, flatA_mod hk'] using this

/-! ## The target tensor (Appendix B.1) -/

/-- The support indicator of `T_{n,m,p}` on flattened coordinates (B.1).

`T[a,b,c] = 1` exactly when `a`, `b`, and `c` decode to `(i,k)`, `(k,j)`, and the
dual `(j,i)` with matching `i`, `j`, and `k`; every other entry is zero. -/
def targetEntry (n m p a b c : ℕ) : Bool :=
  (a % m == b / p) && (b % p == c / n) && (c % n == a / m)

/-- The target tensor entry as a ring element. -/
def targetCoeff (R : Type*) [Zero R] [One R] (n m p a b c : ℕ) : R :=
  if targetEntry n m p a b c then 1 else 0

section Semiring
variable [Semiring R]

/-- On the support of `T_{n,m,p}` the coefficient is one (B.1, B.2). -/
theorem targetCoeff_support {n m p i k j : ℕ} (hi : i < n) (hk : k < m) (hj : j < p) :
    targetCoeff R n m p (flatA m i k) (flatB p k j) (flatCdual n j i) = 1 := by
  unfold targetCoeff targetEntry
  rw [flatA_mod hk, flatB_div hj, flatB_mod hj, flatCdual_div hi, flatCdual_mod hi,
    flatA_div hk]
  simp

/-- The coefficient factors into three independent index indicators, which is
the form the reconstruction proof collapses. -/
theorem targetCoeff_as_indicators {n m p i' k k' j' j i : ℕ}
    (hk : k < m) (hj' : j' < p) (hi : i < n) :
    targetCoeff R n m p (flatA m i' k) (flatB p k' j') (flatCdual n j i) =
      (if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0) *
        (if j' = j then 1 else 0) := by
  unfold targetCoeff targetEntry
  rw [flatA_mod hk, flatB_div hj', flatB_mod hj', flatCdual_div hi, flatCdual_mod hi,
    flatA_div hk]
  by_cases h1 : i' = i <;> by_cases h2 : k = k' <;> by_cases h3 : j' = j <;>
    simp [h1, h2, h3, Ne.symm]

end Semiring

/-! ## Decompositions (Appendix B.1) -/

/-- One rank-one summand `u ⊗ v ⊗ w`, with factors indexed by flattened
coordinates. Out-of-range indices read as zero, which matches the executable
representation's `getD _ 0`. -/
structure Term (R : Type*) where
  /-- The left factor, meaningful on `[0, n*m)`. -/
  u : ℕ → R
  /-- The right factor, meaningful on `[0, m*p)`. -/
  v : ℕ → R
  /-- The dual-output factor, meaningful on `[0, p*n)`. -/
  w : ℕ → R

/-- The tensor entry produced by a list of terms at one coordinate. -/
def sumEntry [AddCommMonoid R] [Mul R] (terms : List (Term R)) (a b c : ℕ) : R :=
  (terms.map fun t => t.u a * t.v b * t.w c).sum

/-- `T_{n,m,p} = Σ_r u_r ⊗ v_r ⊗ w_r` entrywise over the coordinate box (B1). -/
def Reconstructs [Semiring R] (n m p : ℕ) (terms : List (Term R)) : Prop :=
  ∀ a b c, a < n * m → b < m * p → c < p * n →
    sumEntry terms a b c = targetCoeff R n m p a b c

/-! ## The bilinear algorithm (§10.2, B.3) -/

section CommRing
variable [CommRing R]

/-- `left[r] = Σ_(i,k) u_r[flatA(i,k)] * A[i,k]` (§10.2). -/
def leftFactor (n m : ℕ) (t : Term R) (A : ℕ → ℕ → R) : R :=
  ∑ i ∈ range n, ∑ k ∈ range m, t.u (flatA m i k) * A i k

/-- `right[r] = Σ_(k,j) v_r[flatB(k,j)] * B[k,j]` (§10.2). -/
def rightFactor (m p : ℕ) (t : Term R) (B : ℕ → ℕ → R) : R :=
  ∑ k ∈ range m, ∑ j ∈ range p, t.v (flatB p k j) * B k j

/-- `C[i,j] = Σ_r w_r[flatCdual(j,i)] * left[r] * right[r]` (§10.2).

The dual unflattening is undone here, explicitly and exactly once. -/
def bilinearProduct (n m p : ℕ) (terms : List (Term R))
    (A B : ℕ → ℕ → R) (i j : ℕ) : R :=
  (terms.map fun t =>
    t.w (flatCdual n j i) * (leftFactor n m t A * rightFactor m p t B)).sum

/-- The ordinary matrix product `C[i,j] = Σ_k A[i,k] * B[k,j]`. -/
def matMul (m : ℕ) (A B : ℕ → ℕ → R) (i j : ℕ) : R :=
  ∑ k ∈ range m, A i k * B k j

/-- A list-sum of finite sums may be exchanged with the finite sum. -/
private theorem list_sum_map_finset_sum {α β : Type*} (l : List α) (s : Finset β)
    (f : α → β → R) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [ih, Finset.sum_add_distrib]

/-- A scalar factors out of a list-sum. -/
private theorem list_sum_map_mul_left {α : Type*} (l : List α) (f : α → R) (x : R) :
    (l.map fun a => x * f a).sum = x * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [ih, mul_add]

/-- **Appendix B.3.** A reconstruction of `T_{n,m,p}` computes the matrix
product under the explicit dual-output unflattening.

This is what makes an accepted decomposition certificate a statement about
matrix multiplication rather than about an array of numbers. -/
theorem reconstructs_bilinear {n m p : ℕ} {terms : List (Term R)}
    (h : Reconstructs n m p terms) (A B : ℕ → ℕ → R) {i j : ℕ}
    (hi : i < n) (hj : j < p) :
    bilinearProduct n m p terms A B i j = matMul m A B i j := by
  classical
  unfold bilinearProduct leftFactor rightFactor matMul
  -- Push the scalar `w` inside and expand the product of the two inner sums.
  have expand : ∀ t : Term R,
      t.w (flatCdual n j i) *
          ((∑ i' ∈ range n, ∑ k ∈ range m, t.u (flatA m i' k) * A i' k) *
            ∑ k' ∈ range m, ∑ j' ∈ range p, t.v (flatB p k' j') * B k' j') =
        ∑ i' ∈ range n, ∑ k ∈ range m, ∑ k' ∈ range m, ∑ j' ∈ range p,
          (A i' k * B k' j') *
            (t.u (flatA m i' k) * t.v (flatB p k' j') * t.w (flatCdual n j i)) := by
    intro t
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring
  -- Exchange the list sum with the four finite sums and pull out the scalar.
  simp only [expand, list_sum_map_finset_sum, list_sum_map_mul_left]
  -- Replace each inner list sum by the reconstruction hypothesis, in factored
  -- indicator form.
  have key : ∀ i' ∈ range n, ∀ k ∈ range m, ∀ k' ∈ range m, ∀ j' ∈ range p,
      (A i' k * B k' j') *
          (terms.map fun t =>
            t.u (flatA m i' k) * t.v (flatB p k' j') * t.w (flatCdual n j i)).sum =
        (A i' k * B k' j') *
          ((if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0) *
            (if j' = j then 1 else 0)) := by
    intro i' hi' k hk k' hk' j' hj'
    rw [Finset.mem_range] at hi' hk hk' hj'
    have hrec := h (flatA m i' k) (flatB p k' j') (flatCdual n j i)
      (flatA_lt hi' hk) (flatB_lt hk' hj') (flatCdual_lt hj hi)
    unfold sumEntry at hrec
    rw [hrec, targetCoeff_as_indicators hk hj' hi]
  rw [Finset.sum_congr rfl fun i' hi' =>
        Finset.sum_congr rfl fun k hk =>
          Finset.sum_congr rfl fun k' hk' =>
            Finset.sum_congr rfl fun j' hj' => key i' hi' k hk k' hk' j' hj']
  -- Collapse the three indicators, innermost first.
  have collapse_j : ∀ i' k k' : ℕ,
      (∑ j' ∈ range p, (A i' k * B k' j') *
        ((if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0) *
          (if j' = j then 1 else 0))) =
      ((if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0)) * (A i' k * B k' j) := by
    intro i' k k'
    have : ∀ j' : ℕ, (A i' k * B k' j') *
        ((if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0) *
          (if j' = j then 1 else 0)) =
        if j' = j then
          ((if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0)) * (A i' k * B k' j')
        else 0 := by
      intro j'
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun j' _ => this j', Finset.sum_ite_eq' (range p) j]
    simp [Finset.mem_range, hj]
  rw [Finset.sum_congr rfl fun i' _ =>
        Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun k' _ => collapse_j i' k k']
  have collapse_k : ∀ i' k : ℕ, k < m →
      (∑ k' ∈ range m, ((if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0)) *
        (A i' k * B k' j)) = (if i' = i then (1 : R) else 0) * (A i' k * B k j) := by
    intro i' k hk
    have : ∀ k' : ℕ, ((if i' = i then (1 : R) else 0) * (if k = k' then 1 else 0)) *
        (A i' k * B k' j) =
        if k' = k then (if i' = i then (1 : R) else 0) * (A i' k * B k' j) else 0 := by
      intro k'
      by_cases hkk : k' = k
      · subst hkk; split_ifs <;> ring
      · rw [if_neg hkk, if_neg (Ne.symm hkk)]; ring
    rw [Finset.sum_congr rfl fun k' _ => this k', Finset.sum_ite_eq' (range m) k]
    simp [Finset.mem_range, hk]
  rw [Finset.sum_congr rfl fun i' _ =>
        Finset.sum_congr rfl fun k hk => collapse_k i' k (Finset.mem_range.mp hk)]
  -- The remaining `i'` indicator is constant in `k`, so it factors out.
  rw [Finset.sum_congr rfl fun i' _ => (Finset.mul_sum (range m) _ _).symm]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (range n) i]
  simp [Finset.mem_range, hi]

end CommRing

end MatrixMath.Spec
