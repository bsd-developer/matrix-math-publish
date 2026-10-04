import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The matrix multiplication exponent, defined

Normative source: `docs/adr/0013-definitional-omega.md`.

Before this module, `omegaExponent` was an *opaque* real: the development's
final theorems bounded a constant about which nothing was stated, and the
connection to matrix multiplication lived entirely in prose. This module
replaces the opaque constant with the standard definition, so that
`AX1_combination_loss` becomes an axiom about the exponent itself and the
top-level theorems have mathematical content inside Lean.

The definition is over `ℚ`, by the infimum characterization:

* a rank-`r` **decomposition** of `n × n` matrix multiplication is a family of
  `r` rank-one bilinear terms summing to the product (A.0 in the cited
  formulation; Strassen's normal form);
* `mulRank n` is the least such `r`;
* `omegaExponent` is `⨅ (n ≥ 2), logb n (mulRank n)`.

Submultiplicativity of rank under tensor powers makes this infimum equal to
the usual `inf { τ | R(n) = O(n^τ) }`; the equivalence is classical and is
*not* needed by the development — the definition itself is the object AX1
speaks about, and the cited theorem is stated over every field, so asserting
it for `ℚ` is the weaker (safer) direction. See the ADR for both points.

Sanity lemmas keep the definition honest: the defining set is inhabited
(`mulRank_le_cube`, via the `n³` schoolbook decomposition), the rank is
positive (`one_le_mulRank`), and the exponent is nonnegative
(`omegaExponent_nonneg`) — so the infimum is over a nonempty, bounded-below
range and its value is not a junk-value artifact.
-/

namespace MatrixMath

open Matrix

/-- Square rational matrices, the arena in which `ω` is defined. -/
abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℚ

/-- A rank-`r` bilinear decomposition of `n × n` matrix multiplication over
`ℚ`: `r` rank-one terms whose sum is the product. -/
structure MulDecomposition (n r : ℕ) : Type where
  left : Fin r → (Mat n →ₗ[ℚ] ℚ)
  right : Fin r → (Mat n →ₗ[ℚ] ℚ)
  out : Fin r → Mat n
  correct : ∀ A B : Mat n, A * B = ∑ t, (left t A * right t B) • out t

/-- The triple index of the schoolbook decomposition, flattened. -/
def cubeIndex (n : ℕ) : (Fin n × Fin n × Fin n) ≃ Fin (n * (n * n)) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finProdFinEquiv

/-- Schoolbook multiplication as a sum of `n³` rank-one terms, entrywise. -/
theorem mul_eq_sum_triple (n : ℕ) (A B : Mat n) :
    A * B = ∑ p : Fin n × Fin n × Fin n,
      (A p.1 p.2.1 * B p.2.1 p.2.2) • Matrix.single p.1 p.2.2 (1 : ℚ) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [ite_and]

/-- The schoolbook decomposition: witnesses that the rank set is inhabited. -/
noncomputable def cubeDecomposition (n : ℕ) : MulDecomposition n (n * (n * n)) where
  left t := Matrix.entryLinearMap ℚ ℚ ((cubeIndex n).symm t).1 ((cubeIndex n).symm t).2.1
  right t := Matrix.entryLinearMap ℚ ℚ ((cubeIndex n).symm t).2.1 ((cubeIndex n).symm t).2.2
  out t := Matrix.single ((cubeIndex n).symm t).1 ((cubeIndex n).symm t).2.2 1
  correct A B := by
    rw [mul_eq_sum_triple]
    exact Fintype.sum_equiv (cubeIndex n) _ _ (fun p => by simp)

/-- The bilinear rank of `n × n` matrix multiplication over `ℚ`. -/
noncomputable def mulRank (n : ℕ) : ℕ :=
  sInf {r | Nonempty (MulDecomposition n r)}

theorem mulRank_le_cube (n : ℕ) : mulRank n ≤ n * (n * n) :=
  Nat.sInf_le ⟨cubeDecomposition n⟩

theorem one_le_mulRank (n : ℕ) (hn : 1 ≤ n) : 1 ≤ mulRank n := by
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have hne : {r | Nonempty (MulDecomposition n r)}.Nonempty := ⟨_, ⟨cubeDecomposition n⟩⟩
  obtain ⟨d⟩ : Nonempty (MulDecomposition n 0) := h ▸ Nat.sInf_mem hne
  have h1 : (1 : Mat n) * 1 = 0 := by
    rw [d.correct 1 1]
    exact Finset.sum_empty
  rw [one_mul] at h1
  have hi : (1 : Mat n) ⟨0, hn⟩ ⟨0, hn⟩ = 0 := by rw [h1]; rfl
  simp [Matrix.one_apply_eq] at hi

/-- **The matrix multiplication exponent**, over `ℚ`, by the infimum
characterization. This is the constant `AX1_combination_loss` bounds. -/
noncomputable def omegaExponent : ℝ :=
  ⨅ n : {m : ℕ // 2 ≤ m}, Real.logb (n : ℕ) (mulRank n)

theorem omegaExponent_nonneg : 0 ≤ omegaExponent := by
  refine Real.iInf_nonneg fun n => Real.logb_nonneg ?_ ?_
  · exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two n.2
  · exact_mod_cast one_le_mulRank n (Nat.one_le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two n.2))

end MatrixMath
