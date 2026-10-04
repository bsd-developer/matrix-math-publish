import MatrixMath.Certificate.Decomposition

/-!
# Decomposition checker soundness

Normative source: `docs/specs/0001_spec.md` §3.1, §3.5, §10.4, Appendix B.

The contract of this module is the one non-negotiable property of the platform
(§0): **acceptance implies the mathematical statement**. The search, the
producer, and the Rust cross-checker may all be wrong; if `validate` returns
`true`, the tensor identity holds and the certificate's term count bounds the
tensor rank from above.
-/

namespace MatrixMath.Certificate

open MatrixMath.Spec

variable {R : Type*}

/-- Tensor rank at most `r` over `R`: some list of at most `r` rank-one terms
reconstructs `T_{n,m,p}` (§10.4, Appendix D).

Stating the conclusion this way keeps the claim honestly an **upper bound**: a
certificate never proves minimality. -/
def TensorRankLE (R : Type*) [Semiring R] (n m p r : ℕ) : Prop :=
  ∃ terms : List (Term R), terms.length ≤ r ∧ Reconstructs n m p terms

section Semiring
variable [Semiring R] [DecidableEq R]

/-- Acceptance implies the Appendix B.1 reconstruction property. -/
theorem reconstructionHolds_sound {d : Decomposition R}
    (h : reconstructionHolds d = true) : Reconstructs d.n d.m d.p d.semantics := by
  intro a b c ha hb hc
  unfold reconstructionHolds at h
  rw [List.all_eq_true] at h
  have ha' := h a (List.mem_range.mpr ha)
  rw [List.all_eq_true] at ha'
  have hb' := ha' b (List.mem_range.mpr hb)
  rw [List.all_eq_true] at hb'
  exact of_decide_eq_true (hb' c (List.mem_range.mpr hc))

/-- **Checker soundness.** If `validate` accepts a decomposition certificate,
its terms reconstruct the matrix multiplication tensor exactly (B1). -/
theorem validate_sound {d : Decomposition R} (h : validate d = true) :
    Reconstructs d.n d.m d.p d.semantics := by
  unfold validate at h
  simp only [Bool.and_eq_true] at h
  exact reconstructionHolds_sound h.2

/-- **Published Track B claim.** Acceptance bounds the tensor rank above by the
certificate's term count, and by nothing smaller (§10.4). -/
theorem validate_rank_le {d : Decomposition R} (h : validate d = true) :
    TensorRankLE R d.n d.m d.p d.termCount :=
  ⟨d.semantics, by simp [Decomposition.semantics, Decomposition.termCount],
    validate_sound h⟩

end Semiring

section CommRing
variable [CommRing R] [DecidableEq R]

/-- **The algorithmic meaning of acceptance (§10.2, B.3).**

If the checker accepts, the bilinear algorithm the certificate describes
computes the matrix product, with the dual output coordinate undone explicitly.
This is the statement a published Track B result asserts. -/
theorem validate_computes_matmul {d : Decomposition R} (h : validate d = true)
    (A B : ℕ → ℕ → R) {i j : ℕ} (hi : i < d.n) (hj : j < d.p) :
    bilinearProduct d.n d.m d.p d.semantics A B i j = matMul d.m A B i j :=
  reconstructs_bilinear (validate_sound h) A B hi hj

end CommRing

end MatrixMath.Certificate
