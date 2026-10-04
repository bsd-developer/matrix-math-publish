/-
Generated certificate module. Do not edit.

canonical sha256 : c5bb171443bb54f0065a95dfbb78b39accd9c8aa9fb18fa0480db74ae5912f0b
claim            : rank_{Z}(T[1,1,1]) <= 1
profile          : CN
spec version     : 2.1.0

This module is hashed publication evidence, not a trusted assumption
(spec §3.3). Its declarations are checked according to §3.4.
-/
import MatrixMath.Certificate.Sound

namespace MatrixMath.Generated

open MatrixMath.Certificate

/-- Literal shard 0 of the decoded certificate (§3.5). -/
def shard0 : List (ArrayTerm Int) := [
  ⟨[1], [1], [1]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition Int where
  n := 1
  m := 1
  p := 1
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_c5bb171443bb54f0065a95dfbb78b39accd9c8aa9fb18fa0480db74ae5912f0b :
    validate certificate = true ∧ certificate.termCount = 1 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{Z}(T[1,1,1]) <= 1**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_c5bb171443bb54f0065a95dfbb78b39accd9c8aa9fb18fa0480db74ae5912f0b :
    TensorRankLE Int 1 1 1 1 := by
  have h := validate_rank_le cert_c5bb171443bb54f0065a95dfbb78b39accd9c8aa9fb18fa0480db74ae5912f0b.1
  rwa [cert_c5bb171443bb54f0065a95dfbb78b39accd9c8aa9fb18fa0480db74ae5912f0b.2] at h

#print axioms cert_c5bb171443bb54f0065a95dfbb78b39accd9c8aa9fb18fa0480db74ae5912f0b
#print axioms result_c5bb171443bb54f0065a95dfbb78b39accd9c8aa9fb18fa0480db74ae5912f0b

end MatrixMath.Generated
