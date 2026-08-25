/-
Generated certificate module. Do not edit.

canonical sha256 : 349e160c76e0bd25a01d93537eba11e280640d8df390800bd6516048070816d1
claim            : rank_{Q}(T[2,2,2]) <= 7
profile          : CN
spec version     : 2.1.0

This module is hashed publication evidence, not a trusted assumption
(spec §3.3). Its declarations are checked according to §3.4.
-/
import MatrixMath.Certificate.Sound
import Mathlib.Data.Rat.Defs

namespace MatrixMath.Generated

open MatrixMath.Certificate

/-- Literal shard 0 of the decoded certificate (§3.5). -/
def shard0 : List (ArrayTerm Rat) := [
  ⟨[((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))], [((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((-1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))], [((-1 : Rat) / (1 : Rat)),((-1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))]⟩,
  ⟨[((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))], [((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))], [((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((-1 : Rat) / (1 : Rat))]⟩,
  ⟨[((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((-1 : Rat) / (1 : Rat))], [((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))], [((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))]⟩,
  ⟨[((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((-1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))], [((1 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))], [((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((-1 : Rat) / (1 : Rat))]⟩,
  ⟨[((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))], [((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((-1 : Rat) / (1 : Rat))], [((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))]⟩,
  ⟨[((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))], [((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))], [((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))]⟩,
  ⟨[((1 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))], [((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat))], [((-1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat)),((1 : Rat) / (1 : Rat)),((0 : Rat) / (1 : Rat))]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition Rat where
  n := 2
  m := 2
  p := 2
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_349e160c76e0bd25a01d93537eba11e280640d8df390800bd6516048070816d1 :
    validate certificate = true ∧ certificate.termCount = 7 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{Q}(T[2,2,2]) <= 7**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_349e160c76e0bd25a01d93537eba11e280640d8df390800bd6516048070816d1 :
    TensorRankLE Rat 2 2 2 7 := by
  have h := validate_rank_le cert_349e160c76e0bd25a01d93537eba11e280640d8df390800bd6516048070816d1.1
  rwa [cert_349e160c76e0bd25a01d93537eba11e280640d8df390800bd6516048070816d1.2] at h

#print axioms cert_349e160c76e0bd25a01d93537eba11e280640d8df390800bd6516048070816d1
#print axioms result_349e160c76e0bd25a01d93537eba11e280640d8df390800bd6516048070816d1

end MatrixMath.Generated
