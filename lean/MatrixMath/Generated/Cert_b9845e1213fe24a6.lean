/-
Generated certificate module. Do not edit.

canonical sha256 : b9845e1213fe24a6f896477ace73da1179397ef3c191989cbea2dccaa5726bb9
claim            : rank_{Z}(T[2,2,2]) <= 7
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
  ⟨[0,0,0,1], [1,0,(-1),0], [(-1),(-1),0,0]⟩,
  ⟨[0,0,1,1], [1,0,0,0], [0,1,0,(-1)]⟩,
  ⟨[0,1,0,(-1)], [0,0,1,1], [1,0,0,0]⟩,
  ⟨[1,0,(-1),0], [1,1,0,0], [0,0,0,(-1)]⟩,
  ⟨[1,0,0,0], [0,1,0,(-1)], [0,0,1,1]⟩,
  ⟨[1,0,0,1], [1,0,0,1], [1,0,0,1]⟩,
  ⟨[1,1,0,0], [0,0,0,1], [(-1),0,1,0]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition Int where
  n := 2
  m := 2
  p := 2
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_b9845e1213fe24a6f896477ace73da1179397ef3c191989cbea2dccaa5726bb9 :
    validate certificate = true ∧ certificate.termCount = 7 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{Z}(T[2,2,2]) <= 7**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_b9845e1213fe24a6f896477ace73da1179397ef3c191989cbea2dccaa5726bb9 :
    TensorRankLE Int 2 2 2 7 := by
  have h := validate_rank_le cert_b9845e1213fe24a6f896477ace73da1179397ef3c191989cbea2dccaa5726bb9.1
  rwa [cert_b9845e1213fe24a6f896477ace73da1179397ef3c191989cbea2dccaa5726bb9.2] at h

#print axioms cert_b9845e1213fe24a6f896477ace73da1179397ef3c191989cbea2dccaa5726bb9
#print axioms result_b9845e1213fe24a6f896477ace73da1179397ef3c191989cbea2dccaa5726bb9

end MatrixMath.Generated
