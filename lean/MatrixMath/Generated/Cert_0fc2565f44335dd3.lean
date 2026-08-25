/-
Generated certificate module. Do not edit.

canonical sha256 : 0fc2565f44335dd32b6a14d29a7e96f73cba9a379766f784396c24d15ca69122
claim            : rank_{F2}(T[2,2,2]) <= 7
profile          : CN
spec version     : 2.1.0

This module is hashed publication evidence, not a trusted assumption
(spec §3.3). Its declarations are checked according to §3.4.
-/
import MatrixMath.Certificate.Sound
import Mathlib.Data.ZMod.Basic

namespace MatrixMath.Generated

open MatrixMath.Certificate

/-- Literal shard 0 of the decoded certificate (§3.5). -/
def shard0 : List (ArrayTerm (ZMod 2)) := [
  ⟨[0,0,1,0], [1,1,1,1], [0,1,0,0]⟩,
  ⟨[0,0,1,1], [0,0,1,1], [0,0,1,1]⟩,
  ⟨[0,1,0,0], [0,0,1,0], [1,1,1,1]⟩,
  ⟨[0,1,0,1], [0,1,0,1], [0,1,0,1]⟩,
  ⟨[0,1,1,1], [0,1,1,1], [0,1,1,1]⟩,
  ⟨[1,0,0,0], [1,0,0,0], [1,0,0,0]⟩,
  ⟨[1,1,1,1], [0,1,0,0], [0,0,1,0]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition (ZMod 2) where
  n := 2
  m := 2
  p := 2
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_0fc2565f44335dd32b6a14d29a7e96f73cba9a379766f784396c24d15ca69122 :
    validate certificate = true ∧ certificate.termCount = 7 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{F2}(T[2,2,2]) <= 7**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_0fc2565f44335dd32b6a14d29a7e96f73cba9a379766f784396c24d15ca69122 :
    TensorRankLE (ZMod 2) 2 2 2 7 := by
  have h := validate_rank_le cert_0fc2565f44335dd32b6a14d29a7e96f73cba9a379766f784396c24d15ca69122.1
  rwa [cert_0fc2565f44335dd32b6a14d29a7e96f73cba9a379766f784396c24d15ca69122.2] at h

#print axioms cert_0fc2565f44335dd32b6a14d29a7e96f73cba9a379766f784396c24d15ca69122
#print axioms result_0fc2565f44335dd32b6a14d29a7e96f73cba9a379766f784396c24d15ca69122

end MatrixMath.Generated
