/-
Generated certificate module. Do not edit.

canonical sha256 : e6f4ff4dfcb5baac750a04004b495ade7e52a355fbefec578775e12abbbc72c9
claim            : rank_{F2}(T[3,3,3]) <= 23
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
  ⟨[0,0,0,0,0,0,0,1,0], [0,1,0,0,1,0,0,1,0], [0,0,0,0,0,1,0,0,1]⟩,
  ⟨[0,0,0,0,0,0,1,0,0], [0,0,1,0,0,0,0,0,0], [1,0,1,0,0,0,1,0,1]⟩,
  ⟨[0,0,0,0,0,1,0,0,0], [0,0,0,0,0,0,0,0,1], [0,1,0,0,0,0,0,1,1]⟩,
  ⟨[0,0,0,0,0,1,0,0,1], [0,1,0,0,1,1,0,1,1], [0,0,0,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,0,0,1,0,1,1], [0,1,0,0,1,1,0,1,0], [0,0,0,1,1,0,0,0,1]⟩,
  ⟨[0,0,0,0,1,0,0,0,0], [0,0,0,0,0,1,0,0,0], [0,0,0,1,1,0,1,1,0]⟩,
  ⟨[0,0,0,0,1,1,0,1,1], [0,0,0,0,1,1,0,0,0], [0,0,0,1,1,0,0,0,0]⟩,
  ⟨[0,0,0,1,0,0,0,0,0], [0,0,1,0,0,0,0,0,0], [0,1,0,0,0,0,0,1,0]⟩,
  ⟨[0,0,0,1,0,1,0,0,0], [0,0,0,0,0,0,0,1,0], [0,1,0,0,1,1,0,0,0]⟩,
  ⟨[0,0,0,1,0,1,0,1,1], [0,1,0,0,0,0,0,1,0], [0,0,0,1,1,1,0,0,0]⟩,
  ⟨[0,0,0,1,0,1,1,0,1], [0,1,0,0,0,0,0,0,0], [0,0,0,0,0,1,0,0,0]⟩,
  ⟨[0,1,0,0,1,0,0,0,0], [1,0,1,1,0,1,1,0,1], [0,0,0,0,0,0,1,0,0]⟩,
  ⟨[0,1,1,0,0,0,0,0,0], [0,0,0,1,0,0,0,0,0], [1,1,1,0,0,0,0,0,0]⟩,
  ⟨[0,1,1,0,1,0,0,0,0], [1,0,1,1,0,0,1,0,1], [0,1,0,0,0,0,1,0,0]⟩,
  ⟨[0,1,1,0,1,1,0,0,0], [0,0,0,0,0,0,1,1,1], [0,1,0,0,0,0,0,0,0]⟩,
  ⟨[0,1,1,1,1,0,0,0,0], [1,0,1,0,0,0,0,1,0], [0,1,0,1,0,0,0,0,0]⟩,
  ⟨[1,0,0,0,0,0,1,0,0], [1,0,0,1,0,0,1,0,0], [1,0,0,0,0,0,1,0,0]⟩,
  ⟨[1,0,0,1,0,0,0,0,0], [0,1,0,0,1,0,0,1,0], [0,0,0,1,0,0,0,0,0]⟩,
  ⟨[1,0,1,0,0,0,0,0,0], [1,0,1,0,0,0,0,0,0], [1,0,1,1,0,0,0,0,0]⟩,
  ⟨[1,0,1,0,0,0,1,0,0], [1,0,1,1,0,0,1,0,0], [1,0,1,0,0,0,1,0,0]⟩,
  ⟨[1,0,1,0,0,0,1,0,1], [0,0,0,0,0,0,1,0,0], [0,0,1,0,0,0,0,0,0]⟩,
  ⟨[1,1,0,0,0,0,1,1,0], [0,0,0,1,0,0,0,0,0], [0,0,1,0,0,0,0,0,0]⟩,
  ⟨[1,1,0,1,1,0,0,0,0], [1,0,1,0,1,0,0,1,0], [0,0,0,1,0,0,0,0,0]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition (ZMod 2) where
  n := 3
  m := 3
  p := 3
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_e6f4ff4dfcb5baac750a04004b495ade7e52a355fbefec578775e12abbbc72c9 :
    validate certificate = true ∧ certificate.termCount = 23 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{F2}(T[3,3,3]) <= 23**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_e6f4ff4dfcb5baac750a04004b495ade7e52a355fbefec578775e12abbbc72c9 :
    TensorRankLE (ZMod 2) 3 3 3 23 := by
  have h := validate_rank_le cert_e6f4ff4dfcb5baac750a04004b495ade7e52a355fbefec578775e12abbbc72c9.1
  rwa [cert_e6f4ff4dfcb5baac750a04004b495ade7e52a355fbefec578775e12abbbc72c9.2] at h

#print axioms cert_e6f4ff4dfcb5baac750a04004b495ade7e52a355fbefec578775e12abbbc72c9
#print axioms result_e6f4ff4dfcb5baac750a04004b495ade7e52a355fbefec578775e12abbbc72c9

end MatrixMath.Generated
