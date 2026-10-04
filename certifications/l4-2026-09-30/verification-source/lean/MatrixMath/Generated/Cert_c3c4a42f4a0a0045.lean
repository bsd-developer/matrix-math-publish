/-
Generated certificate module. Do not edit.

canonical sha256 : c3c4a42f4a0a0045a6ce5f624d93b3d6274f37d43b6a6980e67fe9234e2298d7
claim            : rank_{F2}(T[3,3,3]) <= 23
profile          : CK
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
  ⟨[0,0,0,0,0,0,1,0,0], [0,0,1,0,1,0,0,1,1], [0,0,1,0,0,1,0,0,1]⟩,
  ⟨[0,0,0,0,0,0,1,0,1], [0,0,0,0,1,1,0,1,1], [0,0,1,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,0,0,0,1,1,0], [0,0,0,0,1,0,0,1,0], [0,0,0,0,1,1,0,1,1]⟩,
  ⟨[0,0,0,0,0,0,1,1,1], [0,0,0,0,1,1,0,1,0], [0,0,0,0,0,0,0,1,1]⟩,
  ⟨[0,0,0,0,1,0,0,0,0], [0,1,1,1,0,0,1,0,0], [0,1,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,0,1,0,1,1,1], [0,1,1,0,1,1,0,1,1], [0,0,1,0,0,0,0,1,0]⟩,
  ⟨[0,0,0,0,1,1,0,0,0], [0,0,0,0,0,0,0,1,0], [1,1,1,1,1,1,1,0,0]⟩,
  ⟨[0,0,0,0,1,1,0,1,1], [0,1,1,0,0,0,0,1,1], [0,0,1,0,0,1,1,0,0]⟩,
  ⟨[0,0,0,0,1,1,1,1,1], [0,1,1,0,0,0,0,0,1], [0,0,1,0,0,1,0,1,0]⟩,
  ⟨[0,0,1,0,0,1,0,0,1], [1,0,1,1,0,1,1,0,1], [0,0,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,1,0,0,1,1,1,0], [1,0,1,0,1,0,0,1,0], [0,0,1,0,1,0,0,1,0]⟩,
  ⟨[0,0,1,0,1,1,0,0,0], [1,1,0,0,1,0,1,0,0], [1,0,1,1,1,0,1,1,0]⟩,
  ⟨[0,0,1,0,1,1,0,1,1], [1,1,0,1,0,1,0,1,1], [0,0,1,0,0,0,1,0,0]⟩,
  ⟨[0,1,0,0,0,0,0,0,0], [1,1,0,1,1,0,0,0,0], [1,0,0,0,0,0,1,0,0]⟩,
  ⟨[0,1,1,0,1,1,0,0,0], [0,1,0,0,1,0,0,0,0], [1,0,0,1,0,0,1,0,0]⟩,
  ⟨[0,1,1,0,1,1,0,1,1], [1,0,1,1,0,1,0,0,0], [0,0,0,0,0,0,1,0,0]⟩,
  ⟨[1,1,0,0,0,0,0,0,0], [1,1,0,0,0,0,1,1,0], [0,0,0,1,1,0,1,1,0]⟩,
  ⟨[1,1,0,1,1,0,1,1,0], [1,0,1,0,0,0,0,0,0], [0,0,0,0,1,0,0,1,0]⟩,
  ⟨[1,1,1,0,0,0,0,0,0], [0,1,1,0,0,0,0,0,0], [1,1,0,0,0,0,1,1,0]⟩,
  ⟨[1,1,1,0,0,0,0,0,0], [0,1,1,0,0,0,1,1,0], [1,1,0,0,0,0,0,0,0]⟩,
  ⟨[1,1,1,0,1,1,0,0,0], [1,0,0,0,0,0,1,1,0], [1,1,0,1,1,0,1,1,0]⟩,
  ⟨[1,1,1,1,0,1,0,0,0], [0,1,1,0,0,0,0,0,0], [0,1,0,0,0,0,0,1,0]⟩,
  ⟨[1,1,1,1,1,1,0,0,0], [1,1,1,0,0,0,0,0,0], [0,1,0,0,1,0,0,1,0]⟩
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
theorem cert_c3c4a42f4a0a0045a6ce5f624d93b3d6274f37d43b6a6980e67fe9234e2298d7 :
    validate certificate = true ∧ certificate.termCount = 23 := by
  refine ⟨by decide, by rfl⟩

/-- **rank_{F2}(T[3,3,3]) <= 23**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_c3c4a42f4a0a0045a6ce5f624d93b3d6274f37d43b6a6980e67fe9234e2298d7 :
    TensorRankLE (ZMod 2) 3 3 3 23 := by
  have h := validate_rank_le cert_c3c4a42f4a0a0045a6ce5f624d93b3d6274f37d43b6a6980e67fe9234e2298d7.1
  rwa [cert_c3c4a42f4a0a0045a6ce5f624d93b3d6274f37d43b6a6980e67fe9234e2298d7.2] at h

#print axioms cert_c3c4a42f4a0a0045a6ce5f624d93b3d6274f37d43b6a6980e67fe9234e2298d7
#print axioms result_c3c4a42f4a0a0045a6ce5f624d93b3d6274f37d43b6a6980e67fe9234e2298d7

end MatrixMath.Generated
