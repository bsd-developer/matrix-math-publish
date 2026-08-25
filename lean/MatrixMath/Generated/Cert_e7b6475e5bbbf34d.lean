/-
Generated certificate module. Do not edit.

canonical sha256 : e7b6475e5bbbf34d27f054a475c44537ed3024c8c37abe0002b8197e90107505
claim            : rank_{Z}(T[3,3,3]) <= 27
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
  ⟨[0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,0,1,0], [0,0,0,0,0,1,0,0,0]⟩,
  ⟨[0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,1,0,0], [0,0,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,0,0,0,0,1,0], [0,0,0,0,0,1,0,0,0], [0,0,0,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,0,0,0,0,1,0], [0,0,0,0,1,0,0,0,0], [0,0,0,0,0,1,0,0,0]⟩,
  ⟨[0,0,0,0,0,0,0,1,0], [0,0,0,1,0,0,0,0,0], [0,0,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,0,0,0,1,0,0], [0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,0,0,0,1,0,0], [0,1,0,0,0,0,0,0,0], [0,0,0,0,0,1,0,0,0]⟩,
  ⟨[0,0,0,0,0,0,1,0,0], [1,0,0,0,0,0,0,0,0], [0,0,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,0,0,1,0,0,0], [0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,0,1,0]⟩,
  ⟨[0,0,0,0,0,1,0,0,0], [0,0,0,0,0,0,0,1,0], [0,0,0,0,1,0,0,0,0]⟩,
  ⟨[0,0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0,0], [0,1,0,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,0,1,0,0,0,0], [0,0,0,0,0,1,0,0,0], [0,0,0,0,0,0,0,1,0]⟩,
  ⟨[0,0,0,0,1,0,0,0,0], [0,0,0,0,1,0,0,0,0], [0,0,0,0,1,0,0,0,0]⟩,
  ⟨[0,0,0,0,1,0,0,0,0], [0,0,0,1,0,0,0,0,0], [0,1,0,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,1,0,0,0,0,0], [0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,0,1,0]⟩,
  ⟨[0,0,0,1,0,0,0,0,0], [0,1,0,0,0,0,0,0,0], [0,0,0,0,1,0,0,0,0]⟩,
  ⟨[0,0,0,1,0,0,0,0,0], [1,0,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0,0]⟩,
  ⟨[0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,1,0,0]⟩,
  ⟨[0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,0,1,0], [0,0,0,1,0,0,0,0,0]⟩,
  ⟨[0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,1,0,0], [1,0,0,0,0,0,0,0,0]⟩,
  ⟨[0,1,0,0,0,0,0,0,0], [0,0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0,0]⟩,
  ⟨[0,1,0,0,0,0,0,0,0], [0,0,0,0,1,0,0,0,0], [0,0,0,1,0,0,0,0,0]⟩,
  ⟨[0,1,0,0,0,0,0,0,0], [0,0,0,1,0,0,0,0,0], [1,0,0,0,0,0,0,0,0]⟩,
  ⟨[1,0,0,0,0,0,0,0,0], [0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,1,0,0]⟩,
  ⟨[1,0,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0,0], [0,0,0,1,0,0,0,0,0]⟩,
  ⟨[1,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0,0]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition Int where
  n := 3
  m := 3
  p := 3
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_e7b6475e5bbbf34d27f054a475c44537ed3024c8c37abe0002b8197e90107505 :
    validate certificate = true ∧ certificate.termCount = 27 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{Z}(T[3,3,3]) <= 27**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_e7b6475e5bbbf34d27f054a475c44537ed3024c8c37abe0002b8197e90107505 :
    TensorRankLE Int 3 3 3 27 := by
  have h := validate_rank_le cert_e7b6475e5bbbf34d27f054a475c44537ed3024c8c37abe0002b8197e90107505.1
  rwa [cert_e7b6475e5bbbf34d27f054a475c44537ed3024c8c37abe0002b8197e90107505.2] at h

#print axioms cert_e7b6475e5bbbf34d27f054a475c44537ed3024c8c37abe0002b8197e90107505
#print axioms result_e7b6475e5bbbf34d27f054a475c44537ed3024c8c37abe0002b8197e90107505

end MatrixMath.Generated
