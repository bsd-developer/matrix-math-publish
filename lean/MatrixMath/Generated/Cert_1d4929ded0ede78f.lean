/-
Generated certificate module. Do not edit.

canonical sha256 : 1d4929ded0ede78fc604956edd6b2acea548ee643e596bccb47535ddd1fe6089
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
  ⟨[0,0,0,1], [0,1,0,1], [0,(-1),0,1]⟩,
  ⟨[0,0,1,(-1)], [0,1,0,0], [0,0,(-1),1]⟩,
  ⟨[0,1,0,0], [0,0,1,0], [1,0,(-1),0]⟩,
  ⟨[1,(-1),1,(-1)], [0,0,1,1], [0,0,(-1),0]⟩,
  ⟨[1,0,0,0], [1,0,0,0], [1,(-1),0,0]⟩,
  ⟨[1,0,1,(-1)], [0,1,1,1], [0,(-1),1,0]⟩,
  ⟨[1,0,1,0], [1,1,1,1], [0,1,0,0]⟩
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
theorem cert_1d4929ded0ede78fc604956edd6b2acea548ee643e596bccb47535ddd1fe6089 :
    validate certificate = true ∧ certificate.termCount = 7 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{Z}(T[2,2,2]) <= 7**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_1d4929ded0ede78fc604956edd6b2acea548ee643e596bccb47535ddd1fe6089 :
    TensorRankLE Int 2 2 2 7 := by
  have h := validate_rank_le cert_1d4929ded0ede78fc604956edd6b2acea548ee643e596bccb47535ddd1fe6089.1
  rwa [cert_1d4929ded0ede78fc604956edd6b2acea548ee643e596bccb47535ddd1fe6089.2] at h

#print axioms cert_1d4929ded0ede78fc604956edd6b2acea548ee643e596bccb47535ddd1fe6089
#print axioms result_1d4929ded0ede78fc604956edd6b2acea548ee643e596bccb47535ddd1fe6089

end MatrixMath.Generated
