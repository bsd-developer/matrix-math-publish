/-
Generated certificate module. Do not edit.

canonical sha256 : 8279ee2823559de9c328a7020ad12c5ace87aed446fe054abe513c9a9c530abb
claim            : rank_{Z}(T[3,3,3]) <= 23
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
  ⟨[0,0,0,0,0,0,0,0,1], [1,0,0,0,0,0,(-1),1,0], [0,0,(-1),0,0,0,0,0,(-1)]⟩,
  ⟨[0,0,0,0,0,0,0,1,0], [0,1,0,(-1),1,0,0,0,0], [0,0,0,0,1,1,0,0,(-1)]⟩,
  ⟨[0,0,0,0,0,0,1,(-1),0], [0,1,0,0,0,0,0,0,0], [0,0,0,1,1,1,0,0,0]⟩,
  ⟨[0,0,0,0,0,0,1,0,1], [1,0,0,0,0,0,0,0,0], [1,(-2),1,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,0,1,(-1),0,(-1),0], [0,0,0,1,0,0,0,1,0], [0,0,(-1),0,(-1),(-1),0,0,(-1)]⟩,
  ⟨[0,0,0,0,1,(-1),0,(-1),1], [0,0,0,0,0,0,0,1,0], [0,0,1,0,0,1,0,0,1]⟩,
  ⟨[0,0,0,0,1,(-1),0,0,0], [0,0,0,1,0,0,0,0,0], [(-1),1,1,(-1),1,1,(-1),1,1]⟩,
  ⟨[0,0,0,0,1,0,0,(-1),0], [0,1,0,0,(-1),0,0,(-1),0], [0,0,0,0,(-1),0,0,0,0]⟩,
  ⟨[0,0,0,1,0,0,2,0,2], [1,0,0,(-1),0,0,(-1),0,0], [0,1,0,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,1,0,1,2,0,2], [0,0,0,1,0,0,1,0,0], [0,1,0,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,1,1,0,(-1),(-1),0], [0,1,0,0,0,0,0,0,0], [0,0,0,0,1,0,0,0,0]⟩,
  ⟨[0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,0,1,(-1)], [0,0,0,1,0,0,0,0,0]⟩,
  ⟨[0,1,(-1),0,1,(-1),0,0,0], [0,0,0,0,0,0,0,0,1], [(-1),0,0,(-1),0,0,(-1),0,0]⟩,
  ⟨[0,1,0,(-1),1,0,0,0,0], [0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,0,(-1),0]⟩,
  ⟨[0,1,0,0,0,0,0,0,0], [0,0,0,1,0,(-1),0,0,0], [0,0,0,1,0,0,(-1),1,0]⟩,
  ⟨[0,1,0,0,1,(-1),0,0,0], [0,0,0,1,0,0,0,0,1], [1,0,0,1,0,0,1,(-1),0]⟩,
  ⟨[0,1,0,0,1,0,0,0,0], [0,0,1,0,0,1,0,0,1], [0,0,0,0,0,0,0,1,0]⟩,
  ⟨[1,(-1),0,0,0,0,(-1),1,0], [0,0,0,2,(-1),(-1),0,0,0], [0,0,0,1,0,0,0,0,0]⟩,
  ⟨[1,0,0,0,0,0,(-1),0,(-1)], [1,0,0,0,0,0,(-1),0,1], [1,0,0,0,0,0,0,0,(-1)]⟩,
  ⟨[1,0,0,0,0,0,(-1),0,0], [1,(-1),(-1),2,(-1),(-1),(-1),0,1], [0,0,0,0,0,0,0,0,1]⟩,
  ⟨[1,0,0,0,0,0,(-1),1,0], [0,1,0,(-2),1,1,0,0,0], [0,0,0,1,0,0,0,0,1]⟩,
  ⟨[1,0,0,0,0,0,0,0,0], [0,0,1,0,0,0,0,0,0], [0,0,0,0,0,0,1,0,1]⟩,
  ⟨[1,0,1,0,0,0,(-1),0,(-1)], [0,0,0,0,0,0,1,0,(-1)], [1,0,0,0,0,0,0,0,0]⟩
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
theorem cert_8279ee2823559de9c328a7020ad12c5ace87aed446fe054abe513c9a9c530abb :
    validate certificate = true ∧ certificate.termCount = 23 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{Z}(T[3,3,3]) <= 23**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_8279ee2823559de9c328a7020ad12c5ace87aed446fe054abe513c9a9c530abb :
    TensorRankLE Int 3 3 3 23 := by
  have h := validate_rank_le cert_8279ee2823559de9c328a7020ad12c5ace87aed446fe054abe513c9a9c530abb.1
  rwa [cert_8279ee2823559de9c328a7020ad12c5ace87aed446fe054abe513c9a9c530abb.2] at h

#print axioms cert_8279ee2823559de9c328a7020ad12c5ace87aed446fe054abe513c9a9c530abb
#print axioms result_8279ee2823559de9c328a7020ad12c5ace87aed446fe054abe513c9a9c530abb

end MatrixMath.Generated
