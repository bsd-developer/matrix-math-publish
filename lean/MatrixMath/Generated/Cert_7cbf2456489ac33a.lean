/-
Generated certificate module. Do not edit.

canonical sha256 : 7cbf2456489ac33aaecc18c5198361f0211d17afe35e5d01e35965a597d9fe7e
claim            : rank_{Z}(T[2,3,4]) <= 24
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
  ⟨[0,0,0,0,0,1], [0,0,0,0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,0,0,1], [0,0,0,0,0,0,0,0,0,0,1,0], [0,0,0,0,0,1,0,0]⟩,
  ⟨[0,0,0,0,0,1], [0,0,0,0,0,0,0,0,0,1,0,0], [0,0,0,1,0,0,0,0]⟩,
  ⟨[0,0,0,0,0,1], [0,0,0,0,0,0,0,0,1,0,0,0], [0,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,0,1,0], [0,0,0,0,0,0,0,1,0,0,0,0], [0,0,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,0,1,0], [0,0,0,0,0,0,1,0,0,0,0,0], [0,0,0,0,0,1,0,0]⟩,
  ⟨[0,0,0,0,1,0], [0,0,0,0,0,1,0,0,0,0,0,0], [0,0,0,1,0,0,0,0]⟩,
  ⟨[0,0,0,0,1,0], [0,0,0,0,1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,0,1,0,0], [0,0,0,1,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,1]⟩,
  ⟨[0,0,0,1,0,0], [0,0,1,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,1,0,0]⟩,
  ⟨[0,0,0,1,0,0], [0,1,0,0,0,0,0,0,0,0,0,0], [0,0,0,1,0,0,0,0]⟩,
  ⟨[0,0,0,1,0,0], [1,0,0,0,0,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0]⟩,
  ⟨[0,0,1,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,1], [0,0,0,0,0,0,1,0]⟩,
  ⟨[0,0,1,0,0,0], [0,0,0,0,0,0,0,0,0,0,1,0], [0,0,0,0,1,0,0,0]⟩,
  ⟨[0,0,1,0,0,0], [0,0,0,0,0,0,0,0,0,1,0,0], [0,0,1,0,0,0,0,0]⟩,
  ⟨[0,0,1,0,0,0], [0,0,0,0,0,0,0,0,1,0,0,0], [1,0,0,0,0,0,0,0]⟩,
  ⟨[0,1,0,0,0,0], [0,0,0,0,0,0,0,1,0,0,0,0], [0,0,0,0,0,0,1,0]⟩,
  ⟨[0,1,0,0,0,0], [0,0,0,0,0,0,1,0,0,0,0,0], [0,0,0,0,1,0,0,0]⟩,
  ⟨[0,1,0,0,0,0], [0,0,0,0,0,1,0,0,0,0,0,0], [0,0,1,0,0,0,0,0]⟩,
  ⟨[0,1,0,0,0,0], [0,0,0,0,1,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0]⟩,
  ⟨[1,0,0,0,0,0], [0,0,0,1,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,1,0]⟩,
  ⟨[1,0,0,0,0,0], [0,0,1,0,0,0,0,0,0,0,0,0], [0,0,0,0,1,0,0,0]⟩,
  ⟨[1,0,0,0,0,0], [0,1,0,0,0,0,0,0,0,0,0,0], [0,0,1,0,0,0,0,0]⟩,
  ⟨[1,0,0,0,0,0], [1,0,0,0,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition Int where
  n := 2
  m := 3
  p := 4
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_7cbf2456489ac33aaecc18c5198361f0211d17afe35e5d01e35965a597d9fe7e :
    validate certificate = true ∧ certificate.termCount = 24 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{Z}(T[2,3,4]) <= 24**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_7cbf2456489ac33aaecc18c5198361f0211d17afe35e5d01e35965a597d9fe7e :
    TensorRankLE Int 2 3 4 24 := by
  have h := validate_rank_le cert_7cbf2456489ac33aaecc18c5198361f0211d17afe35e5d01e35965a597d9fe7e.1
  rwa [cert_7cbf2456489ac33aaecc18c5198361f0211d17afe35e5d01e35965a597d9fe7e.2] at h

#print axioms cert_7cbf2456489ac33aaecc18c5198361f0211d17afe35e5d01e35965a597d9fe7e
#print axioms result_7cbf2456489ac33aaecc18c5198361f0211d17afe35e5d01e35965a597d9fe7e

end MatrixMath.Generated
