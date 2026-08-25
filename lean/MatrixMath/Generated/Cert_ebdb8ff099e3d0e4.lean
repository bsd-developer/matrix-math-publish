/-
Generated certificate module. Do not edit.

canonical sha256 : ebdb8ff099e3d0e485bbc49914a34a2e380d164e441cfbaf2ab76d984b1d6dbf
claim            : rank_{F7}(T[2,2,2]) <= 7
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
def shard0 : List (ArrayTerm (ZMod 7)) := [
  ⟨[0,0,0,1], [1,0,6,0], [6,6,0,0]⟩,
  ⟨[0,0,1,1], [1,0,0,0], [0,1,0,6]⟩,
  ⟨[0,1,0,6], [0,0,1,1], [1,0,0,0]⟩,
  ⟨[1,0,0,0], [0,1,0,6], [0,0,1,1]⟩,
  ⟨[1,0,0,1], [1,0,0,1], [1,0,0,1]⟩,
  ⟨[1,0,6,0], [1,1,0,0], [0,0,0,6]⟩,
  ⟨[1,1,0,0], [0,0,0,1], [6,0,1,0]⟩
]

/-- The complete decoded semantic certificate. No node or block is
omitted (§3.5). -/
def certificate : Decomposition (ZMod 7) where
  n := 2
  m := 2
  p := 2
  terms := shard0

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- The closed checker evaluation over the complete certificate. -/
theorem cert_ebdb8ff099e3d0e485bbc49914a34a2e380d164e441cfbaf2ab76d984b1d6dbf :
    validate certificate = true ∧ certificate.termCount = 7 := by
  refine ⟨by native_decide, by rfl⟩

/-- **rank_{F7}(T[2,2,2]) <= 7**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_ebdb8ff099e3d0e485bbc49914a34a2e380d164e441cfbaf2ab76d984b1d6dbf :
    TensorRankLE (ZMod 7) 2 2 2 7 := by
  have h := validate_rank_le cert_ebdb8ff099e3d0e485bbc49914a34a2e380d164e441cfbaf2ab76d984b1d6dbf.1
  rwa [cert_ebdb8ff099e3d0e485bbc49914a34a2e380d164e441cfbaf2ab76d984b1d6dbf.2] at h

#print axioms cert_ebdb8ff099e3d0e485bbc49914a34a2e380d164e441cfbaf2ab76d984b1d6dbf
#print axioms result_ebdb8ff099e3d0e485bbc49914a34a2e380d164e441cfbaf2ab76d984b1d6dbf

end MatrixMath.Generated
