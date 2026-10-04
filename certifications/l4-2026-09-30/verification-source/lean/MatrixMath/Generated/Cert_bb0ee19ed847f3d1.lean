/-
Generated certificate module. Do not edit.

canonical sha256 : bb0ee19ed847f3d1cfb3a64761b82bb3c0ae0304d0e1ea051baa6b8af1986b29
claim            : rank_{F2}(T[2,2,2]) <= 7
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
  ⟨[0,0,1,0], [1,0,1,0], [1,1,0,0]⟩,
  ⟨[0,0,1,1], [0,0,1,0], [0,1,0,1]⟩,
  ⟨[0,1,0,0], [0,1,0,1], [0,0,1,1]⟩,
  ⟨[0,1,0,1], [0,0,1,1], [0,0,0,1]⟩,
  ⟨[0,1,1,0], [0,1,1,0], [1,0,0,1]⟩,
  ⟨[1,0,1,0], [1,1,0,0], [1,0,0,0]⟩,
  ⟨[1,1,0,0], [0,1,0,0], [1,0,1,0]⟩
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
theorem cert_bb0ee19ed847f3d1cfb3a64761b82bb3c0ae0304d0e1ea051baa6b8af1986b29 :
    validate certificate = true ∧ certificate.termCount = 7 := by
  refine ⟨by decide, by rfl⟩

/-- **rank_{F2}(T[2,2,2]) <= 7**

Follows from the general soundness theorem applied to the closed
evaluation above; the term count is a bound, never a minimality claim
(§10.4). -/
theorem result_bb0ee19ed847f3d1cfb3a64761b82bb3c0ae0304d0e1ea051baa6b8af1986b29 :
    TensorRankLE (ZMod 2) 2 2 2 7 := by
  have h := validate_rank_le cert_bb0ee19ed847f3d1cfb3a64761b82bb3c0ae0304d0e1ea051baa6b8af1986b29.1
  rwa [cert_bb0ee19ed847f3d1cfb3a64761b82bb3c0ae0304d0e1ea051baa6b8af1986b29.2] at h

#print axioms cert_bb0ee19ed847f3d1cfb3a64761b82bb3c0ae0304d0e1ea051baa6b8af1986b29
#print axioms result_bb0ee19ed847f3d1cfb3a64761b82bb3c0ae0304d0e1ea051baa6b8af1986b29

end MatrixMath.Generated
