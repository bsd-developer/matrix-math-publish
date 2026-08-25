import MatrixMath.Spec.Tensor

/-!
# Decomposition certificate validation

Normative source: `docs/specs/0001_spec.md` §6.6, §10.4, Appendix B.1.

This module holds the **executable** side of the Track B checker: a total,
decidable predicate over a concrete array representation. `MatrixMath.Certificate.Sound`
proves that acceptance implies the Appendix B.1 reconstruction property, and
hence (through `MatrixMath.Spec.reconstructs_bilinear`) that the certificate
describes an algorithm computing `C = A * B`.

The representation is **lists** of ring elements with out-of-range reads
returning zero, matching the Rust decoder's `getD _ 0` and the canonical
certificate grammar of §6.6. Lists rather than arrays is a deliberate choice:
`Array` operations in Lean core are compiled loops that do not reduce in the
kernel, so an array representation would silently force every result to profile
CN. Structural list recursion keeps profile CK (§3.4) reachable.
-/

namespace MatrixMath.Certificate

open MatrixMath.Spec

variable {R : Type*}

/-- One rank-one summand in its concrete array representation. -/
structure ArrayTerm (R : Type*) where
  /-- The left factor, of length `n*m`. -/
  u : List R
  /-- The right factor, of length `m*p`. -/
  v : List R
  /-- The dual-output factor, of length `p*n`. -/
  w : List R
  deriving Repr, DecidableEq

/-- Reinterpret an array factor as the total function the specification uses,
reading out of range as zero. -/
def arrayFn [Zero R] (a : List R) : ℕ → R := fun i => a.getD i 0

/-- The semantic term denoted by a concrete term. -/
def ArrayTerm.toTerm [Zero R] (t : ArrayTerm R) : Term R :=
  { u := arrayFn t.u, v := arrayFn t.v, w := arrayFn t.w }

/-- A decoded decomposition certificate (§6.6).

`n`, `m`, and `p` come from the certificate's `claim`; `terms` from its payload.
Nothing here is trusted until [`validate`] accepts it. -/
structure Decomposition (R : Type*) where
  /-- Rows of `A` and of `C`. -/
  n : ℕ
  /-- The shared inner dimension. -/
  m : ℕ
  /-- Columns of `B` and of `C`. -/
  p : ℕ
  /-- The ordered list of nonzero terms. -/
  terms : List (ArrayTerm R)
  deriving Repr

/-- The semantic term list denoted by a certificate. -/
def Decomposition.semantics [Zero R] (d : Decomposition R) : List (Term R) :=
  d.terms.map ArrayTerm.toTerm

/-- The declared term count. This is a **term count**, never a proven tensor
rank (§10.4). -/
def Decomposition.termCount (d : Decomposition R) : ℕ := d.terms.length

/-! ## Structural validation (§0.2, §6.6) -/

/-- Version 1 accepts dimensions in `1..=12` (§0.2). -/
def dimensionsSupported (d : Decomposition R) : Bool :=
  1 ≤ d.n && d.n ≤ 12 && 1 ≤ d.m && d.m ≤ 12 && 1 ≤ d.p && d.p ≤ 12

/-- Every factor has the length its tensor mode requires (§6.6). -/
def lengthsValid (d : Decomposition R) : Bool :=
  d.terms.all fun t =>
    t.u.length == d.n * d.m && t.v.length == d.m * d.p && t.w.length == d.p * d.n

/-- No canonical term contains an all-zero factor (§6.6). -/
def noZeroFactor [Zero R] [DecidableEq R] (d : Decomposition R) : Bool :=
  d.terms.all fun t =>
    (t.u.any fun x => decide (x ≠ 0)) && (t.v.any fun x => decide (x ≠ 0)) &&
      (t.w.any fun x => decide (x ≠ 0))

/-! ## Reconstruction (B1) -/

section Semiring
variable [Semiring R] [DecidableEq R]

/-- The reconstruction check: `T_{n,m,p} = Σ_r u_r ⊗ v_r ⊗ w_r` entrywise over
the whole coordinate box (B1).

Deliberately written with `List.range` and `List.all` rather than a bounded
`∀` quantifier. `Nat.decidableBallLT` is defined by well-founded recursion, so a
bounded quantifier does not reduce in the kernel and would force every result to
profile CN. Structural list recursion reduces, which keeps profile CK (§3.4)
reachable for small certificates. -/
def reconstructionHolds (d : Decomposition R) : Bool :=
  (List.range (d.n * d.m)).all fun a =>
    (List.range (d.m * d.p)).all fun b =>
      (List.range (d.p * d.n)).all fun c =>
        decide (sumEntry d.semantics a b c = targetCoeff R d.n d.m d.p a b c)

/-- The full certificate validator (§6.6, B1).

Structural validity is checked before reconstruction so that a malformed
certificate is rejected for the structural reason, deterministically (§5.4). -/
def validate (d : Decomposition R) : Bool :=
  dimensionsSupported d && lengthsValid d && noZeroFactor d && reconstructionHolds d

end Semiring

end MatrixMath.Certificate
