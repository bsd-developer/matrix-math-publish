import MatrixMath.Schema.Canonical
import MatrixMath.Certificate.Sound
import MatrixMath.Spec.Gaussian
import Mathlib.Data.ZMod.Basic

/-!
# Total, resource-bounded canonical decoder

Normative source: `docs/specs/0001_spec.md` §3.1, §6.1–§6.4, §17.5.

§3.1 puts *decode* inside the Lean box: the authoritative path is
`decode → validate domains → exact evaluation → verdict`, and §17.5 rejects a
soundness theorem stated only for prevalidated data when the publication command
accepts bytes. This module is that decoder.

Two design choices are worth stating because they are not obvious:

**The parser expects keys in canonical order rather than dispatching on them.**
§6.3 requires object keys to be strictly ascending, so for a fixed schema the key
sequence is known in advance. Expecting it positionally makes canonical order
impossible to violate silently — a certificate with permuted keys fails at the
first mismatched byte rather than being accepted and re-serialized differently.

**String escapes are rejected outright.** §6.3 permits `\u00xx` for control
characters, but no string in the version 1 certificate grammar contains one: the
schema id, kind, spec version, source hashes, and numeric strings are all plain
ASCII. Rejecting escapes is therefore not a restriction on the grammar, and it
removes an entire class of "two spellings of one value".

Scope: every version 1 decomposition ring — `Fp`, `Z`, `Q`, and `Qi`. The ring
tag selects the coefficient grammar, and §6.2's canonical rational rules are
enforced here rather than assumed: a denominator of zero, a non-coprime pair, a
leading zero, a `+` sign, or `-0` is a rejection. Nothing is normalized on the
way in, because normalizing would make two spellings of one value both
acceptable and the certificate identity ambiguous.
-/

namespace MatrixMath.Schema

open MatrixMath.Certificate MatrixMath.Spec

/-- The decoder's position and resource counters (§6.4). -/
structure Cursor where
  /-- The input bytes. -/
  bytes : ByteArray
  /-- The current offset. -/
  pos : Nat
  /-- Rational values decoded so far, checked against the §6.4 ceiling. -/
  rationals : Nat

-- A decoding step is `Except DecodeError (α × Cursor)`, written out at every
-- signature rather than hidden behind an abbreviation: an abbreviation of that
-- shape makes `do` notation try to use it as the monad, which fails
-- confusingly.

namespace Cursor

/-- The byte at the cursor, if any. -/
def peek (c : Cursor) : Option UInt8 :=
  if h : c.pos < c.bytes.size then some c.bytes[c.pos] else none

/-- Advance by one byte. -/
def next (c : Cursor) : Cursor := { c with pos := c.pos + 1 }

/-- Whether every byte has been consumed. -/
def atEnd (c : Cursor) : Bool := c.bytes.size ≤ c.pos

end Cursor

/-- Consume one expected byte, or reject (§6.3). -/
def expectByte (b : UInt8) (c : Cursor) : Except DecodeError (Unit × Cursor) :=
  match c.peek with
  | some got => if got == b then .ok ((), c.next) else .error (.noncanonicalJson c.pos)
  | none => .error (.invalidJson c.pos)

/-- Consume an expected literal byte sequence. -/
def expectBytes (expected : List UInt8) (c : Cursor) : Except DecodeError (Unit × Cursor) :=
  match expected with
  | [] => .ok ((), c)
  | b :: rest => do
      let (_, c) ← expectByte b c
      expectBytes rest c

/-- Consume an expected ASCII literal. -/
def expectString (s : String) (c : Cursor) : Except DecodeError (Unit × Cursor) :=
  expectBytes s.toUTF8.toList c

/-- Read a canonical non-negative JSON integer (§6.2).

Rejects a leading zero, a sign, a fraction, and an exponent: §6.2 restricts JSON
numbers to canonical non-negative integers because every mathematical magnitude
travels as a decimal string instead. -/
def readNat (limits : Limits) (c : Cursor) : Except DecodeError (Nat × Cursor) :=
  let rec go (fuel : Nat) (acc : Nat) (digits : Nat) (c : Cursor) : Except DecodeError ((Nat × Nat) × Cursor) :=
    match fuel with
    | 0 => .error (.resourceLimit)
    | fuel + 1 =>
      match c.peek with
      | some b =>
        if isDigit b then
          if digits + 1 > limits.maxDigits then .error .resourceLimit
          else go fuel (acc * 10 + digitValue b) (digits + 1) c.next
        else .ok ((acc, digits), c)
      | none => .ok ((acc, digits), c)
  match c.peek with
  | none => .error (.invalidJson c.pos)
  | some first =>
    if !isDigit first then .error (.noncanonicalJson c.pos)
    else if first == 0x30 then
      -- "0" is canonical only when no digit follows.
      let c := c.next
      match c.peek with
      | some b => if isDigit b then .error (.noncanonicalJson c.pos) else .ok (0, c)
      | none => .ok (0, c)
    else do
      let ((value, _), c) ← go (c.bytes.size + 1) 0 0 c
      .ok (value, c)

/-- Read a JSON string with **no escapes** (§6.3, see the module docstring).

Returns the raw bytes so a caller can check a numeric grammar without a round
trip through `String`. -/
def readStringBytes (c : Cursor) : Except DecodeError ((List UInt8) × Cursor) :=
  let rec go (fuel : Nat) (acc : List UInt8) (c : Cursor) : Except DecodeError ((List UInt8) × Cursor) :=
    match fuel with
    | 0 => .error .resourceLimit
    | fuel + 1 =>
      match c.peek with
      | none => .error (.invalidJson c.pos)
      | some b =>
        if b == 0x22 then .ok (acc.reverse, c.next)
        else if b == 0x5C then .error (.noncanonicalJson c.pos)
        else if b < 0x20 then .error (.invalidJson c.pos)
        else go fuel (b :: acc) c.next
  do
    let (_, c) ← expectByte 0x22 c
    go (c.bytes.size + 1) [] c

/-- Read a string and compare it against an expected ASCII literal. -/
def readExpectedString (expected : String) (err : DecodeError) (c : Cursor) :
    Except DecodeError (Unit × Cursor) := do
  let (bytes, c) ← readStringBytes c
  if bytes == expected.toUTF8.toList then .ok ((), c) else .error err

/-- Read a canonical `Fp` coefficient: a JSON integer in `[0, p)` (§6.6). -/
def readFieldElement (limits : Limits) (modulus : Nat) (c : Cursor) : Except DecodeError (Nat × Cursor) := do
  if c.rationals + 1 > limits.maxRationals then .error .resourceLimit else
  let (value, c) ← readNat limits c
  if value ≥ modulus then .error (.badRationalGrammar c.pos)
  else .ok (value, { c with rationals := c.rationals + 1 })

/-! ## The §6.2 numeric string grammar

`Fp` coefficients are JSON integers; every other ring's coefficients travel as
decimal strings inside objects, because §6.2 puts any magnitude that can exceed
the safe JSON integer range into a string. The parsers below are total and take
the raw bytes, so a canonicality violation is a rejection at a byte offset rather
than a silent reinterpretation.
-/

/-- Parse a canonical decimal natural from raw string bytes (§6.2).

Rejects an empty string, a non-digit, more than `maxDigits` digits, and a leading
zero on anything but `"0"` itself. -/
def parseCanonicalNat (maxDigits : Nat) (bytes : List UInt8) : Option Nat :=
  match bytes with
  | [] => none
  | first :: rest =>
    if !isDigit first then none
    else if first == 0x30 && !rest.isEmpty then none
    else if bytes.length > maxDigits then none
    else
      let rec go (todo : List UInt8) (acc : Nat) : Option Nat :=
        match todo with
        | [] => some acc
        | b :: more => if isDigit b then go more (acc * 10 + digitValue b) else none
      go bytes 0

/-- Parse a canonical decimal integer from raw string bytes (§6.2).

`-0` is rejected: §6.2 encodes zero only as `"0"`, so admitting the negative
spelling would give one value two canonical byte sequences. -/
def parseCanonicalInt (maxDigits : Nat) (bytes : List UInt8) : Option Int :=
  match bytes with
  | 0x2D :: rest =>
    match parseCanonicalNat maxDigits rest with
    | some 0 => none
    | some value => some (-(value : Int))
    | none => none
  | _ => (parseCanonicalNat maxDigits bytes).map (fun value => (value : Int))

/-- Read a canonical `Z` coefficient: a decimal integer string (§6.6). -/
def readIntCoefficient (limits : Limits) (c : Cursor) :
    Except DecodeError (Int × Cursor) := do
  if c.rationals + 1 > limits.maxRationals then .error .resourceLimit else
  let (bytes, c) ← readStringBytes c
  match parseCanonicalInt limits.maxDigits bytes with
  | some value => .ok (value, { c with rationals := c.rationals + 1 })
  | none => .error (.badRationalGrammar c.pos)

/-- Read a canonical rational object `{"d":"...","n":"..."}` (§6.2).

The denominator must be strictly positive and coprime to the numerator. Coprimality
also settles the zero case on its own: `gcd 0 d = d`, so `gcd = 1` forces `d = 1`,
which is exactly §6.2's "zero encoded only as `{n:0,d:1}`". -/
def readRationalObject (limits : Limits) (c : Cursor) :
    Except DecodeError (Rat × Cursor) := do
  if c.rationals + 1 > limits.maxRationals then .error .resourceLimit else
  let (_, c) ← expectString "{\"d\":" c
  let (denominatorBytes, c) ← readStringBytes c
  let (_, c) ← expectString ",\"n\":" c
  let (numeratorBytes, c) ← readStringBytes c
  let (_, c) ← expectByte 0x7D c
  match parseCanonicalNat limits.maxDigits denominatorBytes,
        parseCanonicalInt limits.maxDigits numeratorBytes with
  | some denominator, some numerator =>
    if denominator == 0 then .error (.badRationalGrammar c.pos)
    else if Nat.gcd numerator.natAbs denominator != 1 then
      .error (.badRationalGrammar c.pos)
    else .ok (mkRat numerator denominator, { c with rationals := c.rationals + 1 })
  | _, _ => .error (.badRationalGrammar c.pos)

/-- Read a canonical Gaussian rational object `{"im":…,"re":…}` (§6.6, B.7). -/
def readGaussianObject (limits : Limits) (c : Cursor) :
    Except DecodeError (GaussianRat × Cursor) := do
  let (_, c) ← expectString "{\"im\":" c
  let (im, c) ← readRationalObject limits c
  let (_, c) ← expectString ",\"re\":" c
  let (re, c) ← readRationalObject limits c
  let (_, c) ← expectByte 0x7D c
  .ok (⟨re, im⟩, c)

/-! ## Terms, over any coefficient grammar -/

/-- Read a JSON array of coefficients of a required length. -/
def readFactorOf {α : Type} (readOne : Cursor → Except DecodeError (α × Cursor))
    (len : Nat) (c : Cursor) : Except DecodeError ((List α) × Cursor) :=
  let rec go (remaining : Nat) (acc : List α) (c : Cursor) :
      Except DecodeError ((List α) × Cursor) :=
    match remaining with
    | 0 => do
        let (_, c) ← expectByte 0x5D c   -- ']'
        .ok (acc.reverse, c)
    | remaining + 1 => do
        let (value, c) ← readOne c
        if remaining = 0 then go 0 (value :: acc) c
        else do
          let (_, c) ← expectByte 0x2C c  -- ','
          go remaining (value :: acc) c
  do
    let (_, c) ← expectByte 0x5B c        -- '['
    if len = 0 then
      -- A zero-length factor cannot occur for a supported instance (§0.2).
      .error .wrongVectorLength
    else go len [] c

/-- Read one term `[[u...],[v...],[w...]]`. -/
def readTermOf {α : Type} (readOne : Cursor → Except DecodeError (α × Cursor))
    (lenA lenB lenC : Nat) (c : Cursor) : Except DecodeError (ArrayTerm α × Cursor) := do
  let (_, c) ← expectByte 0x5B c
  let (u, c) ← readFactorOf readOne lenA c
  let (_, c) ← expectByte 0x2C c
  let (v, c) ← readFactorOf readOne lenB c
  let (_, c) ← expectByte 0x2C c
  let (w, c) ← readFactorOf readOne lenC c
  let (_, c) ← expectByte 0x5D c
  .ok ({ u := u, v := v, w := w }, c)

/-- Read the term array of a declared length. -/
def readTermsOf {α : Type} (readOne : Cursor → Except DecodeError (α × Cursor))
    (lenA lenB lenC count : Nat) (c : Cursor) :
    Except DecodeError ((List (ArrayTerm α)) × Cursor) :=
  let rec go (remaining : Nat) (acc : List (ArrayTerm α)) (c : Cursor) :
      Except DecodeError ((List (ArrayTerm α)) × Cursor) :=
    match remaining with
    | 0 => do
        let (_, c) ← expectByte 0x5D c
        .ok (acc.reverse, c)
    | remaining + 1 => do
        let (term, c) ← readTermOf readOne lenA lenB lenC c
        if remaining = 0 then go 0 (term :: acc) c
        else do
          let (_, c) ← expectByte 0x2C c
          go remaining (term :: acc) c
  do
    let (_, c) ← expectByte 0x5B c
    if count = 0 then .error .countMismatch else go count [] c

/-- The decoded payload, tagged by the ring the certificate declares (§6.6).

The ring is part of the decoded value rather than a separate field, so no
downstream function can read `Fp` terms as if they were `Q` terms: the two do not
have the same type. -/
inductive RawPayload where
  /-- `Fp`: a prime modulus and coefficients in `[0, p)`. -/
  | fp (modulus : Nat) (terms : List (ArrayTerm Nat))
  /-- `Z`: canonical decimal integer strings. -/
  | z (terms : List (ArrayTerm Int))
  /-- `Q`: canonical rational objects (§6.2). -/
  | q (terms : List (ArrayTerm Rat))
  /-- `Qi`: canonical Gaussian rational objects (B.7). -/
  | qi (terms : List (ArrayTerm GaussianRat))
  deriving Repr

/-- The number of decoded terms, whatever the ring. -/
def RawPayload.length : RawPayload → Nat
  | .fp _ terms => terms.length
  | .z terms => terms.length
  | .q terms => terms.length
  | .qi terms => terms.length

/-- A decoded decomposition certificate. -/
structure RawCertificate where
  /-- Rows of `A` and of `C`. -/
  n : Nat
  /-- The shared inner dimension. -/
  m : Nat
  /-- Columns of `B` and of `C`. -/
  p : Nat
  /-- The declared term count. -/
  termCount : Nat
  /-- The ring-tagged terms. -/
  payload : RawPayload
  deriving Repr

/-- Exact primality by trial division, matching §6.6.

Probabilistic tests are forbidden in certificate acceptance, so this is a total
bounded loop rather than a witness check. -/
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    let rec go (d : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => true
      | fuel + 1 => if d * d > n then true else if n % d == 0 then false else go (d + 1) fuel
    go 2 n

/-- Decode a canonical `Fp` decomposition certificate (§6.1, §6.6).

The key sequence is expected positionally in canonical order, so a permuted or
duplicated key fails at the first mismatched byte. -/
def decodeCertificate (limits : Limits) (bytes : ByteArray) :
    Except DecodeError RawCertificate := do
  if bytes.size > limits.maxBytes then .error .resourceLimit else
  let c : Cursor := { bytes := bytes, pos := 0, rationals := 0 }
  let (_, c) ← expectString "{\"claim\":{\"m\":" c
  let (m, c) ← readNat limits c
  let (_, c) ← expectString ",\"n\":" c
  let (n, c) ← readNat limits c
  let (_, c) ← expectString ",\"p\":" c
  let (p, c) ← readNat limits c
  let (_, c) ← expectString ",\"term_count\":" c
  let (termCount, c) ← readNat limits c
  let (_, c) ← expectString "},\"kind\":" c
  let (_, c) ← readExpectedString "decomposition" .schemaMismatch c
  -- §0.2 bounds every dimension, checked before any instance-sized allocation.
  if n = 0 || m = 0 || p = 0 || n > 12 || m > 12 || p > 12 then
    .error .unsupportedInstance
  else
  -- §6.3 sorts keys, so `modulus` precedes `ring` and only `Fp` carries it. The
  -- branch is on the *bytes*, which is what keeps a permuted payload from being
  -- silently accepted.
  let (_, c) ← expectString ",\"payload\":{" c
  let (payload, c) ←
    if (expectString "\"modulus\":" c).isOk then do
      let (_, c) ← expectString "\"modulus\":" c
      let (modulus, c) ← readNat limits c
      if !isPrime modulus then .error .compositeModulus else
      let (_, c) ← expectString ",\"ring\":" c
      let (_, c) ← readExpectedString "Fp" .unsupportedInstance c
      let (_, c) ← expectString ",\"terms\":" c
      let (terms, c) ←
        readTermsOf (readFieldElement limits modulus) (n * m) (m * p) (p * n) termCount c
      .ok (RawPayload.fp modulus terms, c)
    else do
      let (_, c) ← expectString "\"ring\":" c
      let (ringBytes, c) ← readStringBytes c
      let (_, c) ← expectString ",\"terms\":" c
      if ringBytes == "Z".toUTF8.toList then do
        let (terms, c) ←
          readTermsOf (readIntCoefficient limits) (n * m) (m * p) (p * n) termCount c
        .ok (RawPayload.z terms, c)
      else if ringBytes == "Q".toUTF8.toList then do
        let (terms, c) ←
          readTermsOf (readRationalObject limits) (n * m) (m * p) (p * n) termCount c
        .ok (RawPayload.q terms, c)
      else if ringBytes == "Qi".toUTF8.toList then do
        let (terms, c) ←
          readTermsOf (readGaussianObject limits) (n * m) (m * p) (p * n) termCount c
        .ok (RawPayload.qi terms, c)
      else .error .unsupportedInstance
  let (_, c) ← expectString "},\"schema\":" c
  let (_, c) ← readExpectedString "matrix-math-certificate/1" .schemaMismatch c
  let (_, c) ← expectString ",\"source_hashes\":{\"S1\":" c
  let (_, c) ← readExpectedString
    "da7be6aadb5cb0611af8f033fb2984ab5a16f136230330371127d5877951c093"
    .sourceHashMismatch c
  let (_, c) ← expectString ",\"S2\":" c
  let (_, c) ← readExpectedString
    "42aea3994792b42358ca5d9d4c95cb3eac15f28254850a11d082b995aed8d401"
    .sourceHashMismatch c
  let (_, c) ← expectString "},\"spec_version\":" c
  let (_, c) ← readExpectedString "2.1.0" .specVersionMismatch c
  let (_, c) ← expectString "}" c
  -- §6.3: trailing bytes after the document are a rejection, not slack.
  if !c.atEnd then .error (.noncanonicalJson c.pos) else
  if payload.length != termCount then .error .countMismatch else
  .ok { n := n, m := m, p := p, termCount := termCount, payload := payload }

/-- Assemble a decomposition from decoded terms already in the target ring. -/
def decompositionOf {R : Type} (n m p : Nat) (terms : List (ArrayTerm R)) :
    Decomposition R :=
  { n := n, m := m, p := p, terms := terms }

/-- Reinterpret `Fp` coefficients in `ZMod p`. -/
def decompositionFp (n m p modulus : Nat) (terms : List (ArrayTerm Nat)) :
    Decomposition (ZMod modulus) :=
  decompositionOf n m p (terms.map fun t =>
    { u := t.u.map (fun value => (value : ZMod modulus))
      v := t.v.map (fun value => (value : ZMod modulus))
      w := t.w.map (fun value => (value : ZMod modulus)) })

/-- The full validator, applied in whichever ring the certificate declares. -/
def RawCertificate.validates (r : RawCertificate) : Bool :=
  match r.payload with
  | .fp modulus terms => validate (decompositionFp r.n r.m r.p modulus terms)
  | .z terms => validate (decompositionOf (R := Int) r.n r.m r.p terms)
  | .q terms => validate (decompositionOf (R := Rat) r.n r.m r.p terms)
  | .qi terms =>
    validate (decompositionOf (R := GaussianRat) r.n r.m r.p terms)

/-- The tensor identity an accepted certificate asserts, in its own ring (B1). -/
def RawCertificate.Meaning (r : RawCertificate) : Prop :=
  match r.payload with
  | .fp modulus terms =>
    Reconstructs r.n r.m r.p (decompositionFp r.n r.m r.p modulus terms).semantics
  | .z terms =>
    Reconstructs r.n r.m r.p (decompositionOf (R := Int) r.n r.m r.p terms).semantics
  | .q terms =>
    Reconstructs r.n r.m r.p (decompositionOf (R := Rat) r.n r.m r.p terms).semantics
  | .qi terms =>
    Reconstructs r.n r.m r.p
      (decompositionOf (R := GaussianRat) r.n r.m r.p terms).semantics

/-- The rank bound an accepted certificate asserts, in its own ring (§10.4). -/
def RawCertificate.RankClaim (r : RawCertificate) : Prop :=
  match r.payload with
  | .fp modulus terms => TensorRankLE (ZMod modulus) r.n r.m r.p terms.length
  | .z terms => TensorRankLE Int r.n r.m r.p terms.length
  | .q terms => TensorRankLE Rat r.n r.m r.p terms.length
  | .qi terms => TensorRankLE GaussianRat r.n r.m r.p terms.length

/-- **The authoritative byte-level check** (§3.1).

`checkBytes bytes = true` exactly when the bytes decode as a canonical `Fp`
decomposition certificate whose terms reconstruct the target tensor. -/
def checkBytes (limits : Limits) (bytes : ByteArray) : Bool :=
  match decodeCertificate limits bytes with
  | .error _ => false
  | .ok raw =>
    -- `ZMod n` is a commutative ring with decidable equality for every `n`, so
    -- no `NeZero` side condition is needed here; `isPrime` already rejected
    -- a modulus below two during decoding (§6.6).
    raw.validates

end MatrixMath.Schema

/-! ## Soundness of the byte-level check

§3.1's authoritative shape is

```text
theorem checkBytes_sound : checkBytes bytes = true → Meaning bytes
```

and §17.5 rejects a soundness theorem stated only for prevalidated data when the
publication command accepts bytes. These are that theorem: the hypothesis is
about **bytes**, and the conclusion is about the tensor.
-/

namespace MatrixMath.Schema

open MatrixMath.Certificate MatrixMath.Spec

/-- **Byte-level soundness.** If the check accepts a byte sequence, that sequence
decodes to a certificate whose terms reconstruct the matrix multiplication
tensor (B1). -/
theorem validates_sound {r : RawCertificate} (h : r.validates = true) : r.Meaning := by
  unfold RawCertificate.validates RawCertificate.Meaning at *
  cases hp : r.payload <;> rw [hp] at h <;> exact validate_sound h

theorem checkBytes_sound {limits : Limits} {bytes : ByteArray}
    (h : checkBytes limits bytes = true) :
    ∃ raw : RawCertificate,
      decodeCertificate limits bytes = .ok raw ∧ raw.Meaning := by
  -- The case split is on a universally quantified `decoded`, so it cannot
  -- rewrite the goal, which must keep naming `decodeCertificate limits bytes`.
  unfold checkBytes at h
  have key : ∀ decoded : Except DecodeError RawCertificate,
      decodeCertificate limits bytes = decoded →
      (match decoded with
        | .error _ => false
        | .ok raw => raw.validates) = true →
      ∃ raw : RawCertificate,
        decodeCertificate limits bytes = .ok raw ∧ raw.Meaning := by
    intro decoded hdec hcheck
    cases decoded with
    | error e => exact absurd hcheck (by simp)
    | ok raw => exact ⟨raw, hdec, validates_sound hcheck⟩
  exact key _ rfl h

/-- **The published Track B claim, from bytes.**

Acceptance of a byte sequence bounds the tensor rank above by the number of terms
the certificate actually contains — and by nothing smaller (§10.4).

The bound is stated in terms of the *decoded* term list rather than the declared
`term_count` field, so the theorem does not depend on that field being honest.
The decoder rejects a mismatch between the two anyway (§6.6), so for any accepted
certificate they agree. -/
theorem checkBytes_rank_le {limits : Limits} {bytes : ByteArray}
    (h : checkBytes limits bytes = true) :
    ∃ raw : RawCertificate,
      decodeCertificate limits bytes = .ok raw ∧ raw.RankClaim := by
  obtain ⟨raw, hdec, hrec⟩ := checkBytes_sound h
  refine ⟨raw, hdec, ?_⟩
  unfold RawCertificate.RankClaim
  unfold RawCertificate.Meaning at hrec
  cases hp : raw.payload <;> rw [hp] at hrec <;>
    exact ⟨_, by simp [Decomposition.semantics, decompositionOf, decompositionFp], hrec⟩

end MatrixMath.Schema
