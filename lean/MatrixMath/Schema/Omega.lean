import MatrixMath.Schema.Decode
import MatrixMath.Certificate.OmegaCheck
import MatrixMath.Util.Sha256

/-!
# Byte-level decoding of the omega certificate

Normative source: `docs/specs/0001_spec.md` §3.1, §6.2, §6.5.

§3.1 puts *decode* inside the Lean box, and `MatrixMath.Schema.Decode` already
does that for decomposition certificates. This module does it for the §6.5 omega
schema, so a Track A theorem can be stated about **bytes** rather than about
typed literals bound to bytes by an external round trip.

The design choices are the ones `Decode` makes and for the same reasons: keys are
expected positionally in canonical order, string escapes are rejected, and the
§6.2 numeric grammar is enforced rather than normalized.

## What the decoder refuses

An `ℓ*` outside §0.2's range is rejected at the claim, not at the check: a
rejection carries a reason and a bare `false` does not.

Every structural fact the schema fixes — six regions, the shape set at each
level, the `Split` set below a positive node, the block count, the `β` width
implied by each shape — is derived here from `ℓ*` and never taken from the
certificate. §6.5 is explicit about the block count in particular.

The one exception is a `λ_W` vector's width, which depends on how many distinct
values its coordinate takes on the block's domain. The decoder reads it as
written and `blockOk` checks it against the domain it is applied to, where the
check is decided and proved rather than assumed.
-/

namespace MatrixMath.Schema

open MatrixMath MatrixMath.Certificate MatrixMath.Spec

/-- Read a JSON array of exactly `len` canonical rationals (§6.2). -/
def readRatArray (limits : Limits) (len : Nat) (c : Cursor) :
    Except DecodeError ((List ℚ) × Cursor) :=
  let rec go (remaining : Nat) (acc : List ℚ) (c : Cursor) :
      Except DecodeError ((List ℚ) × Cursor) :=
    match remaining with
    | 0 => do
        let (_, c) ← expectByte 0x5D c
        .ok (acc.reverse, c)
    | remaining + 1 => do
        let (value, c) ← readRationalObject limits c
        if remaining = 0 then go 0 (value :: acc) c
        else do
          let (_, c) ← expectByte 0x2C c
          go remaining (value :: acc) c
  do
    let (_, c) ← expectByte 0x5B c
    if len = 0 then .error .wrongVectorLength else go len [] c

/-- Read a JSON array of canonical rationals of **unstated** length (§6.2).

A `λ_W` vector's width is the number of distinct values its coordinate takes on
the block's domain, which depends on where in the tree the block sits. Rather
than recompute the whole block-to-domain assignment here, the decoder reads the
array as written and `blockOk` checks the width against the domain it is applied
to — where the check is decided and proved, rather than assumed. -/
def readRatArrayAny (limits : Limits) (c : Cursor) :
    Except DecodeError ((List ℚ) × Cursor) :=
  let rec go (fuel : Nat) (acc : List ℚ) (c : Cursor) :
      Except DecodeError ((List ℚ) × Cursor) :=
    match fuel with
    | 0 => .error .resourceLimit
    | fuel + 1 => do
        let (value, c) ← readRationalObject limits c
        match c.peek with
        | some 0x2C => do
            let (_, c) ← expectByte 0x2C c
            go fuel (value :: acc) c
        | some 0x5D => do
            let (_, c) ← expectByte 0x5D c
            .ok ((value :: acc).reverse, c)
        | _ => .error (.invalidJson c.pos)
  do
    let (_, c) ← expectByte 0x5B c
    go (c.bytes.size + 1) [] c

/-- Read one §7.4 maximum-entropy block. -/
def readBlock (limits : Limits) (c : Cursor) : Except DecodeError (Block × Cursor) := do
  let (_, c) ← expectString "{\"epsilon\":" c
  let (epsilon, c) ← readRationalObject limits c
  let (_, c) ← expectString ",\"lambda0\":" c
  let (lambda0, c) ← readRationalObject limits c
  let (_, c) ← expectString ",\"lambda_x\":" c
  let (lambdaX, c) ← readRatArrayAny limits c
  let (_, c) ← expectString ",\"lambda_y\":" c
  let (lambdaY, c) ← readRatArrayAny limits c
  let (_, c) ← expectString ",\"lambda_z\":" c
  let (lambdaZ, c) ← readRatArrayAny limits c
  let (_, c) ← expectString ",\"y\":" c
  let (y, c) ← readRatArrayAny limits c
  let (_, c) ← expectByte 0x7D c
  .ok ({ y := y, lambda0 := lambda0, lambdaX := lambdaX, lambdaY := lambdaY,
         lambdaZ := lambdaZ, epsilon := epsilon }, c)

/-- Read the block array. The count comes from the instance (§6.5). -/
def readBlocks (limits : Limits) (count : Nat) (c : Cursor) :
    Except DecodeError ((List Block) × Cursor) :=
  let rec go (remaining : Nat) (acc : List Block) (c : Cursor) :
      Except DecodeError ((List Block) × Cursor) :=
    match remaining with
    | 0 => do
        let (_, c) ← expectByte 0x5D c
        .ok (acc.reverse, c)
    | remaining + 1 => do
        let (block, c) ← readBlock limits c
        if remaining = 0 then go 0 (block :: acc) c
        else do
          let (_, c) ← expectByte 0x2C c
          go remaining (block :: acc) c
  do
    let (_, c) ← expectByte 0x5B c
    if count = 0 then .error .countMismatch else go count [] c

/-- Read a JSON array of exactly `rows` rational arrays of length `width`. -/
def readRatMatrix (limits : Limits) (rows width : Nat) (c : Cursor) :
    Except DecodeError ((List (List ℚ)) × Cursor) :=
  let rec go (remaining : Nat) (acc : List (List ℚ)) (c : Cursor) :
      Except DecodeError ((List (List ℚ)) × Cursor) :=
    match remaining with
    | 0 => do
        let (_, c) ← expectByte 0x5D c
        .ok (acc.reverse, c)
    | remaining + 1 => do
        let (row, c) ← readRatArray limits width c
        if remaining = 0 then go 0 (row :: acc) c
        else do
          let (_, c) ← expectByte 0x2C c
          go remaining (row :: acc) c
  do
    let (_, c) ← expectByte 0x5B c
    if rows = 0 then .error .countMismatch else go rows [] c

/-- Read the root node: `A_G` and one `α_G^(r)` per region (A.2). -/
def readRootNode (limits : Limits) (levels : ℕ) (c : Cursor) :
    Except DecodeError ((List ℚ × List (List ℚ)) × Cursor) := do
  let (_, c) ← expectString "{\"alpha\":" c
  let (alpha, c) ← readRatMatrix limits 6 (shapeList levels).length c
  let (_, c) ← expectString ",\"region_weights\":" c
  let (regionWeights, c) ← readRatArray limits 6 c
  let (_, c) ← expectByte 0x7D c
  .ok ((regionWeights, alpha), c)

/-- Read one leaf, whose payload key is fixed by its shape and level (A.2).

A positive level-2 shape carries `μ_T`; every other leaf is a zero shape and
carries the free `β_(T,W1)` laid onto `C_(ℓ, s_(T,W1))`. Reading the key the
*position* demands, rather than dispatching on whichever key is present, is what
makes a payload that disagrees with its position a rejection instead of a
reinterpretation. -/
def readLeafNode (limits : Limits) (ℓ region : ℕ) (shape : AShape) (alpha : ℚ)
    (c : Cursor) : Except DecodeError (ANode × Cursor) :=
  if AShape.positive shape then do
    if ℓ != 2 then .error .unsupportedInstance else
    let (_, c) ← expectString "{\"mu\":" c
    let (mu, c) ← readRationalObject limits c
    let (_, c) ← expectByte 0x7D c
    .ok (.posTwo region shape alpha mu, c)
  else do
    let vectors := supportList ℓ (AShape.coord shape (AShape.firstPos shape))
    let (_, c) ← expectString "{\"beta\":" c
    let (beta, c) ← readRatArray limits vectors.length c
    let (_, c) ← expectByte 0x7D c
    .ok (.zeroLeaf region shape alpha (vectors.zip beta), c)

/-- The children of a node, as `(region, shape, α)` in canonical preorder (§5.2). -/
def childSlots (shapes : List AShape) (alpha : List (List ℚ)) :
    List (ℕ × AShape × ℚ) :=
  (List.range 6).flatMap fun region =>
    (List.range shapes.length).map fun index =>
      (region, shapes.getD index (0, 0, 0), ((alpha.getD region []).getD index 0))

mutual

/-- Read the subtree rooted at one node, given the position the tree implies.

The traversal is the one §5.2 fixes: the node's own payload, then each region in
turn, and within a region each child shape in `Split` order. Nothing about the
shape of the tree comes from the certificate. -/
def readSubtree (limits : Limits) : ℕ → ℕ → AShape → ℚ → Cursor →
    Except DecodeError (ANode × Cursor)
  | 0, _, _, _, _ => .error .unsupportedInstance
  | 1, _, _, _, _ => .error .unsupportedInstance
  | 2, region, shape, alpha, c => readLeafNode limits 2 region shape alpha c
  | ℓ + 3, region, shape, alpha, c =>
    if !AShape.positive shape then readLeafNode limits (ℓ + 3) region shape alpha c
    else do
      let splits := splitList (ℓ + 3) shape
      let (_, c) ← expectString "{\"alpha\":" c
      let (rows, c) ← readRatMatrix limits 6 splits.length c
      let (_, c) ← expectString ",\"region_weights\":" c
      let (weights, c) ← readRatArray limits 6 c
      let (_, c) ← expectByte 0x7D c
      let (kids, c) ← readChildren limits (ℓ + 2) (childSlots splits rows) [] c
      .ok (.posBranch region shape alpha weights kids, c)
  termination_by ℓ _ _ _ _ => (ℓ, 0)

/-- Read each child subtree in turn, separated by the array commas. -/
def readChildren (limits : Limits) : ℕ → List (ℕ × AShape × ℚ) → List ANode →
    Cursor → Except DecodeError ((List ANode) × Cursor)
  | _, [], acc, c => .ok (acc.reverse, c)
  | ℓ, slot :: rest, acc, c => do
      let (_, c) ← expectByte 0x2C c
      let (node, c) ← readSubtree limits ℓ slot.1 slot.2.1 slot.2.2 c
      readChildren limits ℓ rest (node :: acc) c
  termination_by ℓ slots _ _ => (ℓ, slots.length + 1)

end

/-- Decode a canonical omega certificate (§6.1, §6.5). -/
def decodeOmega (limits : Limits) (bytes : ByteArray) :
    Except DecodeError TrackACert := do
  if bytes.size > limits.maxBytes then .error .resourceLimit else
  let c : Cursor := { bytes := bytes, pos := 0, rationals := 0 }
  let (_, c) ← expectString "{\"claim\":{\"l_star\":" c
  let (levels, c) ← readNat limits c
  -- §0.2 fixes the supported range; anything else is rejected with a reason.
  if levels < 2 || levels > 4 then .error .unsupportedInstance else
  let (_, c) ← expectString ",\"omega\":" c
  let (omega, c) ← readRationalObject limits c
  -- §7.2 and A.10: the version 1 certificate restriction is `Ω ≥ 0`, checked
  -- here so a negative value never reaches the monotonic shortcut.
  if omega < 0 then .error .negativeOmega else
  let (_, c) ← expectString ",\"q\":" c
  let (q, c) ← readNat limits c
  if q = 0 then .error .unsupportedInstance else
  let (_, c) ← expectString "},\"kind\":" c
  let (_, c) ← readExpectedString "omega" .schemaMismatch c
  -- `0007_spec.md` §3.1 adds `encoding` ahead of `log_precision_bits` in sorted
  -- key order. It has no default, so a payload without it does not parse.
  let (_, c) ← expectString ",\"payload\":{\"encoding\":\"general\",\"log_precision_bits\":" c
  let (precision, c) ← readNat limits c
  -- §6.5 fixes the inclusive range 32..=4096.
  if precision < 32 || precision > 4096 then .error .unsupportedInstance else
  let (_, c) ← expectString ",\"max_entropy_blocks\":" c
  -- §6.5: the block count is derived from the instance, never trusted.
  let (blocks, c) ← readBlocks limits (blockCount levels) c
  let (_, c) ← expectString ",\"nodes\":[" c
  let ((regionWeights, alpha), c) ← readRootNode limits levels c
  let (kids, c) ← readChildren limits levels (childSlots (shapeList levels) alpha) [] c
  let (_, c) ← expectByte 0x5D c
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
  .ok { inst := { q := q, levels := levels, A := regionWeights, kids := kids }
        blocks := blocks
        omega := omega
        precision := precision }

/-- **The authoritative byte-level Track A check** (§3.1, §7.2). -/
def checkOmegaBytes (limits : Limits) (bytes : ByteArray) : Bool :=
  match decodeOmega limits bytes with
  | .error _ => false
  | .ok cert => TrackACert.check cert

end MatrixMath.Schema

/-! ## Soundness of the byte-level Track A check

The hypothesis is about **bytes** and the conclusion is about `ω`. §17.5 rejects
a soundness theorem stated only for prevalidated data when the publication
command accepts bytes, and this is the Track A form of that theorem.
-/

namespace MatrixMath.Schema

open MatrixMath MatrixMath.Certificate

/-- **Byte-level Track A soundness.** Accepting a byte sequence establishes
feasibility of the cited A.10 problem for the certificate it decodes to. -/
theorem checkOmegaBytes_sound {limits : Limits} {bytes : ByteArray}
    (h : checkOmegaBytes limits bytes = true) :
    ∃ cert : TrackACert,
      decodeOmega limits bytes = .ok cert ∧
        CombinationLossFeasible cert.inst.q cert.inst.levels ((cert.omega : ℚ) : ℝ) := by
  unfold checkOmegaBytes at h
  have key : ∀ decoded : Except DecodeError TrackACert,
      decodeOmega limits bytes = decoded →
      (match decoded with
        | .error _ => false
        | .ok cert => TrackACert.check cert) = true →
      ∃ cert : TrackACert,
        decodeOmega limits bytes = .ok cert ∧
          CombinationLossFeasible cert.inst.q cert.inst.levels ((cert.omega : ℚ) : ℝ) := by
    intro decoded hdec hcheck
    cases decoded with
    | error e => exact absurd hcheck (by simp)
    | ok cert => exact ⟨cert, hdec, TrackACert.check_sound hcheck⟩
  exact key _ rfl h

/-- **The whole Track A acceptance test, as one Boolean** (§3.4, §3.5).

A generated module must establish two things about the published bytes: that the
checker accepts them, and that the `Ω` they carry is the one the theorem names.
Deciding them separately would need two `native_decide` calls and therefore two
distinct native axioms, which §3.4 forbids — it permits *one* certificate-specific
native-evaluation axiom. Conjoining them here keeps that to one. -/
def acceptsOmega (limits : Limits) (bytes : ByteArray) (claim : ℚ) : Bool :=
  checkOmegaBytes limits bytes &&
    (match decodeOmega limits bytes with
     | .ok cert => cert.omega == claim
     | .error _ => false)

/-- **The published Track A claim, from bytes.**

`AX1_combination_loss` is the one project axiom §3.2 permits, and it is the only
one this theorem adds over Lean's standard set. -/
theorem checkOmegaBytes_omega_le {limits : Limits} {bytes : ByteArray}
    (h : checkOmegaBytes limits bytes = true) :
    ∃ cert : TrackACert,
      decodeOmega limits bytes = .ok cert ∧
        omegaExponent ≤ ((cert.omega : ℚ) : ℝ) := by
  obtain ⟨cert, hdec, hfeas⟩ := checkOmegaBytes_sound h
  exact ⟨cert, hdec, AX1_combination_loss hfeas⟩

/-- **The theorem a generated Track A module states**: accepting the published
bytes bounds `ω` by the named rational.

The bound is a literal in the statement rather than a projection out of the
decoded certificate, so a reader sees the claim without having to evaluate the
decoder. -/
theorem omega_le_of_acceptsOmega {limits : Limits} {bytes : ByteArray} {claim : ℚ}
    (h : acceptsOmega limits bytes claim = true) :
    omegaExponent ≤ ((claim : ℚ) : ℝ) := by
  unfold acceptsOmega at h
  obtain ⟨hcheck, hvalue⟩ := Bool.and_eq_true _ _ |>.mp h
  obtain ⟨cert, hdec, hle⟩ := checkOmegaBytes_omega_le hcheck
  rw [hdec] at hvalue
  simp only [beq_iff_eq] at hvalue
  rwa [hvalue] at hle


/-- **The acceptance test with the artifact identity folded in** (§3.4, §6.3).

`acceptsOmega` establishes that *some* bytes are accepted and carry the named
`Ω`; this conjunction additionally establishes that those bytes **are** the
published artifact — their SHA-256 is the digest the theorem names — inside
the same single Boolean, and therefore under the same single
native-evaluation axiom §3.4 permits. Before this definition the binding
between the Lean byte literal and the published file was a generator-side
step outside the development; with it, a generated theorem is checkably
about exactly the object the published digest identifies. -/
def acceptsOmegaDigest (limits : Limits) (bytes : ByteArray) (claim : ℚ)
    (digest : ByteArray) : Bool :=
  acceptsOmega limits bytes claim &&
    (MatrixMath.Util.sha256 bytes).data == digest.data

/-- Digest-bound acceptance still bounds `ω`: the identity conjunct narrows
which bytes the theorem speaks about and contributes nothing else. -/
theorem omega_le_of_acceptsOmegaDigest {limits : Limits} {bytes : ByteArray}
    {claim : ℚ} {digest : ByteArray}
    (h : acceptsOmegaDigest limits bytes claim digest = true) :
    omegaExponent ≤ ((claim : ℚ) : ℝ) := by
  unfold acceptsOmegaDigest at h
  exact omega_le_of_acceptsOmega (Bool.and_eq_true _ _ |>.mp h).1

end MatrixMath.Schema
