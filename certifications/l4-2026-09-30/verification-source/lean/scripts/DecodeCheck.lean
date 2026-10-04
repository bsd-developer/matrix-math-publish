import MatrixMath.Schema.Omega

/-!
Lean-side byte-level corpus check (spec §3.1, §12.6).

Runs the **authoritative** Lean path — decode the published bytes, validate
domains, evaluate exactly, produce a verdict — over the curated corpus and
compares each verdict against the expectation recorded here. This is what makes
§3.1's "decode" step real rather than a claim: nothing is pre-parsed for Lean.

Run with `just lean-decode-check`.
-/

open MatrixMath.Schema

/-- One corpus entry: a path, whether it must be accepted, and, for a rejection,
the stable error code expected (`""` when the certificate decodes but fails the
tensor check). -/
structure Case where
  path : String
  accept : Bool
  code : String := ""

def cases : List Case :=
  [ { path := "tests/vectors/strassen-f2.json", accept := true }
  , { path := "tests/vectors/alphatensor-f2-2x2x2.json", accept := true }
  , { path := "tests/vectors/alphatensor-f2-3x3x3.json", accept := true }
  , { path := "tests/vectors/alphatensor-f2-4x4x4.json", accept := true }
  , { path := "schemas/fixtures/valid/ring-fp-2x2x2.json", accept := true }
  , { path := "schemas/fixtures/valid/ring-fp7-2x2x2.json", accept := true }
    -- Every version 1 ring, decoded from bytes by Lean itself (§6.6).
  , { path := "schemas/fixtures/valid/ring-z-2x2x2.json", accept := true }
  , { path := "schemas/fixtures/valid/ring-q-2x2x2.json", accept := true }
  , { path := "schemas/fixtures/valid/ring-qi-2x2x2.json", accept := true }
  , { path := "schemas/fixtures/valid/smallest-1x1x1-z.json", accept := true }
  , { path := "tests/vectors/strassen-z.json", accept := true }
  , { path := "tests/vectors/alphatensor-z-2x2x2.json", accept := true }
  , { path := "tests/vectors/naive-2x3x4-z.json", accept := true }
  , { path := "schemas/fixtures/invalid/reconstruction_mismatch.json", accept := false }
  , { path := "schemas/fixtures/invalid/removed_term.json", accept := false }
  , { path := "schemas/fixtures/invalid/duplicated_term.json", accept := false }
  , { path := "schemas/fixtures/invalid/transposed_output.json", accept := false }
  , { path := "schemas/fixtures/invalid/zero_factor.json", accept := false }
  , { path := "schemas/fixtures/invalid/wrong_field.json", accept := false }
    -- The §6.2 numeric grammar, one violation per fixture.
  , { path := "schemas/fixtures/invalid/bad_rational_grammar.json", accept := false
    , code := "bad_rational_grammar" }
  , { path := "schemas/fixtures/invalid/zero_denominator.json", accept := false
    , code := "bad_rational_grammar" }
  , { path := "schemas/fixtures/invalid/negative_zero_rational.json", accept := false
    , code := "bad_rational_grammar" }
  , { path := "schemas/fixtures/invalid/leading_zero_integer.json", accept := false
    , code := "bad_rational_grammar" }
  , { path := "schemas/fixtures/invalid/plus_signed_integer.json", accept := false
    , code := "bad_rational_grammar" }
  , { path := "schemas/fixtures/invalid/noncanonical_json.json", accept := false
    , code := "noncanonical_json" }
  , { path := "schemas/fixtures/invalid/noncanonical_json_whitespace.json", accept := false
    , code := "noncanonical_json" }
  , { path := "schemas/fixtures/invalid/composite_modulus.json", accept := false
    , code := "composite_modulus" }
  , { path := "schemas/fixtures/invalid/source_hash_mismatch.json", accept := false
    , code := "source_hash_mismatch" }
  , { path := "schemas/fixtures/invalid/spec_version_mismatch.json", accept := false
    , code := "spec_version_mismatch" }
  , { path := "schemas/fixtures/invalid/schema_mismatch.json", accept := false
    , code := "schema_mismatch" }
    -- Rejected, but with `noncanonical_json` rather than Rust's `count_mismatch`:
    -- the positional parser runs past the term array and hits `]` where a term
    -- was expected, so it detects the mismatch earlier and by a different route.
    -- Both implementations reject, which is what §12.6 compares.
  , { path := "schemas/fixtures/invalid/count_mismatch.json", accept := false }
  , { path := "schemas/fixtures/invalid/truncated.json", accept := false
    , code := "invalid_json" }
  , { path := "schemas/fixtures/invalid/unsupported_instance.json", accept := false } ]

/-- Omega certificates, decoded and decided by the Lean Track A checker (§6.5).

The same corpus shape as the decomposition cases above: a path, the expected
verdict, and for a rejection the stable code. -/
def omegaCases : List Case :=
  [ { path := "tests/vectors/omega-l2-hand.json", accept := true }
  , { path := "tests/vectors/omega-l2-optimized.json", accept := true }
  , { path := "schemas/fixtures/invalid/omega_feasibility_violated.json", accept := false }
  , { path := "schemas/fixtures/invalid/omega_negative.json", accept := false
    , code := "negative_omega" }
  , { path := "schemas/fixtures/invalid/omega_bad_precision.json", accept := false
    , code := "unsupported_instance" } ]

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let bytes ← IO.FS.readBinFile ("../" ++ c.path)
    match decodeCertificate Limits.small bytes with
    | .error e =>
        if c.accept then
          IO.eprintln s!"FAIL {c.path}: expected acceptance, decoder returned {e.code}"
          failures := failures + 1
        else if c.code != "" && e.code != c.code then
          IO.eprintln s!"FAIL {c.path}: expected {c.code}, got {e.code}"
          failures := failures + 1
        else
          IO.println s!"  rej   {e.code} — {c.path}"
    | .ok raw =>
        let verdict := checkBytes Limits.small bytes
        if verdict != c.accept then
          IO.eprintln s!"FAIL {c.path}: decoded but verdict {verdict}, expected {c.accept}"
          failures := failures + 1
        else if !c.accept && c.code != "" then
          IO.eprintln s!"FAIL {c.path}: expected decode error {c.code}, but it decoded"
          failures := failures + 1
        else
          let label := if verdict then "ok " else "rej"
          let ring :=
            match raw.payload with
            | .fp modulus _ => s!"F{modulus}"
            | .z _ => "Z"
            | .q _ => "Q"
            | .qi _ => "Qi"
          let shape := s!"T[{raw.n},{raw.m},{raw.p}]/{ring}"
          IO.println s!"  {label}   {shape} {raw.payload.length} terms — {c.path}"
  for c in omegaCases do
    let bytes ← IO.FS.readBinFile ("../" ++ c.path)
    match decodeOmega Limits.small bytes with
    | .error e =>
        if c.accept then
          IO.eprintln s!"FAIL {c.path}: expected acceptance, decoder returned {e.code}"
          failures := failures + 1
        else if c.code != "" && e.code != c.code then
          IO.eprintln s!"FAIL {c.path}: expected {c.code}, got {e.code}"
          failures := failures + 1
        else
          IO.println s!"  rej   {e.code} — {c.path}"
    | .ok cert =>
        let verdict := checkOmegaBytes Limits.small bytes
        if verdict != c.accept then
          IO.eprintln s!"FAIL {c.path}: decoded but verdict {verdict}, expected {c.accept}"
          failures := failures + 1
        else if !c.accept && c.code != "" then
          IO.eprintln s!"FAIL {c.path}: expected decode error {c.code}, but it decoded"
          failures := failures + 1
        else
          let label := if verdict then "ok " else "rej"
          IO.println s!"  {label}   omega q={cert.inst.q} l*={cert.inst.levels} — {c.path}"
  if failures = 0 then
    IO.println s!"lean-decode-check: {cases.length + omegaCases.length} cases, all verdicts as expected"
    return 0
  else
    IO.eprintln s!"lean-decode-check: {failures} failures"
    return 1
