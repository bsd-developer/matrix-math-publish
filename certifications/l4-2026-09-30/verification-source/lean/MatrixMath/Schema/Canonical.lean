/-!
# Canonical byte grammar

Normative source: `docs/specs/0001_spec.md` §6.2, §6.3, §6.4.

Canonical bytes are UTF-8 JSON conforming to RFC 8785 plus the stricter rules of
§6.2 and §6.3. This module states the grammar predicates and the resource
limits; `MatrixMath.Schema.Decode` is the total decoder that enforces them.

The rules that matter for identity, all of which make a value have exactly one
spelling:

* no whitespace anywhere between tokens;
* object keys strictly ascending, with no duplicates;
* canonical non-negative integers only — no leading zero, sign, fraction, or
  exponent — because every mathematical magnitude travels as a decimal string
  instead (§6.2); and
* integer strings with no leading `+`, no leading zeros except exactly `"0"`, and
  no `-0`.

Deliberately **not** included: a normalizing reader. §6.3 requires a byte
sequence that is valid JSON but not canonical to be *rejected*, because
normalizing on input would give one value two digests.
-/

namespace MatrixMath.Schema

/-- The §6.4 resource envelope. Limits are checked incrementally as bytes are
consumed, so a hostile input is rejected before it can allocate. -/
structure Limits where
  /-- Maximum canonical uncompressed bytes (§6.4: 8 GiB by default). -/
  maxBytes : Nat
  /-- Maximum number of rational values (§6.4: 50,000,000 by default). -/
  maxRationals : Nat
  /-- Maximum nesting depth (§6.4: 32 by default). -/
  maxDepth : Nat
  /-- Maximum decimal digits per numerator or denominator (§6.2: 4,096). -/
  maxDigits : Nat
  deriving Repr, DecidableEq

/-- The §6.4 defaults. -/
def Limits.default : Limits :=
  { maxBytes := 8 * 1024 * 1024 * 1024
    maxRationals := 50000000
    maxDepth := 32
    maxDigits := 4096 }

/-- A tighter envelope for tests and small fixtures. -/
def Limits.small : Limits :=
  { maxBytes := 64 * 1024 * 1024
    maxRationals := 1000000
    maxDepth := 32
    maxDigits := 4096 }

/-- The stable rejection codes this decoder can produce (§5.4).

These are the same strings the Rust checker uses, so a differential test can
compare verdict *and* code. -/
inductive DecodeError where
  /-- Bytes were not well-formed JSON. -/
  | invalidJson (offset : Nat)
  /-- Valid JSON but not canonical form (§6.3). -/
  | noncanonicalJson (offset : Nat)
  /-- A numeric string violated the §6.2 grammar. -/
  | badRationalGrammar (offset : Nat)
  /-- A required field was absent. -/
  | missingField (name : String)
  /-- An unknown field was present; §6.1 rejects rather than ignores. -/
  | unknownField (name : String)
  /-- The schema discriminator did not match. -/
  | schemaMismatch
  /-- The specification version did not match. -/
  | specVersionMismatch
  /-- A recorded source hash disagreed with the locked value (§0.1). -/
  | sourceHashMismatch
  /-- A declared count disagreed with the decoded data. -/
  | countMismatch
  /-- A value fell outside the §0.2 supported domain. -/
  | unsupportedInstance
  /-- A declared field modulus was not prime (§6.6). -/
  | compositeModulus
  /-- A resource limit was exceeded (§6.4). -/
  | resourceLimit
  /-- A term contained an all-zero factor (§6.6). -/
  | zeroFactor
  /-- A factor had the wrong length for its tensor mode. -/
  | wrongVectorLength
  /-- Terms were not in canonical sorted order (§10.4). -/
  | noncanonicalTermOrder
  /-- A claimed `Ω` was negative, which §7.2 validates before the monotonic
  shortcut is used. -/
  | negativeOmega
  deriving Repr, DecidableEq

/-- The stable wire string for a rejection code (§5.4). -/
def DecodeError.code : DecodeError → String
  | .invalidJson _ => "invalid_json"
  | .noncanonicalJson _ => "noncanonical_json"
  | .badRationalGrammar _ => "bad_rational_grammar"
  | .missingField _ => "missing_field"
  | .unknownField _ => "unknown_field"
  | .schemaMismatch => "schema_mismatch"
  | .specVersionMismatch => "spec_version_mismatch"
  | .sourceHashMismatch => "source_hash_mismatch"
  | .countMismatch => "count_mismatch"
  | .unsupportedInstance => "unsupported_instance"
  | .compositeModulus => "composite_modulus"
  | .resourceLimit => "resource_limit"
  | .zeroFactor => "zero_factor"
  | .wrongVectorLength => "wrong_vector_length"
  | .noncanonicalTermOrder => "noncanonical_term_order"
  | .negativeOmega => "negative_omega"

/-- Whether a byte is an ASCII decimal digit. -/
def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- The numeric value of a decimal digit byte. -/
def digitValue (b : UInt8) : Nat := (b - 0x30).toNat

/-- Whether a digit string is canonical: nonempty, all digits, and no leading
zero unless it is exactly `"0"` (§6.2). -/
def canonicalDigits (s : List UInt8) : Bool :=
  match s with
  | [] => false
  | [b] => isDigit b
  | b :: rest => isDigit b && b != 0x30 && rest.all isDigit

end MatrixMath.Schema
