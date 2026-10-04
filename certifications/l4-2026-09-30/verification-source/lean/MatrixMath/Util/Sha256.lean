/-!
# SHA-256 in Lean

Normative source: `docs/specs/0001_spec.md` §6.3 and §6.8.

The certificate identity is `sha256(canonical_uncompressed_bytes)` (§6.3), and
§6.8 requires the same digest to be produced by Lean-side tooling, by Rust, and
by the system SHA-256 utility. This module is the Lean side of that three-way
agreement, and it also supplies the statement digests the §4.6 assurance audit
emits.

This is a plain transcription of FIPS 180-4 using `UInt32`, whose arithmetic is
already modulo `2^32`.
-/

namespace MatrixMath.Util

/-- The FIPS 180-4 round constants. -/
private def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The FIPS 180-4 initial hash value. -/
private def initialState : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
private def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
private def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
private def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

private def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
private def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def beWord (b : ByteArray) (offset : Nat) : UInt32 :=
  (b.get! offset).toUInt32 <<< 24 |||
  (b.get! (offset + 1)).toUInt32 <<< 16 |||
  (b.get! (offset + 2)).toUInt32 <<< 8 |||
  (b.get! (offset + 3)).toUInt32

/-- Expand one 64-byte block into the 64-word message schedule. -/
private def schedule (block : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 64
  for i in [0:16] do
    w := w.push (beWord block (offset + i * 4))
  for i in [16:64] do
    let s0 := smallSigma0 (w[i - 15]!)
    let s1 := smallSigma1 (w[i - 2]!)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  return w

/-- Compress one block into the running state. -/
private def compress (state : Array UInt32) (block : ByteArray) (offset : Nat) :
    Array UInt32 := Id.run do
  let w := schedule block offset
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let t1 := h + bigSigma1 e + ch e f g + k[i]! + w[i]!
    let t2 := bigSigma0 a + maj a b c
    h := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
           state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- Append the FIPS 180-4 padding to a message. -/
private def pad (message : ByteArray) : ByteArray := Id.run do
  let bitLength : UInt64 := (UInt64.ofNat message.size) * 8
  let mut out := message.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
    out := out.push ((bitLength >>> (UInt64.ofNat shift)).toUInt8)
  return out

/-- The SHA-256 digest of a byte array, as 32 bytes. -/
def sha256 (message : ByteArray) : ByteArray := Id.run do
  let padded := pad message
  let mut state := initialState
  let mut offset := 0
  while offset < padded.size do
    state := compress state padded offset
    offset := offset + 64
  let mut out := ByteArray.emptyWithCapacity 32
  for word in state do
    out := out.push ((word >>> 24).toUInt8)
    out := out.push ((word >>> 16).toUInt8)
    out := out.push ((word >>> 8).toUInt8)
    out := out.push (word.toUInt8)
  return out

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (n.toNat + '0'.toNat)
  else Char.ofNat (n.toNat - 10 + 'a'.toNat)

/-- Lowercase hexadecimal encoding (§8.3). -/
def toHex (bytes : ByteArray) : String := Id.run do
  let mut out := ""
  for byte in bytes do
    out := out.push (hexDigit (byte >>> 4))
    out := out.push (hexDigit (byte &&& 0x0f))
  return out

/-- The lowercase hexadecimal SHA-256 of a string's UTF-8 encoding. -/
def sha256Hex (text : String) : String :=
  toHex (sha256 text.toUTF8)

end MatrixMath.Util
