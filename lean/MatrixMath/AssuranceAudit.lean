import Lean
import MatrixMath.Theorems
import MatrixMath.Util.Sha256

/-!
# Compiled theorem assurance audit

Normative source: `docs/specs/0001_spec.md` §4.6, §17.5.

This executable queries Lean's **compiled environment**, not the source text. It
fails if a declaration is missing, renamed, has a changed type, or depends on
`sorryAx`. It emits canonical UTF-8 JSON sorted by fully qualified declaration
name, using the pinned pretty-printer with explicit universes, explicit
arguments, and fully qualified names; the statement digest is therefore
version-specific and changes intentionally with a Lean upgrade (§4.6).

`scripts/check-assurance.py` compares this output against the reviewed
`lean/assurance-manifest.toml` and rejects drift.
-/

open Lean

namespace MatrixMath.Audit

/-- Escape a string as a canonical JSON string literal (§6.3). -/
def jsonString (value : String) : String := Id.run do
  let mut out := "\""
  for ch in value.toList do
    let code := ch.toNat
    if ch == '"' then out := out ++ "\\\""
    else if ch == '\\' then out := out ++ "\\\\"
    else if code == 8 then out := out ++ "\\b"
    else if code == 9 then out := out ++ "\\t"
    else if code == 10 then out := out ++ "\\n"
    else if code == 12 then out := out ++ "\\f"
    else if code == 13 then out := out ++ "\\r"
    else if code < 32 then
      let hi := MatrixMath.Util.toHex (ByteArray.mk #[UInt8.ofNat code])
      out := out ++ "\\u00" ++ hi
    else out := out.push ch
  return out ++ "\""

/-- Render a list of strings as a canonical JSON array. -/
def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," (values.map jsonString) ++ "]"

/-- The declaration kind reported for a constant (§4.6). -/
def declKind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The audited facts for one claim. -/
structure Row where
  id : String
  allowlist : List String
  declName : String
  kind : String
  statement : String
  statementSha256 : String
  axioms : List String
  evidence : List String
  residual : List String
  status : String

/-- Render one row as canonical JSON with lexicographically sorted keys. -/
def Row.toJson (r : Row) : String :=
  "{\"axiom_allowlist\":" ++ jsonArray r.allowlist ++
  ",\"axioms\":" ++ jsonArray r.axioms ++
  ",\"declaration\":" ++ jsonString r.declName ++
  ",\"evidence\":" ++ jsonArray r.evidence ++
  ",\"id\":" ++ jsonString r.id ++
  ",\"kind\":" ++ jsonString r.kind ++
  ",\"residual_assumptions\":" ++ jsonArray r.residual ++
  ",\"statement\":" ++ jsonString r.statement ++
  ",\"statement_sha256\":" ++ jsonString r.statementSha256 ++
  ",\"status\":" ++ jsonString r.status ++ "}"

/-- Audit one inventory entry against the compiled environment. -/
def auditEntry (entry : MatrixMath.ClaimEntry) : MetaM Row := do
  let env ← getEnv
  let some info := env.find? entry.declName
    | throwError "assurance: declaration {entry.declName} is missing from the compiled environment"
  let statement ← withOptions (fun opts =>
      opts.setBool `pp.universes true
        |>.setBool `pp.explicit true
        |>.setBool `pp.fullNames true) do
    let formatted ← Lean.PrettyPrinter.ppExpr info.type
    pure formatted.pretty
  let axiomSet ← collectAxioms entry.declName
  let axiomNames := (axiomSet.toList.map (·.toString)).mergeSort (· ≤ ·)
  if axiomNames.contains "sorryAx" then
    throwError "assurance: {entry.declName} depends on sorryAx"
  return {
    id := entry.id
    allowlist := entry.allowlist
    declName := entry.declName.toString
    kind := declKind info
    statement := statement
    statementSha256 := MatrixMath.Util.sha256Hex statement
    axioms := axiomNames
    evidence := entry.evidence
    residual := entry.residual
    status := entry.status }

end MatrixMath.Audit

open MatrixMath.Audit in
/-- Emit the canonical audit document for the whole public inventory. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `MatrixMath.Theorems }] {}
  let rows ← try
      Prod.fst <$> (Core.CoreM.toIO
        (Meta.MetaM.run' (MatrixMath.publicTheoremInventory.mapM auditEntry))
        { fileName := "<assurance>", fileMap := default }
        { env := env })
    catch e =>
      IO.eprintln s!"assurance audit failed: {e}"
      return 1
  let sorted := rows.mergeSort (fun a b => a.declName ≤ b.declName)
  let body := String.intercalate "," (sorted.map Row.toJson)
  IO.println <|
    "{\"claims\":[" ++ body ++
    "],\"schema\":\"matrix-math-assurance-audit/1\",\"spec_version\":" ++
    jsonString "2.1.0" ++ "}"
  return 0
