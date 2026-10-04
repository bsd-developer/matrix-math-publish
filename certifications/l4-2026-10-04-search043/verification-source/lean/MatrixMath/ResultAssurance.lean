import Lean
import MatrixMath.Util.Sha256

/-!
# Certificate-local compiled assurance

Specification §4.6 and ADR 0014. The generated omega module calls `emit` only
after its complete closed check and result theorem have elaborated. This is
reporting code: it adds no theorem, axiom, arithmetic, or checker dependency.
The separate public inventory remains in `MatrixMath.AssuranceAudit`.
-/

open Lean

namespace MatrixMath.ResultAssurance

private def strings (xs : List String) : Json :=
  toJson xs

private def statementOf (type : Expr) : MetaM String :=
  withOptions (fun opts => opts.setBool `pp.universes true
      |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
    return (← Lean.PrettyPrinter.ppExpr type).pretty

private def row (name : Name) (evaluation : Name) (isResult : Bool) : MetaM (Json × Name) := do
  let env ← getEnv
  let some info := env.find? name
    | throwError "result assurance: missing declaration {name}"
  unless info matches .thmInfo _ do
    throwError "result assurance: {name} is not a theorem"
  let statement ← statementOf info.type
  let axiomNames := (← collectAxioms name).toList
  let axioms := (axiomNames.map (·.toString)).mergeSort (· ≤ ·)
  let nativePrefix := evaluation.toString ++ "._native.native_decide."
  let native := axioms.filter (nativePrefix.isPrefixOf ·)
  unless native.length == 1 do
    throwError "result assurance: {name} must contain exactly one evaluation-scoped native axiom"
  for axiomName in axioms do
    unless ["Classical.choice", "Quot.sound", "propext"].contains axiomName ||
        native.contains axiomName ||
        (isResult && axiomName == "MatrixMath.AX1_combination_loss") do
      throwError "result assurance: unexpected axiom {axiomName} in {name}"
  unless axioms.contains "MatrixMath.AX1_combination_loss" == isResult do
    throwError "result assurance: AX1 must occur in the result theorem only"
  let some nativeName := axiomNames.find? (fun n => nativePrefix.isPrefixOf n.toString)
    | throwError "result assurance: native axiom is missing"
  return (Json.mkObj [
    ("axioms", strings axioms),
    ("declaration", toJson name.toString),
    ("kind", toJson "theorem"),
    ("statement", toJson statement),
    ("statement_sha256", toJson (MatrixMath.Util.sha256Hex statement))], nativeName)

/-- Emit facts queried from the compiled evaluation/result declarations.

The marker is consumed by the proof supervisor. Both rows independently require
one native axiom under the evaluation declaration, whose equality is checked
explicitly. Printed statements use the same pinned options as the core audit.
-/
def emit (evaluation result : Name) : Elab.Command.CommandElabM Unit := do
  let audit ← Elab.Command.liftTermElabM do
    let (evaluationRow, evaluationNative) ← row evaluation evaluation false
    let (resultRow, resultNative) ← row result evaluation true
    unless evaluationNative == resultNative do
      throwError "result assurance: the two theorems use different native axioms"
    let evaluationInfo ← getConstInfo evaluation
    let nativeInfo ← getConstInfo evaluationNative
    unless nativeInfo matches .axiomInfo _ do
      throwError "result assurance: native declaration is not an axiom"
    let expected ← Meta.mkEq (← Meta.mkDecide evaluationInfo.type) (mkConst ``Bool.true)
    unless ← Meta.isDefEq nativeInfo.type expected do
      throwError "result assurance: native axiom does not assert the actual closed evaluation"
    let nativeStatement ← statementOf nativeInfo.type
    let nativeRow := Json.mkObj [
      ("declaration", toJson evaluationNative.toString),
      ("kind", toJson "axiom"),
      ("statement", toJson nativeStatement),
      ("statement_sha256", toJson (MatrixMath.Util.sha256Hex nativeStatement))]
    return Json.mkObj [
      ("declarations", toJson [evaluationRow, resultRow]),
      ("native_axiom", nativeRow),
      ("schema", toJson "matrix-math-compiled-result-assurance/1")]
  Elab.Command.liftIO <| IO.println ("MATRIX_MATH_RESULT_AUDIT " ++ audit.compress)

end MatrixMath.ResultAssurance
