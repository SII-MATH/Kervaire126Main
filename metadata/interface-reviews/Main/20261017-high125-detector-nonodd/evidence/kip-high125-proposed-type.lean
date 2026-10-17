module
public import KIP126.Literature
import Lean
open Lean Elab Command CategoryTheory
set_option pp.universes true
set_option pp.proofs true
private def proposedHigh125Conclusion : Prop :=
  ¬ KIP126.AdamsSynthetic.IsOddTorsionMap
    (KIP126.Literature.Standard.high125 ≫ KIP126.Literature.Standard.tmfUnit)
run_cmd do
  let env ← getEnv
  let some info := env.find? ``proposedHigh125Conclusion | throwError "Missing proposed type"
  let some body := info.value? | throwError "Missing proposed type expression"
  if body.hasSorry || body.hasMVar then throwError "Invalid candidate expression"
  let ty ← liftTermElabM <| Meta.ppExpr body
  let row := Json.mkObj [
    ("status", toJson "candidate-only; production declaration unchanged"),
    ("full_type", toJson ty.pretty),
    ("type_fingerprint", toJson (toString (hash (toString body)))),
    ("universes", toJson (info.levelParams.map Name.toString)),
    ("type_dependencies", toJson (body.getUsedConstants.map Name.toString))]
  liftIO <| IO.FS.writeFile "/tmp/kip-high125-proposed-type.json" row.pretty
  logInfo m!"Proposed conclusion expression elaborated; no proof or production change"
