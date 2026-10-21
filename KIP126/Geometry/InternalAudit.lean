module

import all KIP126.Geometry
import all KIP126.Geometry.Kervaire
public meta import Checks.Registry.Geometry
import Lean

/-! Full-body audit of every Geometry declaration, including private lemmas.
There are no local proof/construction holes. Transitive upstream obligations
remain permitted only in their own modules and are retained in the Blueprint.
-/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let ledger ← Lean.ofExcept <| Json.parse Checks.Registry.Geometry.proofObligationLedger
  let entries ← Lean.ofExcept <| ledger.getObjValAs? (Array Json) "obligations"
  for row in entries do
    let mod ← Lean.ofExcept <| row.getObjValAs? String "module"
    if (`KIP126.Geometry).isPrefixOf mod.toName then
      throwError "Geometry must have no permitted local proof/construction holes"
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Geometry).isPrefixOf mod do continue
    let body := info.value? (allowOpaque := true)
    if info.isAxiom || info.type.hasSorry || body.any (·.hasSorry) then
      throwError "Geometry contains a local axiom or unfinished proof: {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless body.isSome do throwError "Missing Geometry proof body: {name}"
    | _ => pure ()
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  logInfo m!"Geometry trust audit: {checked} declarations; no local axioms or proof holes; upstream obligations retained"
