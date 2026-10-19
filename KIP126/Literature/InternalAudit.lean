module
import all KIP126.Literature
import all KIP126.Literature.Applicability
import all KIP126.Literature.BHS
import all KIP126.Literature.BX
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.Delivery
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Geometry.Manifolds
import all KIP126.Literature.Geometry.KervaireInvariant
import all KIP126.Literature.Geometry.Browder
import all KIP126.Literature.Lift
import all KIP126.Literature.May
import all KIP126.Literature.Moss
import all KIP126.Literature.RealizationTransport
import all KIP126.Literature.Rigidity
import all KIP126.Literature.Secondary
import all KIP126.Literature.Standard
import all KIP126.Literature.Standard.AdamsTwoLine
import all KIP126.Literature.Standard.Filtration
import all KIP126.Literature.Standard.FiniteQuotientAdditivity
import all KIP126.Literature.Standard.FiniteQuotientCone
import all KIP126.Literature.Standard.FiniteQuotientConstruction
import all KIP126.Literature.Standard.FiniteQuotientGhosts
import all KIP126.Literature.Standard.FiniteQuotientMiddle
import all KIP126.Literature.Standard.FiniteQuotientNaturality
import all KIP126.Literature.Standard.FiniteQuotientNoReturn
import all KIP126.Literature.Standard.FiniteQuotientNormalized
import all KIP126.Literature.Standard.FiniteQuotientObjectCases
import all KIP126.Literature.Standard.FiniteQuotientPositive
import all KIP126.Literature.Standard.FiniteQuotientRecognition
import all KIP126.Literature.Standard.FiniteQuotientRowCriterion
import all KIP126.Literature.Standard.FiniteQuotientRows
import all KIP126.Literature.Standard.FiniteQuotientRotations
import all KIP126.Literature.Standard.FiniteQuotientSuspension
import all KIP126.Literature.Standard.FiniteQuotientTail
import all KIP126.Literature.Standard.FiniteQuotientTriangle
import all KIP126.Literature.Standard.FiniteQuotientWhitehead
import all KIP126.Literature.Standard.QuotientAlgebra
import all KIP126.Literature.Standard.Secondary
import all KIP126.Literature.Toda
import all KIP126.Literature.Triangles


public meta import Checks.Registry
import Lean

/-! Trust audit for fixed upstream declarations. Only the exact individually
registered proof/construction holes are permitted; project axioms and synthetic
(elaboration-error) holes are always rejected. SpectralSequence stays sorry-free. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let ledger ← Lean.ofExcept <| Json.parse proofObligationLedger
  let entries ← Lean.ofExcept <| ledger.getObjValAs? (Array Json) "obligations"
  let expected : Array Json ← entries.filterM fun (row : Json) => do
    let mod ← Lean.ofExcept <| row.getObjValAs? String "module"
    pure ((`KIP126.Literature).isPrefixOf mod.toName)
  let expectedNames : Array String ← expected.mapM fun (row : Json) => Lean.ofExcept <| row.getObjValAs? String "name"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut holes : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Literature).isPrefixOf mod do continue
    if info.isAxiom then throwError "Project axiom declaration: {name}"
    let body := info.value? (allowOpaque := true)
    if info.type.hasSyntheticSorry || body.any (·.hasSyntheticSorry) then
      throwError "Synthetic sorry from failed elaboration: {name}"
    if info.type.hasSorry || body.any (·.hasSorry) then
      holes := holes.push name.toString
      let some entry := expected.find? (fun e => e.getObjValAs? String "name" == .ok name.toString)
        | throwError "Unregistered proof/construction obligation: {name}"
      let expectedType ← Lean.ofExcept <| entry.getObjValAs? String "type_fingerprint"
      let expectedBody ← Lean.ofExcept <| entry.getObjValAs? String "body_fingerprint"
      unless expectedType == toString (hash (toString info.type)) &&
          expectedBody == toString (hash (toString body)) do
        throwError "Registered obligation changed; review its exact type/body: {name}"
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
    checked := checked + 1
  unless holes.qsort (· < ·) == expectedNames.qsort (· < ·) do
    throwError "Proof obligation registry has stale or missing declarations: {holes}"
  logInfo m!"Literature trust audit: {checked} declarations; {holes.size} individually registered pending proofs/constructions; no project axioms"
