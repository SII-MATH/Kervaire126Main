module

import all KIP126.Def.AdamsSynthetic.AdamsFiltration
import all KIP126.Def.AdamsSynthetic.Background
import all KIP126.Def.AdamsSynthetic.Coherence
import all KIP126.Def.AdamsSynthetic.Comparisons
import all KIP126.Def.AdamsSynthetic.Compatibility
import all KIP126.Def.AdamsSynthetic.Configuration
import all KIP126.Def.AdamsSynthetic.ConsumerOperations
import all KIP126.Def.AdamsSynthetic.Context
import all KIP126.Def.AdamsSynthetic.Detection
import all KIP126.Def.AdamsSynthetic.ESSShift
import all KIP126.Def.AdamsSynthetic.Enrichment
import all KIP126.Def.AdamsSynthetic.Extension
import all KIP126.Def.AdamsSynthetic.ExtensionLabels
import all KIP126.Def.AdamsSynthetic.ExtensionWitnesses
import all KIP126.Def.AdamsSynthetic.ExtensionZero
import all KIP126.Def.AdamsSynthetic.Families
import all KIP126.Def.AdamsSynthetic.HomologyExactness
import all KIP126.Def.AdamsSynthetic.Mapping
import all KIP126.Def.AdamsSynthetic.MappingComposition
import all KIP126.Def.AdamsSynthetic.MappingDetection
import all KIP126.Def.AdamsSynthetic.MappingEnrichment
import all KIP126.Def.AdamsSynthetic.Normalized
import all KIP126.Def.AdamsSynthetic.PageExtensions
import all KIP126.Def.AdamsSynthetic.Quotients
import all KIP126.Def.AdamsSynthetic.Realization
import all KIP126.Def.AdamsSynthetic.Recovery
import all KIP126.Def.AdamsSynthetic.Sphere
import all KIP126.Def.AdamsSynthetic.Standard.Background
import all KIP126.Def.AdamsSynthetic.Standard.Filtration
import all KIP126.Def.AdamsSynthetic.Standard.Operations
import all KIP126.Def.AdamsSynthetic.Standard.Realization
import all KIP126.Def.AdamsSynthetic.Standard.Separation
import all KIP126.Def.AdamsSynthetic.Standard
import all KIP126.Def.AdamsSynthetic.Suspension
import all KIP126.Def.AdamsSynthetic.System
import all KIP126.Def.AdamsSynthetic.Tower
import all KIP126.Def.AdamsSynthetic.Weight
import all KIP126.Def.AdamsSynthetic

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
    pure ((`KIP126.Def.AdamsSynthetic).isPrefixOf mod.toName)
  let expectedNames : Array String ← expected.mapM fun (row : Json) => Lean.ofExcept <| row.getObjValAs? String "name"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut holes : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Def.AdamsSynthetic).isPrefixOf mod do continue
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
  logInfo m!"AdamsSynthetic trust audit: {checked} declarations; {holes.size} individually registered pending proofs/constructions; no project axioms"
