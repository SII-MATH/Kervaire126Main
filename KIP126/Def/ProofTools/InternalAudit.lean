module

import all KIP126.Def.ProofTools.ConvergenceOperations
import all KIP126.Def.ProofTools.DetectionOperations
import all KIP126.Def.ProofTools.FiltrationOperations
import all KIP126.Def.ProofTools.FiniteFiltration
import all KIP126.Def.ProofTools.GeneralizedLeibniz
import all KIP126.Def.ProofTools.GeneralizedMahowald.Adjacent
import all KIP126.Def.ProofTools.GeneralizedMahowald.BoundaryDetection
import all KIP126.Def.ProofTools.GeneralizedMahowald.BoundaryLambda
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.Def.ProofTools.GeneralizedMahowald.Detection
import all KIP126.Def.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.Def.ProofTools.GeneralizedMahowald.FinalOperations
import all KIP126.Def.ProofTools.GeneralizedMahowald.KernelCorrection
import all KIP126.Def.ProofTools.GeneralizedMahowald.KernelTriangles
import all KIP126.Def.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.Def.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.Def.ProofTools.GeneralizedMahowald.Sphere
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.Def.ProofTools.GeneralizedMahowald
import all KIP126.Def.ProofTools.Language
import all KIP126.Def.ProofTools.Laws
import all KIP126.Def.ProofTools.Representatives
import all KIP126.Def.ProofTools.Standard
import all KIP126.Def.ProofTools.Stretching
import all KIP126.Def.ProofTools.StretchingRepresentatives
import all KIP126.Def.ProofTools

public meta import Checks.Registry
import Lean

/-! Trust audit for article-owned proof and construction responsibilities. Only the exact individually
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
    pure ((`KIP126.Def.ProofTools).isPrefixOf mod.toName)
  let expectedNames : Array String ← expected.mapM fun (row : Json) => Lean.ofExcept <| row.getObjValAs? String "name"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut holes : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Def.ProofTools).isPrefixOf mod do continue
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
  let originalGapDeclarations := #[
    "KIP126.ProofTools.Standard.generalizedLeibniz",
    "KIP126.ProofTools.Standard.generalizedMahowald"]
  unless holes.qsort (· < ·) == originalGapDeclarations.qsort (· < ·) do
    throwError "ProofTools permits only the original GL1/GL2 and MH1/MH2 gaps: {holes}"
  -- Stretching may use unfinished fixed upstream objects/results, but its
  -- finite correction proof must not depend on any unproved paper tool.
  let mut pending := #[`KIP126.ProofTools.Standard.finitePageExtensionStretching]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing proof dependency: {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf mod do continue
    let body := info.value? (allowOpaque := true)
    if (`KIP126.Def.ProofTools).isPrefixOf mod &&
        (info.type.hasSorry || body.any (·.hasSorry)) then
      throwError "Stretching depends on a local paper proof gap: {name}"
    pending := pending ++ info.type.getUsedConstants
    if let some value := body then pending := pending ++ value.getUsedConstants
  logInfo m!"ProofTools trust audit: {checked} declarations; {holes.size} individually registered pending proofs/constructions; no project axioms"
