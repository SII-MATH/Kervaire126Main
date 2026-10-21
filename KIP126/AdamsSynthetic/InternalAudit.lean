module
import all KIP126.AdamsSynthetic
import all KIP126.AdamsSynthetic.AdamsFiltration
import all KIP126.AdamsSynthetic.Background
import all KIP126.AdamsSynthetic.Coherence
import all KIP126.AdamsSynthetic.Comparisons
import all KIP126.AdamsSynthetic.Compatibility
import all KIP126.AdamsSynthetic.Configuration
import all KIP126.AdamsSynthetic.ConsumerOperations
import all KIP126.AdamsSynthetic.Context
import all KIP126.AdamsSynthetic.Detection
import all KIP126.AdamsSynthetic.ESSShift
import all KIP126.AdamsSynthetic.Enrichment
import all KIP126.AdamsSynthetic.Extension
import all KIP126.AdamsSynthetic.ExtensionLabels
import all KIP126.AdamsSynthetic.ExtensionWitnesses
import all KIP126.AdamsSynthetic.ExtensionZero
import all KIP126.AdamsSynthetic.Families
import all KIP126.AdamsSynthetic.HomologyExactness
import all KIP126.AdamsSynthetic.Mapping
import all KIP126.AdamsSynthetic.MappingComposition
import all KIP126.AdamsSynthetic.MappingDetection
import all KIP126.AdamsSynthetic.MappingEnrichment
import all KIP126.AdamsSynthetic.Normalized
import all KIP126.AdamsSynthetic.PageExtensions
import all KIP126.AdamsSynthetic.Quotients
import all KIP126.AdamsSynthetic.Realization
import all KIP126.AdamsSynthetic.Recovery
import all KIP126.AdamsSynthetic.Sphere
import all KIP126.AdamsSynthetic.SphereTensor
import all KIP126.AdamsSynthetic.Standard
import all KIP126.AdamsSynthetic.Standard.Background
import all KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.AdamsSynthetic.Standard.Filtration
import all KIP126.AdamsSynthetic.Standard.FirstQuotientCompatibility
import all KIP126.AdamsSynthetic.Standard.Operations
import all KIP126.AdamsSynthetic.Standard.Realization
import all KIP126.AdamsSynthetic.Standard.Separation
import all KIP126.AdamsSynthetic.Suspension
import all KIP126.AdamsSynthetic.System
import all KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Weight
import all KIP126.AdamsSynthetic.Internal.Milnor.Cobar
import all KIP126.AdamsSynthetic.Internal.Milnor.Cohomology
import all KIP126.AdamsSynthetic.Internal.Milnor.Complex
import all KIP126.AdamsSynthetic.Internal.Milnor.Hi
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Data
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Grading
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Multiplication
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Normalization
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Preservation
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Inverse
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Milnor
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Tower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsSequence
import all KIP126.AdamsSynthetic.Internal.Source.AdamsTower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsNaturality
import all KIP126.AdamsSynthetic.Internal.Source.Completion
import all KIP126.AdamsSynthetic.Internal.Source.DerivedSmash
import all KIP126.AdamsSynthetic.Internal.Source.MilnorComparison
import all KIP126.AdamsSynthetic.Internal.Source.PointSet
import all KIP126.AdamsSynthetic.Internal.Source.PointSetRecognition
import all KIP126.AdamsSynthetic.Internal.Source.Prespectrum
import all KIP126.AdamsSynthetic.Internal.Source.Recognition
import all KIP126.AdamsSynthetic.Internal.Source.Sphere
import all KIP126.AdamsSynthetic.Internal.Source.SurvivalTransport
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Standard.Source


public meta import Checks.Registry.AdamsSynthetic
import Lean

/-! Trust audit for fixed upstream declarations. Only the exact individually
registered proof/construction holes are permitted; project axioms and synthetic
(elaboration-error) holes are always rejected. SpectralSequence stays sorry-free. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let ledger ← Lean.ofExcept <| Json.parse Checks.Registry.AdamsSynthetic.proofObligationLedger
  let entries ← Lean.ofExcept <| ledger.getObjValAs? (Array Json) "obligations"
  let expected : Array Json ← entries.filterM fun (row : Json) => do
    let mod ← Lean.ofExcept <| row.getObjValAs? String "module"
    pure ((`KIP126.AdamsSynthetic).isPrefixOf mod.toName)
  let expectedNames : Array String ← expected.mapM fun (row : Json) => Lean.ofExcept <| row.getObjValAs? String "name"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut holes : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.AdamsSynthetic).isPrefixOf mod do continue
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
  -- These generic tower proofs are independent of the fixed background and
  -- must not delegate their responsibility to another registered placeholder.
  let towerRoots : Array Name := #[
    `KIP126.AdamsSynthetic.Internal.Source.towerDifferential_exists,
    `KIP126.AdamsSynthetic.Internal.Source.towerD_comp,
    `KIP126.AdamsSynthetic.Internal.Source.towerD_kernel,
    `KIP126.AdamsSynthetic.Internal.Source.towerD_image,
    `KIP126.AdamsSynthetic.Internal.Source.canonicalTowerMap,
    `KIP126.AdamsSynthetic.Internal.Source.towerSSDataMap,
    `KIP126.AdamsSynthetic.Internal.Source.towerSequenceMap,
    `KIP126.AdamsSynthetic.Internal.Source.canonicalSequenceMap]
  for target in towerRoots do
    let candidates := env.constants.toList.filter fun (name, _) =>
      ((privateToUserName? name).getD name) == target
    unless candidates.length == 1 do
      throwError "Expected one private tower proof: {target}"
    let name := candidates.head!.1
    let axioms ← collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Generic tower proof has an unfinished dependency: {name}: {axioms}"
  unless holes.qsort (· < ·) == expectedNames.qsort (· < ·) do
    throwError "Proof obligation registry has stale or missing declarations: {holes}"
  logInfo m!"AdamsSynthetic trust audit: {checked} declarations; {holes.size} individually registered pending proofs/constructions; no project axioms"
