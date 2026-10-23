module

public import KIP126.SSComputation
import Lean

open Lean Elab Command
set_option maxHeartbeats 0

/-! SS propagation calculations have their own reviewed public interface. They
may use E₂ input and ProofTools, and cannot import Main or unowned modules. -/
run_cmd do
  let contract ← ofExcept <| Json.parse (include_str "../../interface/baselines/ss-computation-api.json")
  let named ← ofExcept <| contract.getObjValAs? (Array Json) "declarations"
  let generated ← ofExcept <| contract.getObjValAs? (Array Json) "generated_declarations"
  let expectedExports ← ofExcept <| contract.getObjValAs? (Array String) "exports"
  let env ← getEnv
  let exported := env.setExporting true
  for mod in env.header.moduleNames do
    if (`KIP126).isPrefixOf mod &&
        !(`KIP126.SpectralSequence).isPrefixOf mod &&
        !(`KIP126.AdamsSynthetic).isPrefixOf mod &&
        !(`KIP126.Literature).isPrefixOf mod &&
        !(`KIP126.AdamsComputation).isPrefixOf mod &&
        !(`KIP126.ProofTools).isPrefixOf mod &&
        !(`KIP126.SSComputation).isPrefixOf mod then
      throwError "SSComputation crossed its mathematical boundary: {mod}"
  for decl in named ++ generated do
    let name ← ofExcept <| decl.getObjValAs? String "name"
    let expectedType ← ofExcept <| decl.getObjValAs? String "type_fingerprint"
    let universes ← ofExcept <| decl.getObjValAs? (List String) "universes"
    let some info := exported.find? name.toName
      | throwError "Missing SS computation interface: {name}"
    let some idx := env.getModuleIdxFor? name.toName
      | throwError "SS computation interface has no compiled source owner: {name}"
    unless (`KIP126.SSComputation).isPrefixOf env.header.moduleNames[idx.toNat]! do
      throwError "SS computation partition declaration belongs to another source owner: {name}"
    unless toString (hash (toString info.type)) == expectedType &&
        info.levelParams.map Name.toString == universes do
      throwError "SS computation public type or universe parameters changed: {name}"
    let expectedAxioms ← ofExcept <| decl.getObjValAs? (Array String) "axioms"
    let actualAxioms ← collectAxioms name.toName
    unless (actualAxioms.map Name.toString).qsort (· < ·) == expectedAxioms.qsort (· < ·) do
      throwError "SS computation public trust dependencies changed: {name}"
  let mut actualExports : Array String := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`KIP126.SSComputation).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    unless (exported.find? name).isSome do continue
    if isPrivateName name then continue
    actualExports := actualExports.push name.toString
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected SS computation axiom dependency in {name}: {unexpected}"
  unless actualExports.qsort (· < ·) == expectedExports.qsort (· < ·) do
    throwError "SS computation public export partition changed"

#check_failure KIP126.Computation.Table.sourceValue
#check_failure KIP126.Computation.Table.value_comparison
#check_failure KIP126.Computation.ComputationInterface
#check_failure KIP126.Main.h6_sq_permanent

-- Prespectrum, concrete towers, Milnor/cobar and program rows are not part
-- of this ordinary consumer import.
#check_failure KIP126.StableHomotopy.Implementation.FoundationInput
#check_failure KIP126.Classical.Adams.MilnorCooperations
#check_failure KIP126.Core.SpectralSequence.FilteredComplex
#check_failure KIP126.Core.SpectralSequence.submoduleCokernelIso

#check_failure KIP126.Main.Axiom.challenge2
#check_failure KIP126.LinProgram.RawData.lookup

-- A source result package must never become an ordinary downstream premise.
#check_failure KIP126.Challenge2
#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Computation.RouteResults
#check_failure KIP126.Computation.Near126Results

run_cmd do
  let env ← getEnv
  let exported := env.setExporting true
  for (name, info) in env.constants.toList do
    unless (`KIP126.Computation.Standard).isPrefixOf name do continue
    unless (exported.find? name).isSome do continue
    liftTermElabM <| Meta.forallTelescope info.type fun args _ => do
      for arg in args do
        let ty ← Meta.inferType arg
        for dep in ty.getUsedConstants do
          if dep == `KIP126.Kervaire.Route.Model ||
              dep == `KIP126.Kervaire.Route.ModelData ||
              dep == `KIP126.Literature.LiteratureInterface ||
              dep == `KIP126.Literature.LiteratureResults ||
              dep == `KIP126.Computation.ComputationInterface ||
              dep == `KIP126.Computation.RouteResults ||
              dep == `KIP126.Computation.Near126Results then
            throwError "Fixed public interface asks its caller for an upstream result package: {name}"
