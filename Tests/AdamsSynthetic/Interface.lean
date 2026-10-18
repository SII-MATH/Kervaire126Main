module

public import KIP126.AdamsSynthetic
import Lean

open Lean Elab Command

set_option maxHeartbeats 0

-- A normal consumer imports only the public entry point. The contract locks
-- complete types, universe parameters, exports and transitive axiom dependencies.
-- Direct sorry obligations are locked separately by the internal trust audits.
run_cmd do
  let contract ← ofExcept <| Json.parse (include_str "../../metadata/adams-synthetic-api.json")
  let named ← ofExcept <| contract.getObjValAs? (Array Json) "declarations"
  let generated ← ofExcept <| contract.getObjValAs? (Array Json) "generated_declarations"
  let declarations := named ++ generated
  let expectedExports ← ofExcept <| contract.getObjValAs? (Array String) "exports"
  let env ← getEnv
  let exported := env.setExporting true
  for mod in env.header.moduleNames do
    if (`KIP126).isPrefixOf mod &&
        !(`KIP126.SpectralSequence).isPrefixOf mod &&
        !(`KIP126.AdamsSynthetic).isPrefixOf mod then
      throwError "AdamsSynthetic crossed its dependency boundary: {mod}"
  for decl in declarations do
    let name ← ofExcept <| decl.getObjValAs? String "name"
    let expectedType ← ofExcept <| decl.getObjValAs? String "type_fingerprint"
    let universes ← ofExcept <| decl.getObjValAs? (List String) "universes"
    let some info := exported.find? name.toName
      | throwError "Missing public interface: {name}"
    unless toString (hash (toString info.type)) == expectedType &&
        info.levelParams.map Name.toString == universes do
      throwError "Public type or universe parameters changed: {name}"
    let expectedAxioms ← ofExcept <| decl.getObjValAs? (Array String) "axioms"
    let actualAxioms ← collectAxioms name.toName
    unless (actualAxioms.map Name.toString).qsort (· < ·) == expectedAxioms.qsort (· < ·) do
      throwError "Public trust dependencies changed: {name}"
  let mut actualExports : Array String := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`KIP126.AdamsSynthetic).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    unless (exported.find? name).isSome do continue
    if isPrivateName name then continue
    actualExports := actualExports.push name.toString
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
  unless actualExports.qsort (· < ·) == expectedExports.qsort (· < ·) do
    let added := actualExports.filter (!expectedExports.contains ·)
    let missing := expectedExports.filter (!actualExports.contains ·)
    throwError "Public exports changed; added: {added}; missing: {missing}"

-- Concrete implementation helpers remain hidden. The fixed Milnor cochain
-- space, differential and square-zero statement are public type support.
#check_failure KIP126.StableHomotopy.Implementation.FoundationInput
#check_failure KIP126.Classical.Adams.MilnorCooperations
#check_failure KIP126.Core.SpectralSequence.FilteredComplex
#check_failure KIP126.Core.SpectralSequence.submoduleCokernelIso
#check_failure KIP126.AdamsSynthetic.Milnor.differentialPolynomial
#check_failure KIP126.AdamsSynthetic.Milnor.coproductGenerator

-- Redundant proof records stay retired; their mathematical premises are
-- passed directly to generic results and fixed producers remain callable.
#check_failure KIP126.AdamsSynthetic.NuExactTriangleInput
#check_failure KIP126.AdamsSynthetic.FactorizationFiltrationComparison
#check_failure KIP126.AdamsSynthetic.AdamsBoundednessInput
#check_failure KIP126.AdamsSynthetic.MappingFiltrationComparison
#check_failure KIP126.AdamsSynthetic.MappingDetectionInput
#check_failure KIP126.StableHomotopy.SphereTwistSign

-- A source result package must never become an ordinary downstream premise.
#check_failure KIP126.Challenge2
#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Computation.ComputationInterface
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Computation.RouteResults
#check_failure KIP126.Computation.Near126Results

run_cmd do
  let env ← getEnv
  let exported := env.setExporting true
  for (name, info) in env.constants.toList do
    unless (`KIP126.AdamsSynthetic.Standard).isPrefixOf name do continue
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
