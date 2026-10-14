module

public import KIP126.Def.Literature
import Lean

open Lean Elab Command

set_option maxHeartbeats 0

-- A normal consumer imports only the public entry point. The contract locks
-- complete types, universe parameters, exports and transitive axiom dependencies.
run_cmd do
  let contract ← ofExcept <| Json.parse (include_str "../../literature-api.json")
  let named ← ofExcept <| contract.getObjValAs? (Array Json) "declarations"
  let generated ← ofExcept <| contract.getObjValAs? (Array Json) "generated_declarations"
  let declarations := named ++ generated
  let expectedExports ← ofExcept <| contract.getObjValAs? (Array String) "exports"
  let env ← getEnv
  let exported := env.setExporting true
  for mod in env.header.moduleNames do
    if (`KIP126).isPrefixOf mod &&
        !(`KIP126.Def.SpectralSequence).isPrefixOf mod &&
        !(`KIP126.Def.AdamsSynthetic).isPrefixOf mod &&
        !(`KIP126.Def.Literature).isPrefixOf mod then
      throwError "Literature crossed its dependency boundary: {mod}"
  for decl in declarations do
    let name ← ofExcept <| decl.getObjValAs? String "name"
    let expectedType ← ofExcept <| decl.getObjValAs? String "type_fingerprint"
    let universes ← ofExcept <| decl.getObjValAs? (List String) "universes"
    let some info := exported.find? name.toName
      | throwError "Missing public interface: {name}"
    unless toString (hash (toString info.type)) == expectedType &&
        info.levelParams.map Name.toString == universes do
      throwError "Public type or universe parameters changed: {name}"
  let mut actualExports : Array String := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`KIP126.Def.Literature).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    unless (exported.find? name).isSome do continue
    if isPrivateName name then continue
    actualExports := actualExports.push name.toString
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
  unless actualExports.qsort (· < ·) == expectedExports.qsort (· < ·) do
    let added := actualExports.filter (!expectedExports.contains ·)
    let missing := expectedExports.filter (!actualExports.contains ·)
    throwError "Public exports changed; added: {added}; missing: {missing}"

-- Prespectrum, concrete towers, Milnor/cobar and program rows are not part
-- of this ordinary consumer import.
#check_failure KIP126.StableHomotopy.Implementation.FoundationInput
#check_failure KIP126.Classical.Adams.MilnorCooperations
#check_failure KIP126.Core.SpectralSequence.FilteredComplex
#check_failure KIP126.Core.SpectralSequence.submoduleCokernelIso

#check_failure KIP126.Main.Axiom.challenge2
#check_failure KIP126.LinProgram.RawData.lookup
