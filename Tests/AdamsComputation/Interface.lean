module

public import KIP126.AdamsComputation
import Lean

open Lean Elab Command
set_option maxHeartbeats 0

/-! The Adams computation entry is consumable before ProofTools and SS. Its own lock
fixes public types, universes, axiom dependencies and generated declarations. -/
run_cmd do
  let contract ← ofExcept <| Json.parse (include_str "../../interface/baselines/adams-computation-api.json")
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
        !(`KIP126.AdamsComputation).isPrefixOf mod then
      throwError "AdamsComputation imports a later or unowned mathematical layer: {mod}"
  for decl in named ++ generated do
    let name ← ofExcept <| decl.getObjValAs? String "name"
    let expectedType ← ofExcept <| decl.getObjValAs? String "type_fingerprint"
    let universes ← ofExcept <| decl.getObjValAs? (List String) "universes"
    let some info := exported.find? name.toName
      | throwError "Missing Adams computation interface: {name}"
    let some idx := env.getModuleIdxFor? name.toName
      | throwError "Adams computation interface has no compiled source owner: {name}"
    unless (`KIP126.AdamsComputation).isPrefixOf env.header.moduleNames[idx.toNat]! do
      throwError "Adams computation partition declaration belongs to another source owner: {name}"
    unless toString (hash (toString info.type)) == expectedType &&
        info.levelParams.map Name.toString == universes do
      throwError "Adams computation public type or universe parameters changed: {name}"
    let expectedAxioms ← ofExcept <| decl.getObjValAs? (Array String) "axioms"
    let actualAxioms ← collectAxioms name.toName
    unless (actualAxioms.map Name.toString).qsort (· < ·) == expectedAxioms.qsort (· < ·) do
      throwError "Adams computation public trust dependencies changed: {name}"
  let mut actualExports : Array String := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`KIP126.AdamsComputation).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    unless (exported.find? name).isSome do continue
    if isPrivateName name then continue
    actualExports := actualExports.push name.toString
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound && n != `sorryAx
    unless unexpected.isEmpty do
      throwError "Unexpected Adams computation axiom dependency in {name}: {unexpected}"
  unless actualExports.qsort (· < ·) == expectedExports.qsort (· < ·) do
    throwError "Adams computation public export partition changed"

#check KIP126.Computation.Standard.d2_h6
#check KIP126.Computation.Standard.d2_h0Six_h6
#check KIP126.Computation.Table.direct_d2_result
#check_failure KIP126.Computation.Table.result
#check_failure KIP126.Computation.Table.Raw.claims
#check_failure KIP126.Computation.Standard.w_to_e6
#check_failure KIP126.Computation.Standard.v_not_hit
#check KIP126.Computation.Table.Raw.Kind
#check KIP126.Computation.Table.Raw.Claim
#check_failure KIP126.Computation.Table.sourceValue
#check_failure KIP126.Computation.Table.value_comparison
#check_failure KIP126.Computation.ComputationInterface
