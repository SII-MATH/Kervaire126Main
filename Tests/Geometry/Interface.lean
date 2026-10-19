module

public import KIP126.Geometry
import Lean

open Lean Elab Command

set_option maxHeartbeats 0

-- A normal consumer imports only the public entry point. The contract locks
-- complete types, universe parameters, exports and transitive axiom dependencies.
-- Direct sorry obligations are locked separately by the internal trust audits.
run_cmd do
  let contract ← ofExcept <| Json.parse (include_str "../../interface/baselines/geometry-api.json")
  let named ← ofExcept <| contract.getObjValAs? (Array Json) "declarations"
  let generated ← ofExcept <| contract.getObjValAs? (Array Json) "generated_declarations"
  let declarations := named ++ generated
  let expectedExports ← ofExcept <| contract.getObjValAs? (Array String) "exports"
  let env ← getEnv
  let exported := env.setExporting true
  for mod in env.header.moduleNames do
    if (`KIP126).isPrefixOf mod &&
        !(`KIP126.SpectralSequence).isPrefixOf mod &&
        !(`KIP126.AdamsSynthetic).isPrefixOf mod &&
        !(`KIP126.Literature).isPrefixOf mod &&
        !(`KIP126.E2Computation).isPrefixOf mod &&
        !(`KIP126.ProofTools).isPrefixOf mod &&
        !(`KIP126.AdamsCalculations).isPrefixOf mod &&
        !(`KIP126.Main).isPrefixOf mod &&
        !(`KIP126.Geometry).isPrefixOf mod then
      throwError "Geometry crossed its dependency boundary: {mod}"
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
    unless (`KIP126.Geometry).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
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

-- These endpoints must be unconditional geometric statements. In particular,
-- neither a caller-supplied Browder theorem nor a synthetic model may appear
-- among their hypotheses or be used to define their geometric predicates.
run_cmd do
  let env ← getEnv
  let first := ``KIP126.Geometry.kervaire_invariant_one_126
  let second := ``KIP126.Geometry.kervaire_invariant_one_iff
  let some firstInfo := env.find? first | throwError "Missing geometric existence theorem"
  if firstInfo.type.isForall then throwError "Geometric existence acquired a caller hypothesis"
  for root in #[first, second] do
    unless wasOriginallyTheorem env root do throwError "Geometric endpoint is not a theorem: {root}"
    let some info := env.find? root | throwError "Missing geometric endpoint: {root}"
    let mut pending := info.type.getUsedConstants
    let mut seen : NameSet := {}
    while let some name := pending.back? do
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some dependency := env.find? name | throwError "Missing geometric dependency: {name}"
      let some idx := env.getModuleIdxFor? name | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless (`KIP126).isPrefixOf mod do continue
      unless (`KIP126.Literature.Geometry).isPrefixOf mod do
        throwError "Geometric statement depends on a non-geometric project object: {name}: {mod}"
      pending := pending ++ dependency.type.getUsedConstants
      if let some value := dependency.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants

