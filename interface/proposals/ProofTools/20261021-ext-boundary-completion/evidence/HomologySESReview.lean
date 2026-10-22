module

import all KIP126.ProofTools.ExtBoundaryComparison.HomologySES
import Lean

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/- Independent inspection of the actual production module. This command
does not add a mathematical premise or assert the still-missing Ext bridge. -/
run_cmd do
  let env ← getEnv
  let owner := `KIP126.ProofTools.ExtBoundaryComparison.HomologySES
  let roots := #[
    `KIP126.ProofTools.Internal.ExtBoundaryComparison.HomologySES.rotated_homology_short_exact_of_zero,
    `KIP126.ProofTools.Internal.ExtBoundaryComparison.HomologySES.positive_normalized_homology_zero,
    `KIP126.ProofTools.Internal.ExtBoundaryComparison.HomologySES.positive_normalized_rotated_homology_short_exact]
  for sourceName in roots do
    let candidates := env.constants.toList.filter fun (n, _) =>
      ((privateToUserName? n).getD n) == sourceName
    unless candidates.length == 1 do
      throwError "Expected one actual source declaration for {sourceName}, got {candidates.length}"
    let (root, info) := candidates.head!
    unless isPrivateName root do
      throwError "Helper unexpectedly public: {root}"
    logInfo m!"Source root: {sourceName}"
    logInfo m!"Kernel type: {info.type}"
    logInfo m!"Universe parameters: {info.levelParams}"
    let axioms ← collectAxioms root
    logInfo m!"Inherited axiom list: {axioms}"
    let mut todo := #[root]
    let mut seen : Array Name := #[]
    let mut boundary : Array Name := #[]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      let some info := env.find? n | throwError "Missing declaration: {n}"
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      if mod != owner then
        if !boundary.contains n then boundary := boundary.push n
        continue
      seen := seen.push n
      if info.isAxiom then throwError "Local axiom: {n}"
      let some body := info.value? (allowOpaque := true)
        | throwError "Local proof body unavailable: {n}"
      if info.type.hasSorry || body.hasSorry ||
          info.type.hasSyntheticSorry || body.hasSyntheticSorry then
        throwError "Local incomplete proof: {n}"
      todo := todo ++ info.type.getUsedConstants ++ body.getUsedConstants
    logInfo m!"Local actual-body closure checked: {seen.size} declarations"
    logInfo m!"Local source names: {seen.map fun n => ((privateToUserName? n).getD n).toString}"
    logInfo m!"Boundary constant count: {boundary.size}"
    let mut projectBoundary : Array String := #[]
    for n in boundary do
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      if (`KIP126.ProofTools).isPrefixOf mod then
        throwError "Unexpected dependency on another ProofTools result: {n}"
      if (`KIP126).isPrefixOf mod then
        projectBoundary := projectBoundary.push ((privateToUserName? n).getD n).toString
    logInfo m!"Actual upstream project boundary: {projectBoundary}"
  logInfo "Independent HomologySES inspection passed; no Ext identity asserted."
