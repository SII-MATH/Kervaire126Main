module
import all KIP126.ProofTools.InternalAudit
import all KIP126.AdamsSynthetic.InternalAudit
import all KIP126.E2Computation.InternalAudit
import all KIP126.Literature.InternalAudit
import all KIP126.SpectralSequence.InternalAudit
import Lean

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 16384
set_option pp.universes true
set_option pp.deepTerms true

run_cmd do
  let env ← getEnv
  let roots := #[
    `KIP126.ProofTools.Internal.FiniteLifting.cutoffAdamsDifferentialAtLevel,
    `KIP126.ProofTools.Internal.FiniteLifting.finiteLevelExtensionToClassical]
  let mut results : Array Json := #[]
  for sourceName in roots do
    let some (root, ci) := env.constants.toList.find? (fun (n, _) =>
        ((privateToUserName? n).getD n) == sourceName)
      | throwError "Missing complete theorem {sourceName}"
    let ty ← liftTermElabM (Meta.ppExpr ci.type)
    logInfo m!"Complete theorem: {sourceName}\n{ty}"
    let ax ← collectAxioms root
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut gaps : Array Json := #[]
    let mut localNames : Array String := #[]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some info := env.find? n | continue
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless (`KIP126).isPrefixOf mod do continue
      let body := info.value? (allowOpaque := true)
      let src := ((privateToUserName? n).getD n).toString
      if (`KIP126.ProofTools).isPrefixOf mod then localNames := localNames.push src
      if info.type.hasSorry || body.any (·.hasSorry) then
        if (`KIP126.ProofTools).isPrefixOf mod then
          throwError "Local ProofTools proof gap: {n}"
        gaps := gaps.push (Json.mkObj [
          ("name", toJson n.toString), ("source_name", toJson src),
          ("module", toJson mod.toString)])
      todo := todo ++ info.type.getUsedConstants
      if let some b := body then todo := todo ++ b.getUsedConstants
    results := results.push (Json.mkObj [
      ("name", toJson sourceName.toString),
      ("type", toJson ty.pretty),
      ("axioms", toJson (ax.map Name.toString)),
      ("proof_tools_dependencies", toJson localNames),
      ("upstream_direct_gaps", toJson gaps)])
    logInfo m!"{sourceName}: {localNames.size} ProofTools dependencies without local holes; {gaps.size} upstream responsibilities"
  liftIO <| IO.FS.writeFile "/tmp/finite-level-theorem-audit.json" (Json.arr results).pretty
