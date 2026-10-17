module

/- Independent read-only cache audit. This is not a proof of either target.
   Import-all is confined to this audit artifact, outside production modules. -/
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import Lean

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192

run_cmd do
  let env ← getEnv
  let suffixes := #["quotient_nu_maps_equal_on_spheres", "shifted_quotient_sphere_congruence"]
  for suffix in suffixes do
    let roots := env.constants.toList.filter (fun (n, _) => n.toString.endsWith suffix)
    unless roots.length == 1 do throwError "Expected one audit root for {suffix}, found {roots.length}"
    let root := roots.head!.1
    let mut pending : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut holes : Array String := #[]
    let mut relevant : Array String := #[]
    let mut i := 0
    while i < pending.size do
      let n := pending[i]!
      i := i + 1
      if seen.contains n then continue
      seen := seen.insert n
      let some info := env.find? n | continue
      let some mi := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[mi.toNat]!
      unless (`KIP126).isPrefixOf mod do continue
      let body := info.value? (allowOpaque := true)
      if info.isAxiom || body.any (·.hasSorry) then holes := holes.push n.toString
      if mod == `KIP126.Literature.Standard || mod == `KIP126.AdamsSynthetic.Standard.Separation ||
          mod == `KIP126.AdamsSynthetic.Standard.Operations ||
          mod == `KIP126.AdamsSynthetic.Standard.FirstQuotientCompatibility then
        relevant := relevant.push n.toString
      pending := pending ++ info.type.getUsedConstants
      if let some b := body then pending := pending ++ b.getUsedConstants
    let ax ← collectAxioms root
    let target1 := `KIP126.AdamsSynthetic.Standard.firstQuotient_positive_shift
    let target2 := `KIP126.AdamsSynthetic.Standard.firstQuotient_suspension
    logInfo (Json.mkObj [
      ("root", toJson root.toString),
      ("positive_target_in_closure", toJson (seen.contains target1)),
      ("suspension_target_in_closure", toJson (seen.contains target2)),
      ("axioms", toJson (ax.map Name.toString)),
      ("pending_source_nodes", toJson holes),
      ("relevant_project_nodes", toJson relevant)]).pretty
