module
import all KIP126.SpectralSequence.InternalAudit
import all KIP126.AdamsSynthetic.InternalAudit
import all KIP126.Literature.InternalAudit
import all KIP126.E2Computation.InternalAudit
import all KIP126.ProofTools.InternalAudit
import all KIP126.AdamsCalculations.InternalAudit
import all KIP126.Computation.InternalAudit
import all KIP126.Main.InternalAudit
import Lean

/- Read-only export of the current compiled environment, including private and
compiler-generated declarations. This script introduces no mathematical API. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192

run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless #[`KIP126.SpectralSequence, `KIP126.AdamsSynthetic, `KIP126.Literature,
      `KIP126.E2Computation, `KIP126.ProofTools, `KIP126.AdamsCalculations,
      `KIP126.Computation, `KIP126.Main].any (·.isPrefixOf mod) do continue
    let body := info.value? (allowOpaque := true)
    let mut deps := info.type.getUsedConstants
    if let some value := body then deps := deps ++ value.getUsedConstants
    let ranges ← findDeclarationRanges? name
    let axioms ← collectAxioms name
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | _ => "generated"
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson mod.toString),
      ("source_name", toJson ((privateToUserName? name).getD name).toString),
      ("declaration_kind", toJson kind),
      ("line", toJson (ranges.map (·.selectionRange.pos.line))),
      ("is_axiom", toJson info.isAxiom),
      ("direct_sorry", toJson (info.type.hasSorry || body.any (·.hasSorry))),
      ("synthetic_sorry", toJson (info.type.hasSyntheticSorry || body.any (·.hasSyntheticSorry))),
      ("dependencies", toJson (deps.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile ".lake/blueprint/kernel.json" (Json.arr rows).compress
  logInfo m!"Blueprint: captured {rows.size} compiled project declarations"
