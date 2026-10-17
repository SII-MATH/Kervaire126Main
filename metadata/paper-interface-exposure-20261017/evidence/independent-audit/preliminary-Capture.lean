module
import all KIP126.Main.Internal.AlphaOne.Existence
import all KIP126.Main.Internal.NuNinth.Assembly
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
run_cmd do
  let env ← getEnv
  let targetNames := #["KIP126.Main.Internal.AlphaOne.alpha_one_exists", "KIP126.Main.Internal.NuNinth.nu_extension_in_ninth_quotient", "KIP126.ProofTools.Internal.Leibniz.higher_source_image_of_nonessential", "KIP126.ProofTools.Internal.Leibniz.tower_correction_of_nonessential"]
  let mut targets : Array Name := #[]
  for (name, _) in env.constants.toList do
    if targetNames.contains ((privateToUserName? name).getD name).toString then
      targets := targets.push name
  let mut pending := targets
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf mod do continue
    let body := info.value? (allowOpaque := true)
    let direct := info.type.hasSorry || body.any (·.hasSorry)
    let mut deps := info.type.getUsedConstants
    if let some value := body then deps := deps ++ value.getUsedConstants
    pending := pending ++ deps
    let ty ← if direct || targets.contains name then liftTermElabM (Meta.ppExpr info.type) else pure Format.nil
    let ranges ← findDeclarationRanges? name
    let axioms ← if targets.contains name then collectAxioms name else pure #[]
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("source_name", toJson ((privateToUserName? name).getD name).toString),
      ("line", toJson (ranges.map (·.selectionRange.pos.line))),
      ("is_axiom", toJson info.isAxiom), ("direct_sorry", toJson direct),
      ("full_type", toJson ty.pretty),
      ("type_fingerprint", toJson (toString (hash (toString info.type)))),
      ("body_fingerprint", toJson (toString (hash (toString body)))),
      ("dependencies", toJson (deps.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "/tmp/aimpaper-new-interface-audit-20261017/dependency-capture.json" (Json.arr rows).compress
  logInfo m!"Captured {targets.size} targets and {rows.size} project dependencies"
