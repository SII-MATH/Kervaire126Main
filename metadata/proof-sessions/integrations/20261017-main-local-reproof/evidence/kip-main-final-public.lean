module
public import KIP126.Main
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option pp.universes true
set_option pp.explicit false
set_option pp.proofs true
set_option pp.deepTerms true
run_cmd do
  let env ← getEnv
  let exported := env.setExporting true
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Main).isPrefixOf mod do continue
    unless (exported.find? name).isSome do continue
    if isPrivateName name then continue
    let ranges ← findDeclarationRanges? name
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | _ => "generated"
    let ty ← liftTermElabM <| Meta.ppExpr info.type
    let axioms ← collectAxioms name
    rows := rows.push <| Json.mkObj [
      ("axioms", toJson (axioms.map Name.toString)),
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("kind", toJson kind), ("full_type", toJson ty.pretty),
      ("line", toJson (ranges.map (·.selectionRange.pos.line))),
      ("column", toJson (ranges.map (·.selectionRange.pos.column))),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("universes", toJson (info.levelParams.map Name.toString)),
      ("type_fingerprint", toJson (toString (hash (toString info.type))))]
  liftIO <| IO.FS.writeFile "/tmp/kip-main-final-public.json" (Json.arr rows).compress
  logInfo m!"Captured {rows.size} exported project declarations"
