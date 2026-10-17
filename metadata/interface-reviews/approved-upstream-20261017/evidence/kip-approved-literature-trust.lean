module
import all KIP126.Literature
import all KIP126.Literature.Applicability
import all KIP126.Literature.BHS
import all KIP126.Literature.BX
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.Delivery
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Lift
import all KIP126.Literature.May
import all KIP126.Literature.Moss
import all KIP126.Literature.RealizationTransport
import all KIP126.Literature.Rigidity
import all KIP126.Literature.Secondary
import all KIP126.Literature.Standard
import all KIP126.Literature.Standard.Filtration
import all KIP126.Literature.Standard.QuotientAlgebra
import all KIP126.Literature.Standard.Secondary
import all KIP126.Literature.Toda
import all KIP126.Literature.Triangles
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126.Literature).isPrefixOf mod do continue
    let body := info.value? (allowOpaque := true)
    let direct := info.type.hasSorry || body.any (·.hasSorry)
    let synthetic := info.type.hasSyntheticSorry || body.any (·.hasSyntheticSorry)
    let mut deps := info.type.getUsedConstants
    if let some value := body then deps := deps ++ value.getUsedConstants
    let ty ← if direct then liftTermElabM (Meta.ppExpr info.type) else pure Format.nil
    let ranges ← findDeclarationRanges? name
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | _ => "generated"
    let axioms ← collectAxioms name
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("source_name", toJson ((privateToUserName? name).getD name).toString),
      ("declaration_kind", toJson kind),
      ("line", toJson (ranges.map (·.selectionRange.pos.line))),
      ("is_axiom", toJson info.isAxiom), ("direct_sorry", toJson direct),
      ("synthetic_sorry", toJson synthetic),
      ("full_type", toJson ty.pretty),
      ("type_fingerprint", toJson (toString (hash (toString info.type)))),
      ("body_fingerprint", toJson (if direct then toString (hash (toString body)) else "")),
      ("dependencies", toJson (deps.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "/tmp/kip-approved-literature-trust.json" (Json.arr rows).compress
  logInfo m!"Captured trust information for {rows.size} project declarations"
