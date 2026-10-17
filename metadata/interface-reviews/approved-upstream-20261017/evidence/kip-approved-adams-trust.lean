module
import all KIP126.AdamsSynthetic
import all KIP126.AdamsSynthetic.AdamsFiltration
import all KIP126.AdamsSynthetic.Background
import all KIP126.AdamsSynthetic.Coherence
import all KIP126.AdamsSynthetic.Comparisons
import all KIP126.AdamsSynthetic.Compatibility
import all KIP126.AdamsSynthetic.Configuration
import all KIP126.AdamsSynthetic.ConsumerOperations
import all KIP126.AdamsSynthetic.Context
import all KIP126.AdamsSynthetic.Detection
import all KIP126.AdamsSynthetic.ESSShift
import all KIP126.AdamsSynthetic.Enrichment
import all KIP126.AdamsSynthetic.Extension
import all KIP126.AdamsSynthetic.ExtensionLabels
import all KIP126.AdamsSynthetic.ExtensionWitnesses
import all KIP126.AdamsSynthetic.ExtensionZero
import all KIP126.AdamsSynthetic.Families
import all KIP126.AdamsSynthetic.HomologyExactness
import all KIP126.AdamsSynthetic.Mapping
import all KIP126.AdamsSynthetic.MappingComposition
import all KIP126.AdamsSynthetic.MappingDetection
import all KIP126.AdamsSynthetic.MappingEnrichment
import all KIP126.AdamsSynthetic.Normalized
import all KIP126.AdamsSynthetic.PageExtensions
import all KIP126.AdamsSynthetic.Quotients
import all KIP126.AdamsSynthetic.Realization
import all KIP126.AdamsSynthetic.Recovery
import all KIP126.AdamsSynthetic.Sphere
import all KIP126.AdamsSynthetic.SphereTensor
import all KIP126.AdamsSynthetic.Standard
import all KIP126.AdamsSynthetic.Standard.Background
import all KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.AdamsSynthetic.Standard.Filtration
import all KIP126.AdamsSynthetic.Standard.FirstQuotientCompatibility
import all KIP126.AdamsSynthetic.Standard.Operations
import all KIP126.AdamsSynthetic.Standard.Realization
import all KIP126.AdamsSynthetic.Standard.Separation
import all KIP126.AdamsSynthetic.Suspension
import all KIP126.AdamsSynthetic.System
import all KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Weight
import all KIP126.AdamsSynthetic.Internal.Milnor.Cobar
import all KIP126.AdamsSynthetic.Internal.Milnor.Cohomology
import all KIP126.AdamsSynthetic.Internal.Milnor.Complex
import all KIP126.AdamsSynthetic.Internal.Milnor.Hi
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Data
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Grading
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Multiplication
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Normalization
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Preservation
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Inverse
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Milnor
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Tower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsSequence
import all KIP126.AdamsSynthetic.Internal.Source.AdamsTower
import all KIP126.AdamsSynthetic.Internal.Source.Completion
import all KIP126.AdamsSynthetic.Internal.Source.DerivedSmash
import all KIP126.AdamsSynthetic.Internal.Source.MilnorComparison
import all KIP126.AdamsSynthetic.Internal.Source.PointSet
import all KIP126.AdamsSynthetic.Internal.Source.PointSetRecognition
import all KIP126.AdamsSynthetic.Internal.Source.Prespectrum
import all KIP126.AdamsSynthetic.Internal.Source.Recognition
import all KIP126.AdamsSynthetic.Internal.Source.Sphere
import all KIP126.AdamsSynthetic.Internal.Source.SurvivalTransport
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Standard.Source
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
    unless (`KIP126.AdamsSynthetic).isPrefixOf mod do continue
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
  liftIO <| IO.FS.writeFile "/tmp/kip-approved-adams-trust.json" (Json.arr rows).compress
  logInfo m!"Captured trust information for {rows.size} project declarations"
