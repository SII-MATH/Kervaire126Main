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
import all KIP126.AdamsSynthetic.Internal.Milnor.Cobar
import all KIP126.AdamsSynthetic.Internal.Milnor.Cohomology
import all KIP126.AdamsSynthetic.Internal.Milnor.Complex
import all KIP126.AdamsSynthetic.Internal.Milnor.Hi
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Data
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Grading
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Multiplication
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Normalization
import all KIP126.AdamsSynthetic.Internal.Milnor.Polynomial.Preservation
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
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Inverse
import all KIP126.AdamsSynthetic.Internal.SphereBHS.Tower
import all KIP126.AdamsSynthetic.Mapping
import all KIP126.AdamsSynthetic.MappingComposition
import all KIP126.AdamsSynthetic.MappingDetection
import all KIP126.AdamsSynthetic.MappingEnrichment
import all KIP126.AdamsSynthetic.Normalized
import all KIP126.AdamsSynthetic.PageExtensions
import all KIP126.AdamsSynthetic.Quotients
import all KIP126.AdamsSynthetic.Realization
import all KIP126.AdamsSynthetic.Recovery
import all KIP126.AdamsSynthetic.Source
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
import all KIP126.AdamsSynthetic.Standard.Source
import all KIP126.AdamsSynthetic.Suspension
import all KIP126.AdamsSynthetic.System
import all KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Weight
import all KIP126.Literature
import all KIP126.Literature.Applicability
import all KIP126.Literature.BHS
import all KIP126.Literature.BX
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.Delivery
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Geometry.Browder
import all KIP126.Literature.Geometry.KervaireInvariant
import all KIP126.Literature.Geometry.Manifolds
import all KIP126.Literature.LambdaInversionAdams
import all KIP126.Literature.Lift
import all KIP126.Literature.May
import all KIP126.Literature.Moss
import all KIP126.Literature.RealizationTransport
import all KIP126.Literature.Rigidity
import all KIP126.Literature.Secondary
import all KIP126.Literature.Standard
import all KIP126.Literature.Standard.AdamsTwoLine
import all KIP126.Literature.Standard.Filtration
import all KIP126.Literature.Standard.FiniteQuotientAdditivity
import all KIP126.Literature.Standard.FiniteQuotientCone
import all KIP126.Literature.Standard.FiniteQuotientConstruction
import all KIP126.Literature.Standard.FiniteQuotientGhosts
import all KIP126.Literature.Standard.FiniteQuotientMiddle
import all KIP126.Literature.Standard.FiniteQuotientNaturality
import all KIP126.Literature.Standard.FiniteQuotientNoReturn
import all KIP126.Literature.Standard.FiniteQuotientNormalized
import all KIP126.Literature.Standard.FiniteQuotientObjectCases
import all KIP126.Literature.Standard.FiniteQuotientPositive
import all KIP126.Literature.Standard.FiniteQuotientRecognition
import all KIP126.Literature.Standard.FiniteQuotientRotations
import all KIP126.Literature.Standard.FiniteQuotientRowCriterion
import all KIP126.Literature.Standard.FiniteQuotientRows
import all KIP126.Literature.Standard.FiniteQuotientSuspension
import all KIP126.Literature.Standard.FiniteQuotientTail
import all KIP126.Literature.Standard.FiniteQuotientTriangle
import all KIP126.Literature.Standard.FiniteQuotientWhitehead
import all KIP126.Literature.Standard.QuotientAlgebra
import all KIP126.Literature.Standard.Secondary
import all KIP126.Literature.Toda
import all KIP126.Literature.Triangles
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.FiniteFiltration
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryLambda
import all KIP126.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.ProofTools.GeneralizedMahowald.Detection
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.Language
import all KIP126.ProofTools.Laws
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.Paper.ClassicalKernelCompactness
import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.Paper.OriginalStatements
import all KIP126.ProofTools.Representatives
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.SpectralSequence
import all KIP126.SpectralSequence.Basic
import all KIP126.SpectralSequence.Basic.Category.Data
import all KIP126.SpectralSequence.Basic.Category.Predicates
import all KIP126.SpectralSequence.Basic.Category.Proofs
import all KIP126.SpectralSequence.Basic.Data
import all KIP126.SpectralSequence.Basic.MorphismCriterion
import all KIP126.SpectralSequence.Basic.PageHomology.Data
import all KIP126.SpectralSequence.Basic.Predicates
import all KIP126.SpectralSequence.Basic.Proofs
import all KIP126.SpectralSequence.BoundedExtension.TwoTerm.Data
import all KIP126.SpectralSequence.BoundedExtension.TwoTerm.Proofs
import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import all KIP126.SpectralSequence.Computation.API.Predicates
import all KIP126.SpectralSequence.Computation.Morphism.Proofs
import all KIP126.SpectralSequence.Computation.PageThree.Proofs
import all KIP126.SpectralSequence.Computation.Predicates
import all KIP126.SpectralSequence.Computation.Proofs
import all KIP126.SpectralSequence.Computation.State.Predicates
import all KIP126.SpectralSequence.Computation.State.Proofs
import all KIP126.SpectralSequence.Consumer.BoundedExtension
import all KIP126.SpectralSequence.Consumer.Extension
import all KIP126.SpectralSequence.Convergence.Category.Data
import all KIP126.SpectralSequence.Convergence.Data
import all KIP126.SpectralSequence.Convergence.Predicates
import all KIP126.SpectralSequence.Convergence.Proofs
import all KIP126.SpectralSequence.Convergence.Vanishing.Proofs
import all KIP126.SpectralSequence.Crossing.Data
import all KIP126.SpectralSequence.Crossing.Predicates
import all KIP126.SpectralSequence.Crossing.Proofs
import all KIP126.SpectralSequence.Extension.Complex.Data
import all KIP126.SpectralSequence.Extension.Complex.Proofs
import all KIP126.SpectralSequence.Extension.Data
import all KIP126.SpectralSequence.Extension.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Data
import all KIP126.SpectralSequence.FilteredComplex.SSData.Data
import all KIP126.SpectralSequence.FilteredComplex.SSData.Predicates
import all KIP126.SpectralSequence.FilteredComplex.SSData.Proofs
import all KIP126.SpectralSequence.FilteredComplex.SSDataConstruction.Data
import all KIP126.SpectralSequence.FilteredComplex.SSDataConstruction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Page.Converse.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Page.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Proofs
import all KIP126.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data
import all KIP126.SpectralSequence.FilteredDifferential.Boundaries
import all KIP126.SpectralSequence.FilteredDifferential.Cycles
import all KIP126.SpectralSequence.FilteredDifferential.Data
import all KIP126.SpectralSequence.FilteredDifferential.Helpers
import all KIP126.SpectralSequence.FilteredDifferential.Proofs
import all KIP126.SpectralSequence.FilteredDifferential.SquareZero
import all KIP126.SpectralSequence.FilteredPage.Data
import all KIP126.SpectralSequence.FilteredPage.Proofs
import all KIP126.SpectralSequence.FinitePageCalculus.Proofs
import all KIP126.SpectralSequence.Internal.Algebra.Coefficients.Data
import all KIP126.SpectralSequence.Internal.Algebra.Completion.Data
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Data
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Predicates
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Proofs
import all KIP126.SpectralSequence.Internal.Algebra.Graded.Data
import all KIP126.SpectralSequence.Internal.Algebra.Truncation.Data
import all KIP126.SpectralSequence.Internal.Algebra.Truncation.Proofs
import all KIP126.SpectralSequence.ModuleQuotient.Data
import all KIP126.SpectralSequence.ModuleQuotient.Proofs
import all KIP126.SpectralSequence.ModuleSubobject.Proofs
import all KIP126.SpectralSequence.Multiplicative
import all KIP126.SpectralSequence.MultiplicativeCategory
import all KIP126.SpectralSequence.PageLevel.Data
import all KIP126.SpectralSequence.PageLevel.Proofs
import all KIP126.SpectralSequence.Permanence.Predicates
import all KIP126.SpectralSequence.Permanence.Proofs
import all KIP126.SpectralSequence.Transport
import all KIP126.SpectralSequence.Truncation.Data
import all KIP126.SpectralSequence.Truncation.Predicates
import all KIP126.SpectralSequence.Truncation.Proofs
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option pp.universes true
run_cmd do
  let env ← getEnv
  let mut result : Array Json := #[]
  for root in #[`KIP126.ProofTools.Paper.extensionBoundary_of_exact, `KIP126.ProofTools.Paper.infiniteExtension_to_classicalExtension] do
    let some ri := env.find? root | throwError "missing root {root}"
    let ty ← liftTermElabM (Meta.ppExpr ri.type)
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut rows : Array Json := #[]
    while let some n := todo.back? do
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let body := ci.value? (allowOpaque := true)
      let deps := ci.type.getUsedConstants ++ (body.map Expr.getUsedConstants).getD #[]
      todo := todo ++ deps
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless (`KIP126).isPrefixOf mod do continue
      if ci.isAxiom || ci.type.hasSorry || body.any (·.hasSorry) then
        throwError "unexpected project axiom/placeholder {n} (root {root})"
      rows := rows.push <| Json.mkObj [("name",toJson n.toString),("module",toJson mod.toString),("deps",toJson (deps.map Name.toString))]
    let axioms ← collectAxioms root
    logInfo m!"{root}: axioms {axioms}; project nodes {rows.size}"
    result := result.push <| Json.mkObj [("root",toJson root.toString),("type",toJson ty.pretty),("universes",toJson (ri.levelParams.map Name.toString)),("type_fingerprint",toJson (toString (hash (toString ri.type)))),("axioms",toJson (axioms.map Name.toString)),("rows",Json.arr rows)]
  liftIO <| IO.FS.writeFile "/tmp/PaperAudit20261019.json" (Json.arr result).compress
