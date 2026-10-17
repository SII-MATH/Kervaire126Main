module
import Lean
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
import all KIP126.AdamsSynthetic.Standard.Background
import all KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.AdamsSynthetic.Standard.Filtration
import all KIP126.AdamsSynthetic.Standard.Operations
import all KIP126.AdamsSynthetic.Standard.Realization
import all KIP126.AdamsSynthetic.Standard.Separation
import all KIP126.AdamsSynthetic.Standard
import all KIP126.AdamsSynthetic.Suspension
import all KIP126.AdamsSynthetic.System
import all KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Weight
import all KIP126.AdamsSynthetic
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
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Standard.Source
import all KIP126.Computation.Basis
import all KIP126.Computation.Source
import all KIP126.Computation.Standard
import all KIP126.Computation.Table.Archive
import all KIP126.Computation.Table.Data
import all KIP126.Computation.Table.Dimensions
import all KIP126.Computation.Table.Internal.ZeroDimension
import all KIP126.Computation.Table.Relations
import all KIP126.Computation.Table.Syntax
import all KIP126.Computation.Table.ThetaRelations
import all KIP126.Computation.Table.Values
import all KIP126.Computation.Table
import all KIP126.Computation
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
import all KIP126.Literature.Standard.Filtration
import all KIP126.Literature.Standard.QuotientAlgebra
import all KIP126.Literature.Standard.Secondary
import all KIP126.Literature.Standard
import all KIP126.Literature.Toda
import all KIP126.Literature.Triangles
import all KIP126.Literature
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.FiniteFiltration
import all KIP126.ProofTools.GeneralizedLeibniz
import all KIP126.ProofTools.GeneralizedMahowald.Adjacent
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryDetection
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryLambda
import all KIP126.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.ProofTools.GeneralizedMahowald.Detection
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.FinalOperations
import all KIP126.ProofTools.GeneralizedMahowald.KernelCorrection
import all KIP126.ProofTools.GeneralizedMahowald.KernelTriangles
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.ProofTools.GeneralizedMahowald.Sphere
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedMahowald
import all KIP126.ProofTools.Language
import all KIP126.ProofTools.Laws
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.Representatives
import all KIP126.ProofTools.Standard
import all KIP126.ProofTools.Stretching
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.ProofTools
import all KIP126.SpectralSequence.Basic.Category.Data
import all KIP126.SpectralSequence.Basic.Category.Predicates
import all KIP126.SpectralSequence.Basic.Category.Proofs
import all KIP126.SpectralSequence.Basic.Data
import all KIP126.SpectralSequence.Basic.MorphismCriterion
import all KIP126.SpectralSequence.Basic.PageHomology.Data
import all KIP126.SpectralSequence.Basic.Predicates
import all KIP126.SpectralSequence.Basic.Proofs
import all KIP126.SpectralSequence.Basic
import all KIP126.SpectralSequence.BoundedExtension.BoundedComplex.Data
import all KIP126.SpectralSequence.BoundedExtension.Chain.Data
import all KIP126.SpectralSequence.BoundedExtension.Chain.Proofs
import all KIP126.SpectralSequence.BoundedExtension.Detection.Predicates
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Construction.Data
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Construction.Proofs
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Data
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Proofs
import all KIP126.SpectralSequence.BoundedExtension.SelfComplex.Data
import all KIP126.SpectralSequence.BoundedExtension.Sequence.Data
import all KIP126.SpectralSequence.BoundedExtension.Sequence.Predicates
import all KIP126.SpectralSequence.BoundedExtension.Sequence.Proofs
import all KIP126.SpectralSequence.BoundedExtension.SpectralSequence.Data
import all KIP126.SpectralSequence.BoundedExtension.SpectralSequence.Proofs
import all KIP126.SpectralSequence.BoundedExtension.Square.Construction.Data
import all KIP126.SpectralSequence.BoundedExtension.Square.Data
import all KIP126.SpectralSequence.BoundedExtension.Square.Proofs
import all KIP126.SpectralSequence.BoundedExtension.TwoTerm.Data
import all KIP126.SpectralSequence.BoundedExtension.TwoTerm.Proofs
import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import all KIP126.SpectralSequence.BoundedExtension
import all KIP126.SpectralSequence.Commutativity.Basic.Proofs
import all KIP126.SpectralSequence.Commutativity.Detection.Data
import all KIP126.SpectralSequence.Commutativity.Detection.Proofs
import all KIP126.SpectralSequence.Commutativity.Predicates
import all KIP126.SpectralSequence.Commutativity.Square.Data
import all KIP126.SpectralSequence.Commutativity.Square.Proofs
import all KIP126.SpectralSequence.Commutativity
import all KIP126.SpectralSequence.Completion.Comparison.Data
import all KIP126.SpectralSequence.Completion.Comparison.Proofs
import all KIP126.SpectralSequence.Completion.CompletedFiltration.Data
import all KIP126.SpectralSequence.Completion.Data
import all KIP126.SpectralSequence.Completion.Predicates
import all KIP126.SpectralSequence.Completion.Proofs
import all KIP126.SpectralSequence.Completion.UniversalProperty.Data
import all KIP126.SpectralSequence.Completion.UniversalProperty.Proofs
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
import all KIP126.SpectralSequence.FilteredComplex.Crossing.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Crossing
import all KIP126.SpectralSequence.FilteredComplex.Data
import all KIP126.SpectralSequence.FilteredComplex.HomologyTarget.Data
import all KIP126.SpectralSequence.FilteredComplex.SSData.Data
import all KIP126.SpectralSequence.FilteredComplex.SSData.Predicates
import all KIP126.SpectralSequence.FilteredComplex.SSData.Proofs
import all KIP126.SpectralSequence.FilteredComplex.SSData
import all KIP126.SpectralSequence.FilteredComplex.SSDataConstruction.Data
import all KIP126.SpectralSequence.FilteredComplex.SSDataConstruction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Affine.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.AffineRestriction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Finiteness.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Morphism.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Morphism.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Obstruction.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Obstruction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Page.Converse.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Page.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Proofs
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Restriction.Data
import all KIP126.SpectralSequence.FilteredComplex.Solutions.Restriction.Proofs
import all KIP126.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data
import all KIP126.SpectralSequence.FilteredComplex.WeakConvergence.Comparison.Proofs
import all KIP126.SpectralSequence.FilteredComplex.WeakConvergence.Data
import all KIP126.SpectralSequence.FilteredComplex
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
import all KIP126.SpectralSequence.PageComparison.Data
import all KIP126.SpectralSequence.PageComparison.Predicates
import all KIP126.SpectralSequence.PageComparison.Raw.Data
import all KIP126.SpectralSequence.PageComparison.Raw.Proofs
import all KIP126.SpectralSequence.PageLevel.Data
import all KIP126.SpectralSequence.PageLevel.Proofs
import all KIP126.SpectralSequence.Permanence.Predicates
import all KIP126.SpectralSequence.Permanence.Proofs
import all KIP126.SpectralSequence.Representatives.Proofs
import all KIP126.SpectralSequence.Transport
import all KIP126.SpectralSequence.Truncation.Data
import all KIP126.SpectralSequence.Truncation.Predicates
import all KIP126.SpectralSequence.Truncation.Proofs
import all KIP126.SpectralSequence.Truncation
import all KIP126.SpectralSequence.UnboundedExtension.TruncatedComplex.Data
import all KIP126.SpectralSequence.UnboundedExtension.TruncatedComplex.Proofs
import all KIP126.SpectralSequence.UnboundedExtension.TruncatedSpectralSequence.Data
import all KIP126.SpectralSequence
import all KIP126.Main.BoundaryFormula
import all KIP126.Main.ChoiceIndependence
import all KIP126.Main.Internal.Choice.Completion
import all KIP126.Main.ClassicalReduction
import all KIP126.Main.Conditions
import all KIP126.Main.DifferentialCriterion
import all KIP126.Main.DifferentialReduction
import all KIP126.Main.H6SquarePermanent
import all KIP126.Main.Internal.AlphaOne.Classical
import all KIP126.Main.Internal.AlphaOne.Coherence
import all KIP126.Main.Internal.AlphaOne.Corrections
import all KIP126.Main.Internal.AlphaOne.Detection
import all KIP126.Main.Internal.AlphaOne.ErrorFiltration
import all KIP126.Main.Internal.AlphaOne.Existence
import all KIP126.Main.Internal.AlphaOne.Filtration
import all KIP126.Main.Internal.AlphaOne.FiniteFrames
import all KIP126.Main.Internal.AlphaOne.FiniteWindow
import all KIP126.Main.Internal.AlphaOne.LastDifferential
import all KIP126.Main.Internal.AlphaOne.Layers
import all KIP126.Main.Internal.AlphaOne.PageConsequences
import all KIP126.Main.Internal.AlphaOne.PageVanishing
import all KIP126.Main.Internal.AlphaOne.Quotients
import all KIP126.Main.Internal.AlphaOne.Staircase
import all KIP126.Main.Internal.Choice.Filtration
import all KIP126.Main.Internal.Choice.FinitePages
import all KIP126.Main.Internal.Choice.Gap
import all KIP126.Main.Internal.Choice.Invariance
import all KIP126.Main.Internal.Choice.LambdaInjectivity
import all KIP126.Main.Internal.Choice.OrderTwo
import all KIP126.Main.Internal.Choice.PageFrames
import all KIP126.Main.Internal.CofiberRigidity
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.FiniteReflection
import all KIP126.Main.Internal.High125.Detector
import all KIP126.Main.Internal.High125.Differential
import all KIP126.Main.Internal.High125.Filtration
import all KIP126.Main.Internal.High125.Finite
import all KIP126.Main.Internal.High125.Injectivity
import all KIP126.Main.Internal.High125.Pages
import all KIP126.Main.Internal.High125.Source
import all KIP126.Main.Internal.High125.Tail
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.LowEta
import all KIP126.Main.Internal.NuFifth.Frame
import all KIP126.Main.Internal.NuFifth.Lift
import all KIP126.Main.Internal.NuNinth.Assembly
import all KIP126.Main.Internal.NuNinth.Fourth
import all KIP126.Main.Internal.NuNinth.Frames
import all KIP126.Main.Internal.NuNinth.Incoming
import all KIP126.Main.Internal.NuNinth.Lift
import all KIP126.Main.Internal.NuNinth.Shift
import all KIP126.Main.Internal.NuNinth.Unit
import all KIP126.Main.Internal.NuThree.Actual
import all KIP126.Main.Internal.NuThree.ActualOperations
import all KIP126.Main.Internal.NuThree.Assembly
import all KIP126.Main.Internal.NuThree.ClassicalZero
import all KIP126.Main.Internal.NuThree.Finite
import all KIP126.Main.Internal.NuThree.Mahowald
import all KIP126.Main.Internal.NuThree.Shift
import all KIP126.Main.Internal.NuThree.Suspension
import all KIP126.Main.Internal.NuThree.ZeroExtensions
import all KIP126.Main.Internal.NuThree.ZeroLabels
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.Assembly
import all KIP126.Main.Internal.Selected.Classical
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.Internal.Selected.Exhaustion
import all KIP126.Main.Internal.Selected.FinitePages
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Selected.NormalizedFacts
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.Selected.NuErrorData
import all KIP126.Main.Internal.Selected.ProductDetection
import all KIP126.Main.Internal.Selected.ProductZero
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.Selected.TargetFrame
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Theta.Detection
import all KIP126.Main.Internal.Theta.NoCrossing
import all KIP126.Main.Internal.Theta.OrderTwo
import all KIP126.Main.Internal.Theta.Products
import all KIP126.Main.Internal.Theta.RealizationKernel
import all KIP126.Main.Internal.Theta.Shuffle
import all KIP126.Main.Internal.Theta.TodaAlgebra
import all KIP126.Main.Internal.Theta.TodaCofiber
import all KIP126.Main.Internal.Theta.TodaExistence
import all KIP126.Main.Internal.Theta.TodaIndeterminacy
import all KIP126.Main.Internal.Theta.ZeroDegree
import all KIP126.Main.RepresentativeResults
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.AnyYError
import all KIP126.Main.SectionSeven.AnyYFinite
import all KIP126.Main.SectionSeven.AnyYPeeling
import all KIP126.Main.SectionSeven.AnyYShuffle
import all KIP126.Main.SectionSeven.AnyYSplit
import all KIP126.Main.SectionSeven.AnyYTarget
import all KIP126.Main.SectionSeven.CofiberRigidity
import all KIP126.Main.SectionSeven.Final
import all KIP126.Main.SectionSeven.Indeterminacy
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.SectionSeven.NuFifthAction
import all KIP126.Main.SectionSeven.NuTarget
import all KIP126.Main.SectionSeven.NuTargetCommute
import all KIP126.Main.SectionSeven.NuTargetCosets
import all KIP126.Main.SectionSeven.NuTargetDetection
import all KIP126.Main.SectionSeven.NuTargetE2Calculus
import all KIP126.Main.SectionSeven.NuTargetFinite
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
import all KIP126.Main.SectionSeven.NuTargetFrame
import all KIP126.Main.SectionSeven.NuTargetFull
import all KIP126.Main.SectionSeven.NuTargetH0Products
import all KIP126.Main.SectionSeven.NuTargetLambda
import all KIP126.Main.SectionSeven.NuTargetLinear
import all KIP126.Main.SectionSeven.NuTargetPeeling
import all KIP126.Main.SectionSeven.NuTargetProducts
import all KIP126.Main.SectionSeven.NuTargetWindows
import all KIP126.Main.SectionSeven.NuTargetYLambda
import all KIP126.Main.SectionSeven.NuTargetYRelation
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.ThetaEta
import all KIP126.Main.SectionSeven.ThetaToda
import all KIP126.Main.SectionSeven.TodaNonempty
import all KIP126.Main.SectionSeven.WeakInitialLambda
import all KIP126.Main.SectionSeven.WeakInitialNonzero
import all KIP126.Main.SectionSeven.WeakRepresentative
import all KIP126.Main.SectionSeven.WeakStrip
import all KIP126.Main.SectionSeven.WeakStripFinite
import all KIP126.Main.SectionSeven.WeakStripTorsion
import all KIP126.Main.SectionSeven.WeakYDetection
import all KIP126.Main.SectionSeven.WeakYFinite
import all KIP126.Main.SquareClassification
import all KIP126.Main.TableOne
import all KIP126.Main
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration

public import KIP126.Main.Conditions
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.Internal.AlphaOne.Existence
import all KIP126.Main.Internal.NuNinth.Assembly

/-! Complete local statements from Section 7 of AimPaper. The public
detection predicates retain the fixed quotient maps and nonzero associated
graded classes. The proofs call the existing constructions on those objects. -/

@[expose] section
namespace KIP126.Main.Paper
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Literature.Standard (eta syntheticH0)
noncomputable section

/-- Nonzero detection of the specified sphere class in its actual finite
lambda quotient, using the page map of the quotient projection. -/
public def FiniteDetected (n : ℕ) (_hn : 0 < n) (s t : ℤ) (k : ℕ)
    (x : KIP126.AdamsSynthetic.Standard.sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) n)) : Prop :=
  DetectsNonzero (model.convergence (.quotient n .sphere)) (s,t,t-k)
    ((KIP126.AdamsSynthetic.Standard.family.quotientProjection
      KIP126.AdamsSynthetic.Standard.syntheticSphere n).pageMap 2 (s,t,t-k)
        (KIP126.AdamsSynthetic.Standard.comparison.sphereE2 s t k x)) a

/-- Nonzero detection in the fixed untruncated synthetic sphere. -/
public def SphereDetected (s t : ℤ) (k : ℕ)
    (x : KIP126.AdamsSynthetic.Standard.sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (model.convergence .sphere) (s,t,t-k)
    (KIP126.AdamsSynthetic.Standard.comparison.sphereE2 s t k x) a

/-- AimPaper Lemma 7.14 (`lem:x1239`). One Q11 representative supplies
the compatible Q9 alpha-one class, its two correction identities for every
untruncated U representative, and its exact h0 annihilation relation. -/
public theorem lemma_x1239 :
    ∃ a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11),
      let a9 := a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide)
      FiniteDetected 11 (by decide) 9 132 0 KIP126.Computation.Standard.V a11 ∧
      FiniteDetected 9 (by decide) 9 132 0 KIP126.Computation.Standard.V a9 ∧
      (∀ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum),
        SphereDetected 10 134 0 KIP126.Computation.Standard.U u →
        ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
          (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
          lambdaMultiply 3 (sphereAction eta a9) =
            (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
              lambdaMultiply 3 (quotientClass 9 u)) +
            (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
              lambdaMultiply 6 a2) ∧
          sphereAction eta a2 = lambdaMultiply 1 a3) ∧
      lambdaMultiply 3 (sphereAction syntheticH0 a9) = 0 := by
  exact KIP126.Main.Internal.AlphaOne.alpha_one_exists

/-- AimPaper Lemma 7.20 (`lem:nuext125`). The normalized Hopf element
acts on an existential representative of lambda^4 X by lambda times an
existential representative of lambda^5 Y in the same actual Q9. -/
public theorem lemma_nuext125 :
    ∃ (x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
      (y : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
      FiniteDetected 9 (by decide) 8 130 4 KIP126.Computation.Standard.X x ∧
      FiniteDetected 9 (by decide) 11 136 5 KIP126.Computation.Standard.Y y ∧
      sphereAction (KIP126.Literature.normalizedNu model
        KIP126.Literature.Standard.nuCofiber_nu_exponent) x = lambdaMultiply 1 y := by
  exact KIP126.Main.Internal.NuNinth.nu_extension_in_ninth_quotient

end
end KIP126.Main.Paper


set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
#check @KIP126.Main.Paper.FiniteDetected
#check @KIP126.Main.Paper.SphereDetected
#check @KIP126.Main.Paper.lemma_x1239
#check @KIP126.Main.Paper.lemma_nuext125
#print axioms KIP126.Main.Paper.lemma_x1239
#print axioms KIP126.Main.Paper.lemma_nuext125
