module
import all KIP126.SpectralSequence.InternalAudit
import all KIP126.AdamsSynthetic.InternalAudit
import all KIP126.Literature.InternalAudit
import all KIP126.E2Computation.InternalAudit
import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.Paper.OriginalStatements
import all KIP126.ProofTools.Paper.ClassicalKernelCompactness
import all KIP126.ProofTools.Paper.ExtensionDescent
import all KIP126.ProofTools.Paper.ExtensionIndeterminacy
import all KIP126.ProofTools.Paper.ExtensionEssentialSource
import all KIP126.ProofTools.Paper.ExtensionCrossingDichotomy
import all KIP126.ProofTools.Paper.Crossing
import all KIP126.ProofTools.Paper.SyntheticExtensions.LambdaRho
import all KIP126.ProofTools.Paper.SyntheticExtensions
import all KIP126.ProofTools.Paper.NumericalExamples
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.Paper.NuCofiberNumericalDifferential
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions
import all KIP126.ProofTools.Paper.DoublingCrossing
import all KIP126.ProofTools.Paper.DoublingMaximalLift
import all KIP126.ProofTools.StandardSpecializations
import all KIP126.ProofTools
import all KIP126.ProofTools.MahowaldLeibniz
import all KIP126.ProofTools.MahowaldLeibniz.FiniteCore
import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein
import all KIP126.ProofTools.MahowaldLeibniz.Filtration
import all KIP126.ProofTools.MahowaldLeibniz.CoefficientShift
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare
import all KIP126.ProofTools.MahowaldLeibniz.LastLayer
import all KIP126.ProofTools.MahowaldLeibniz.LastLayerNative
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryLastLayer
import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
import all KIP126.ProofTools.MahowaldLeibniz.Corollaries
import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.MahowaldLeibniz.NativeImageSquare
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSource
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.MahowaldLeibniz.TerminalOrdinary
import all KIP126.ProofTools.MahowaldLeibniz.CommonCore
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGCorollary
import all KIP126.ProofTools.MahowaldLeibniz.PositiveFirstCore
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryImageSquare
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGCore
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHCore
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalComposition
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGSource
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHCorollary
import all KIP126.ProofTools.MahowaldLeibniz.TopTarget
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.FiniteFiltration
import all KIP126.ProofTools.GeneralizedLeibniz
import all KIP126.ProofTools.GeneralizedLeibniz.Boundary
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDivision
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLift
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.MinimalBottom
import all KIP126.ProofTools.GeneralizedLeibniz.LevelSource
import all KIP126.ProofTools.GeneralizedLeibniz.LevelBoundary
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.LevelGL
import all KIP126.ProofTools.GeneralizedLeibniz.LevelZero
import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibnizAtLevel
import all KIP126.ProofTools.GeneralizedLeibniz.LevelDivision
import all KIP126.ProofTools.LambdaDivision
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingShift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingRange
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.GeneralizedLeibniz.SquareRepresentatives
import all KIP126.ProofTools.GeneralizedLeibniz.WitnessSquare
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedLeibniz.Survival
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.ProofTools.GeneralizedLeibniz.DivisionLabels
import all KIP126.ProofTools.GeneralizedLeibniz.SphereAutomorphisms
import all KIP126.ProofTools.GeneralizedLeibniz.BoundaryDivision
import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
import all KIP126.ProofTools.GeneralizedMahowald.CofiberIdentification
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import all KIP126.ProofTools.GeneralizedMahowald.HSourceSelection
import all KIP126.ProofTools.GeneralizedMahowald.HMapCoherence
import all KIP126.ProofTools.GeneralizedMahowald.HTarget
import all KIP126.ProofTools.GeneralizedMahowald.HTargetDetection
import all KIP126.ProofTools.GeneralizedMahowald.TargetSurvival
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionTarget
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaShift
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection
import all KIP126.ProofTools.GeneralizedMahowald.ShiftLabels
import all KIP126.ProofTools.GeneralizedMahowald.Synchronization
import all KIP126.ProofTools.GeneralizedMahowald.Geometry
import all KIP126.ProofTools.GeneralizedMahowald.ActualNoCrossing
import all KIP126.ProofTools.GeneralizedMahowald.ClassicalLift
import all KIP126.ProofTools.GeneralizedMahowald.FiniteMay
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelLabels
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelStatement
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelInputs
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLambdaSurjectivity
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelConclusion
import all KIP126.ProofTools.GeneralizedMahowald.FiniteMay3x3
import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelSourceLabel
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelOutputLabels
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelAssembly
import all KIP126.ProofTools.GeneralizedMahowald.OctahedralPullback
import all KIP126.ProofTools.GeneralizedMahowald.CommonShiftEdge
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerAssembly
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerTarget
import all KIP126.ProofTools.GeneralizedMahowald.ZeroLayerSpecial
import all KIP126.ProofTools.GeneralizedMahowald.StatementReview
import all KIP126.ProofTools.GeneralizedMahowald.BottomNuInjection
import all KIP126.ProofTools.GeneralizedMahowald.CorrectedTotalTarget
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuPremises
import all KIP126.ProofTools.GeneralizedMahowald.CommonTotalTarget
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import all KIP126.ProofTools.GeneralizedMahowald.TotalFTransport
import all KIP126.ProofTools.GeneralizedMahowald.CorrectedCoordinates
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeNativeTarget
import all KIP126.ProofTools.GeneralizedMahowald.SourceBoundaryReview
import all KIP126.ProofTools.GeneralizedMahowald.MinimalFinalAssembly
import all KIP126.ProofTools.GeneralizedMahowald.FSourceActual
import all KIP126.ProofTools.GeneralizedMahowald.FSourceRegrade
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.GeneralizedMahowald.NuCofiberMayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayActual
import all KIP126.ProofTools.GeneralizedMahowald.SphereResidualLabels
import all KIP126.ProofTools.GeneralizedMahowald.SphereMayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.CommonCoordinates
import all KIP126.ProofTools.GeneralizedMahowald.FSourceTransport
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.FTransportLambda
import all KIP126.ProofTools.GeneralizedMahowald.MayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.MinimalSource
import all KIP126.ProofTools.GeneralizedMahowald.CumulativeBoundary
import all KIP126.ProofTools.GeneralizedMahowald.FTransport
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeLabels
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection
import all KIP126.ProofTools.GeneralizedMahowald.Signs
import all KIP126.ProofTools.GeneralizedMahowald.ExtensionImage
import all KIP126.ProofTools.GeneralizedMahowald
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
import all KIP126.ProofTools.Language
import all KIP126.ProofTools.Laws
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.Representatives
import all KIP126.ProofTools.Standard
import all KIP126.ProofTools.Stretching
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.ProofTools.SyntheticProgramRules

public import KIP126.ProofTools.Language
public import KIP126.ProofTools.ConvergenceOperations
public import KIP126.E2Computation.Standard
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions
import all KIP126.ProofTools.Paper.DoublingCrossing
import all KIP126.ProofTools.Paper.DoublingMaximalLift
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta

-- Private bridge reproduced from the independent proof worker.
@[expose] section
namespace KIP126.ProofTools.Paper.DoublingWarning
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

private theorem paper6_10_actual_nonzero_image_pair :
    ∃ a : BiHom 14 17 (S_0_0:SyntheticSpectrum),
      ∃ β : BiHom 14 19 (S_0_0:SyntheticSpectrum),
        a≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 3 17).symm h0h3Square ∧
        β≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 ∧
        shiftHomotopyClass (0,1) (14,17) a≫KIP126.Literature.Standard.syntheticH0=
          lambdaMultiply 1 β := by
  obtain ⟨aPos,βν,haposFirst,hβν,heq⟩ := paper6_8_full_two_representatives
  let E := suspInvarianceAddEquiv 14 17 0 1
    (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
  let aν := E.symm aPos
  have hE (b : BiHom 14 17
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :
      E b=shiftHomotopyClass (0,1) (14,17) b := by
    simp [E,suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,Iso.homCongr]
  have haPos : shiftHomotopyClass (0,1) (14,17) aν=aPos := by
    rw [←hE]
    exact E.apply_symm_apply aPos
  have hsource := shifted_full_source_detects_of_first .sphere 1 3 17 h0h3Square
    h0h3Square_permanent aPos haposFirst
  have haν := shifted_nu_source_first .sphere 1 3 17 (Or.inr rfl) h0h3Square aν (by
    rw [←haPos] at hsource
    convert hsource using 1
    norm_num [homotopyRegrade]
    rfl)
  change aν≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square at haν
  let a : BiHom 14 17 (S_0_0:SyntheticSpectrum) := aν≫model.nu.unitIso.hom
  let β : BiHom 14 19 (S_0_0:SyntheticSpectrum) := βν≫model.nu.unitIso.hom
  have haFirst : a≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square≫
      XModLambdaN.map model.nu.unitIso.hom 1 := by
    dsimp only [a]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,haν]
  have hβFirst : β≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 5 19 h0d0≫
      XModLambdaN.map model.nu.unitIso.hom 1 := by
    dsimp only [β]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hβν]
  refine ⟨a,β,?_,?_,?_⟩
  · apply (KIP126.Literature.sphereFirstQuotient model 3 17).injective
    rw [haFirst,sphere_native_quotient_label]
    exact ((KIP126.Literature.sphereFirstQuotient model 3 17).apply_symm_apply _).symm
  · apply (KIP126.Literature.sphereFirstQuotient model 5 19).injective
    rw [hβFirst,sphere_native_quotient_label]
    exact ((KIP126.Literature.sphereFirstQuotient model 5 19).apply_symm_apply _).symm
  · calc
      _ = (shiftHomotopyClass (0,1) (14,17) aν≫selectedTwoNormalized)≫model.nu.unitIso.hom := by
        rw [selectedTwoNormalized_eq_h0]
        simp only [h0NormalizedMap,shiftHomotopyClass,a,Functor.map_comp,
          Category.assoc,Iso.inv_hom_id,Category.comp_id]
      _ = (aPos≫selectedTwoNormalized)≫model.nu.unitIso.hom := by rw [haPos]
      _ = (lambdaMultiply 1 βν)≫model.nu.unitIso.hom := congrArg (fun z => z≫model.nu.unitIso.hom) heq
      _ = lambdaMultiply 1 β := by simp only [β,lambdaMultiply,Category.assoc]

private theorem actual_h0d0_lift_lambda_nonzero
    (β : BiHom 14 19 (S_0_0:SyntheticSpectrum))
    (hβ : β≫XModLambdaN.incl _ 1=
      (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0) :
    lambdaMultiply 1 β≠0 := by
  let βν : BiHom 14 19
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    β≫model.nu.unitIso.inv
  have hlabel : nativeFirstLabel .sphere 5 19 h0d0≫
      XModLambdaN.map model.nu.unitIso.hom 1=
      (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 := by
    apply (KIP126.Literature.sphereFirstQuotient model 5 19).injective
    rw [sphere_native_quotient_label,LinearEquiv.apply_symm_apply]
  let Q := (model.quotients.functoriality.functor 1).mapIso model.nu.unitIso
  letI : IsIso (XModLambdaN.map model.nu.unitIso.hom 1) := by
    change IsIso Q.hom
    infer_instance
  have hβν : βν≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 5 19 h0d0 := by
    apply (cancel_mono (XModLambdaN.map model.nu.unitIso.hom 1)).mp
    rw [hlabel]
    have hh : (βν≫XModLambdaN.incl _ 1)≫XModLambdaN.map model.nu.unitIso.hom 1=
        β≫XModLambdaN.incl _ 1 := by
      have hn := congrArg (fun z => β≫z≫XModLambdaN.map model.nu.unitIso.hom 1)
        (XModLambdaN.incl_naturality model.nu.unitIso.inv 1)
      simpa only [βν,ClassicalObject.obj,S_0_0,Category.assoc,
        ←model.quotients.functoriality.map_comp,Iso.inv_hom_id,
        model.quotients.functoriality.map_id,Category.comp_id] using hn
    exact hh.trans hβ
  have hβp := first_label_lift_permanent .sphere 5 19 h0d0 βν hβν
  have hdet := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hβp βν hβν
  have hnb : h0d0∉boundaries model .sphere (1+19-18) (5,19) := by
    norm_num only
    rw [KIP126.ProofTools.Internal.KernelClassical.stem14_s5_boundaries_two,
      Submodule.mem_bot]
    exact h0d0_ne_zero
  have hnot := KIP126.ProofTools.Internal.DoublingKernel.nu_detects_not_next_filtration
    .sphere 5 19 18 (by decide) h0d0 hnb (lambdaMultiply 1 βν) hdet
  have hnν : lambdaMultiply 1 βν≠0 := by
    intro hz
    apply hnot
    rw [hz]
    exact Submodule.zero_mem _
  intro hz
  apply hnν
  have hf : lambdaMultiply 1 βν=(lambdaMultiply 1 β)≫model.nu.unitIso.inv := by
    simp only [βν,lambdaMultiply,Category.assoc]
  rw [hf,hz,zero_comp]

private theorem paper6_10_actual_nonzero_image_pair_strong :
    ∃ a : BiHom 14 17 (S_0_0:SyntheticSpectrum),
      ∃ β : BiHom 14 19 (S_0_0:SyntheticSpectrum),
        a≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 3 17).symm h0h3Square ∧
        β≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 ∧
        shiftHomotopyClass (0,1) (14,17) a≫KIP126.Literature.Standard.syntheticH0=
          lambdaMultiply 1 β ∧ lambdaMultiply 1 β≠0 := by
  obtain ⟨a,β,ha,hβ,he⟩ := paper6_10_actual_nonzero_image_pair
  exact ⟨a,β,ha,hβ,he,actual_h0d0_lift_lambda_nonzero β hβ⟩

end
end KIP126.ProofTools.Paper.DoublingWarning
end

/-! Review-only scheme E. These three declarations are not applied to the
production public API. The statement uses only existing public language;
all numerical and normalization helpers remain private implementation. -/
@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The fixed archive generator d_0 in the actual sphere Adams E2 page. -/
@[no_expose] public def d0 : model.classical.sphere.Page 2 (4,18) :=
  KIP126.ProofTools.Paper.NumericalExamples.d0

/-- The actual product of the fixed standard h0 with that d_0. -/
public def h0d0 : model.classical.sphere.Page 2 (5,19) := product h0 d0

/-- Complete fixed multiplication-by-two warning of Example 6.8 and
Remarks 6.9--6.10. Every equality concerns the specified actual map and
labels. In particular the last clause is strict zero in homotopy, not
only a zero infinity-page label. -/
public theorem paper6_8_complete_crossing_warning :
    let f : SphereSpectrum (C := Spectrum) ⟶ SphereSpectrum := 2 • 𝟙 _
    let x : Ambient model .sphere (3,17) :=
      product h0 (model.standardClasses.standardHiSquare 3)
    let e := normalizedExponent model.classicalTower f
    ∃ he : e = 1,
    let F : (SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ⟶
        model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary) := by
      have hef : normalizedExponent model.classicalTower f = 1 := he
      simpa only [hef,Nat.cast_one] using (model.normalizedMap .sphere .sphere f).map
    F = (SyntheticCategory.biShift (0,1)).map model.nu.unitIso.hom ≫
      KIP126.Literature.Standard.syntheticH0 ≫ model.nu.unitIso.inv ∧
    DifferentialAt model .sphere 2 (1,16) (3,17) h4 x ∧
    FiniteExtension model .sphere .sphere f 2 1 1 16 h4
      (KIP126.Literature.Standard.hiProduct 0 4) ∧
    NoCrossingOn model .sphere 2 2 (1,16) ∧
    FiniteNoCrossing model .sphere .sphere f 2 1 1 16 ∧
    InfiniteExtension model .sphere .sphere f 2 3 17 x 0 ∧
    (∃ W : InfiniteExtensionWitness model .sphere .sphere f 1 4 18 d0 h0d0,
      W.Essential) ∧
    InfiniteExtension model .sphere .sphere f 2 3 17 x h0d0 ∧
    InfiniteHasCrossing model .sphere .sphere f 2 3 17 ∧
    (∀ W : InfiniteExtensionWitness model .sphere .sphere f 2 3 17 x h0d0,
      ¬ W.Essential ∧ W.target ≠ 0) ∧
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) h0d0 ∧
    ¬ DifferentialAt model .sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) 0 ∧
    -- A genuine shorter essential extension at the SAME weight 18 as
    -- the long relation, whose source represents lambda times a d0 lift.
    (∃ a : BiHom 14 19 ((SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))),
      ∃ b : BiHom 14 19
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      ∃ source target,
        Detects (model.convergence (.shift (0,(e:ℤ)) (.nu .sphere))) (4,18,19)
          (regradeE2 (by rw [he]; norm_num)
            (model.comparison.nuE2 .sphere e 4 18 0 d0)) a ∧
        a ≫ (model.normalizedMap .sphere .sphere f).map = b ∧
        HasInfinityRepresentative _ 2 (5,19,18)
          (nuWeightLabel model .sphere 5 19 18 (by decide) h0d0) target ∧
        TowerEssentialExtension (F := model.family) (P := model.syntheticTower)
          (cx := model.convergence (.shift (0,(e:ℤ)) (.nu .sphere)))
          (cy := model.convergence (.nu .sphere))
          (model.convergentMap (.shift (0,(e:ℤ)) (.nu .sphere)) (.nu .sphere)
            (model.normalizedMap .sphere .sphere f).map)
          (14,18) 4 1 source target ∧
        ∃ ar : (Subobject.underlying.obj ((model.syntheticTower.filtration
          ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).F
              4 (14,18)) : ModuleCat.{0} ℤ),
          ((model.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).F
              4 (14,18)).arrow ar = lambdaMultiply 1 a ∧
          (model.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).toAssociatedGraded
              4 (14,18) ar =
            (infinityGradedIso (model.convergence (.shift (0,(e:ℤ)) (.nu .sphere)))
              (14,18) 4).hom source) ∧
    -- An actual second source lift and its nonzero-label image. The
    -- factor lambda is explicit at weights 17, 18 and 19.
    (∃ a : BiHom 14 17 (S_0_0 : SyntheticSpectrum),
      ∃ β : BiHom 14 19 (S_0_0 : SyntheticSpectrum),
        a ≫ XModLambdaN.incl _ 1 =
          (KIP126.Literature.sphereFirstQuotient model 3 17).symm x ∧
        β ≫ XModLambdaN.incl _ 1 =
          (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 ∧
        shiftHomotopyClass (0,1) (14,17) a ≫
          KIP126.Literature.Standard.syntheticH0 = lambdaMultiply 1 β ∧
        lambdaMultiply 1 β ≠ 0) ∧
    -- A lift with strictly zero actual image, hence with every finite
    -- lambda division of that same image (the maximal-image assertion).
    (∃ a : BiHom 14 17 (S_0_0 : SyntheticSpectrum),
      a ≫ XModLambdaN.incl _ 1 =
        (KIP126.Literature.sphereFirstQuotient model 3 17).symm x ∧
      shiftHomotopyClass (0,1) (14,17) a ≫
        KIP126.Literature.Standard.syntheticH0 = 0 ∧
      ∀ q : ℕ, ∃ b : BiHom 14 (18+(q:ℤ)) (S_0_0 : SyntheticSpectrum),
        homotopyRegrade rfl (by dsimp; omega) (lambdaMultiply q b) =
          shiftHomotopyClass (0,1) (14,17) a ≫
            KIP126.Literature.Standard.syntheticH0) := by
  -- Final proof is filled from the independently implemented, privately
  -- checked numerical roots, with no new mathematical caller premises.
  dsimp only
  have he : normalizedExponent model.classicalTower
      (2 • 𝟙 (SphereSpectrum (C := Spectrum))) = 1 :=
    KIP126.ProofTools.Paper.DoublingNumericalExtensions.twoMap_exponent
  refine ⟨he, ?_⟩
  obtain ⟨hd2,hfinite,hzero,hshort,hlong,hnotzero⟩ :=
    KIP126.ProofTools.Paper.DoublingNumericalExtensions.paper6_8_crossing_warning
  refine ⟨?_,hd2,hfinite,?_,?_,hzero,hshort,hlong,?_,?_,?_,hnotzero,?_,?_,?_⟩
  · change KIP126.ProofTools.Paper.NuNumericalExtensions.normalizedMapInPositiveCoordinates
      .sphere .sphere KIP126.ProofTools.Paper.DoublingNumericalExtensions.twoMap
      KIP126.ProofTools.Paper.DoublingNumericalExtensions.twoMap_exponent =
        KIP126.ProofTools.Paper.DoublingNumericalExtensions.h0NormalizedMap
    exact KIP126.ProofTools.Paper.DoublingNumericalExtensions.selectedTwoNormalized_eq_positive.symm.trans
      KIP126.ProofTools.Paper.DoublingNumericalExtensions.selectedTwoNormalized_eq_h0
  · refine ⟨by decide,by decide,?_⟩
    rintro ⟨a,b,ha,hab,_⟩
    omega
  · rintro ⟨a,b,ha,hab,_⟩
    omega
  · exact KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_has_paper_crossing
  · intro W
    exact ⟨KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_long_inessential W,
      KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_long_target_nonzero W⟩
  · exact KIP126.ProofTools.Paper.NumericalExamples.paper6_8_classical_d3
  · exact KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_lowered_actual_crossing
  · exact KIP126.ProofTools.Paper.DoublingWarning.paper6_10_actual_nonzero_image_pair_strong
  · obtain ⟨a,ha,hzero,hmax⟩ :=
      KIP126.ProofTools.Paper.DoublingMaximalLift.paper6_10_actual_maximal_zero_image_lift
    refine ⟨a,?_,hzero,hmax⟩
    apply (KIP126.Literature.sphereFirstQuotient model 3 17).injective
    rw [ha,KIP126.ProofTools.Paper.NuNumericalExtensions.sphere_native_quotient_label]
    exact ((KIP126.Literature.sphereFirstQuotient model 3 17).apply_symm_apply _).symm

end
end KIP126.ProofTools.Standard
end

-- The three proposed public roots have no free universe or mathematical
-- premise parameters. Their inherited axioms remain visible in the log.
set_option pp.universes true
#check KIP126.ProofTools.Standard.d0
#check KIP126.ProofTools.Standard.h0d0
#check KIP126.ProofTools.Standard.paper6_8_complete_crossing_warning
#print axioms KIP126.ProofTools.Standard.paper6_8_complete_crossing_warning

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let roots := #[
    `KIP126.ProofTools.Standard.d0,
    `KIP126.ProofTools.Standard.h0d0,
    `KIP126.ProofTools.Standard.paper6_8_complete_crossing_warning]
  for userName in roots do
    let some (root, _) := env.constants.toList.find? (fun (n, _) =>
      ((privateToUserName? n).getD n) == userName && (env.getModuleIdxFor? n).isNone)
      | throwError "missing root {userName}"
    let some info := env.find? root | throwError "root not found"
    logInfo m!"TYPE {userName}, universes {info.levelParams}: {info.type}"
    let axioms ← collectAxioms root
    let mut pending := #[root]
    let mut seen : NameSet := {}
    let mut localHoles : Array Name := #[]
    let mut allHoles : Array Name := #[]
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some info := env.find? n | continue
      let mod := match env.getModuleIdxFor? n with
        | some idx => env.header.moduleNames[idx.toNat]!
        | none => `KIP126.ProofTools.Standard
      unless (`KIP126).isPrefixOf mod do continue
      if n == `KIP126.ProofTools.Paper.finiteCrossing_iff_syntheticCrossing then
        throwError "forbidden original crossing iff used by {userName}"
      let body := info.value? (allowOpaque := true)
      if info.type.hasSorry || body.any (·.hasSorry) then
        allHoles := allHoles.push n
        if (`KIP126.ProofTools).isPrefixOf mod then
          localHoles := localHoles.push n
      pending := pending ++ info.type.getUsedConstants
      if let some value := body then pending := pending ++ value.getUsedConstants
    unless localHoles.isEmpty do
      throwError "local proof gaps for {userName}: {localHoles}"
    logInfo m!"AUDIT {userName}: {seen.size} project+boundary dependencies; axioms={axioms}; visible upstream sites={allHoles}"
