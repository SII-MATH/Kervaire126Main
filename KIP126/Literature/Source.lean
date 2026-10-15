module

public import KIP126.Literature.AdamsSynthetic.Statements

public import KIP126.Literature.AdamsSynthetic.ComparisonTheorems
public import KIP126.Def.AdamsSynthetic.AlgebraRealization.Data
public import KIP126.Literature.Standard.Sphere.ClassFamily

@[expose] public section

/-! Parameterized literature theorems, their source objects and comparison
data. Applications to the fixed Adams/synthetic model are proved in
`Main/Literature/Source/Applications`. -/

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BHS lifting, differential and E∞ theorems with their source hypotheses.
Transport of the realization-kernel theorem to the fixed model is proved
separately in Main. -/
structure SyntheticSourceTheorems where
  lifts : KIP126.Literature.AdamsSynthetic.SyntheticLiftTheorems D
  finite_lift : FiniteLiftCriterion D
  bockstein : BocksteinDifferential D
  /-- BHS A.1(2), retaining the source object's actual convergence conditions. -/
  permanent_lift : ∀ (X : C) (products : CategoryTheory.Limits.HasProductsOfShape ℕ C),
    BHSObjectApplicability products H.unit X → BHSPermanentLiftAt D X
  differentials : DifferentialRigidity D
  eInfty : EInftyComparison D
  /-- BHS cor:tau-surj, before transporting back from completed objects. -/
  filtration_lambda : ∀ (X : C) (products : CategoryTheory.Limits.HasProductsOfShape ℕ C),
    BHSObjectApplicability products H.unit X → BHSFiltrationLambdaAt D X
  e2_weight_vanishing : E2WeightVanishing D
  /-- BHS A.11 (1),(3): both zero regions on every finite page, including E2. -/
  finite_quotient_page_vanishing : FiniteQuotientPageVanishing D


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Xu Cor.1.3, the IWX 62-stem computation and the ordinary low-stem
Hopf detections, with one actual convergence and concrete homotopy maps.
No synthetic or arbitrary-choice strengthening is included. -/
structure ClassicalSourceResults (M : MilnorCooperations H) (S : ClassicalHopfThetaClasses H) : Prop where
  h5Square_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (2,64)
      (Sphere.Internal.hiSquare H M 5)
  theta5_detection : TowerDetection.Detects S.convergence (2,64)
    (Sphere.Internal.hiSquare H M 5) S.theta5
  theta5_order_two : S.theta5 + S.theta5 = 0
  stem62_exponent_two : ∀ a : HomotopyGroup (C := C) 62 SphereSpectrum, a+a=0
  theta5_filtration_gap : ∀ a b : HomotopyGroup (C := C) 62 SphereSpectrum,
    TowerDetection.Detects S.convergence (2,64) (Sphere.Internal.hiSquare H M 5) a →
    TowerDetection.Detects S.convergence (2,64) (Sphere.Internal.hiSquare H M 5) b →
    a-b ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 6 62
  two_detection : TowerDetection.Detects S.convergence (1,1) (Sphere.Internal.hi H M 0)
    ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _))
  eta_detection : TowerDetection.Detects S.convergence (1,2) (Sphere.Internal.hi H M 1) S.eta
  nu_detection : TowerDetection.Detects S.convergence (1,4) (Sphere.Internal.hi H M 2) S.nu
  eta_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (1,2) (Sphere.Internal.hi H M 1)
  nu_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (1,4) (Sphere.Internal.hi H M 2)

def ClassicalSourceExistence (H : Mod2EilenbergMacLane (C := C))
    (M : MilnorCooperations H) : Prop :=
  ∃ S : ClassicalHopfThetaClasses H, ClassicalSourceResults M S

variable {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]


end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Synthetic.Context
universe u v
variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- May's push-pull theorem for the specified tensor and suspension
conventions on the synthetic category. -/
def MaySourceResults (B : MayContext Syn) : Prop :=
  ∀ T U : HoCofiberSequence (C := Syn), Nonempty (MayPushpullData Syn B T U)


end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BHS `prop:syn-toda-range`, low-ring/label consequences on the selected
sphere. These equations do not prove a secondary Toda membership. -/
structure TodaSourceResults (η : BiHom 1 2 (S_0_0 : Syn))
    (S : SyntheticH0Class (Syn := Syn)) : Prop where
  h0_label : D.sphereFirstQuotient 1 1 (quotientClass 1 S.h0) = Sphere.Internal.hi H M 0
  lambda_h0 : lambdaMultiply 1 S.h0 = syntheticTwo
  h0_eta : sphereProduct S.h0 η = 0
  low_indeterminacy : ∀ a : BiHom 2 3 (S_0_0 : Syn), sphereProduct S.h0 a = 0


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- BHS A.1(2a),(2b),(3a),(3b) on a specified source object and its
classical convergence. The hypotheses appear in `BHSRealizationSourceResults`. -/
structure BHSRealizationDetectionAt (R : RealizationCoordinates D) (X : C)
    (convergence : TowerDetection.Convergence H.unit X) : Prop where
  /-- BHS A.1(2a): nonzero survival to E_(r+1) controls the lifetime
  of EVERY lift of a permanent cycle. The exponent is r-1, not r. -/
  lifetime : ∀ (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : E2 H X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X))),
    x ∈ PageRepresentatives.permanentCycles H X (s,t) →
    SurvivesTo (adamsTowerInternalSpectralSequence H.unit X)
      (r+1) (s,t) x → quotientClass 1 a = bhsFirstLabel D X s t x →
    lambdaMultiply (r-1) a ≠ 0
  detection : ∀ (s t : ℤ)
    (x : E2 H X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X))),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit X)
      (s,t) x → quotientClass 1 a = bhsFirstLabel D X s t x →
    TowerDetection.Detects convergence (s,t) x (realizeNuZeroObject D R X a)
  prescribed_lift : ∀ (s t : ℤ)
    (x : E2 H X s t) (α : HomotopyGroup (t-s) X),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit X)
      (s,t) x → TowerDetection.Detects convergence (s,t) x α →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel D X s t x ∧ realizeNuZeroObject D R X a = α
  /-- BHS A.1(3a): only SOME lift of a permanent boundary is torsion.
  It would be wrong to demand this of every lift. -/
  boundary_lift : ∀ (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ (y : E2 H X s t),
    y ∈ PageRepresentatives.permanentCycles H X (s,t) →
    HitOnPage (adamsTowerInternalSpectralSequence H.unit X) r (s,t) y →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel D X s t y ∧ lambdaMultiply (r-1) a = 0

/-- The completed-source BHS theorem. No assertion is made here for an
uncompleted selected X; the actual source hypotheses must be supplied. -/
def BHSRealizationSourceResults (R : RealizationCoordinates D) : Prop :=
  ∀ (X : C) (products : CategoryTheory.Limits.HasProductsOfShape ℕ C),
    BHSObjectApplicability products H.unit X →
    ∀ convergence : TowerDetection.Convergence H.unit X,
      BHSRealizationDetectionAt D R X convergence


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable (Syn : Type w) [SyntheticCategory.{w, v} Syn]

variable {Syn}

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- The kernel of λ-localization consists of λ-power torsion, for the images
of the specified synthetic objects in the full source category. The source
theorem uses telescope localization and compactness of the source spheres. -/
def RealizationKernelSourceResults (S : SyntheticCompletionAdjunction Syn) : Prop :=
  ∀ (X : SyntheticObject) (m w : ℤ)
    (a : BiHom m w (S.inclusion.obj (X.obj D.nu D.hopfAndDetector))),
    (S.localization.endofunctor.map a = 0 ↔ ∃ k : ℕ, lambdaMultiply k a = 0)


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- BMQ v4 (2021), Figure 1.1, §2 and §7, after the explicitly separate
2-local-to-2-complete transport. In §7 the nonzero class is the image of
the actual product kappaBar^4*w. The stronger universal statement about
ALL classes detected by g^4 Delta h1 g is deliberately absent. -/
structure TmfSourceResults (S : TmfDetectionData H) : Prop where
  /-- The source is connective tmf with degreewise finite mod-2 homology.
  These are the scope facts needed for BHS completion/convergence after
  transport; local values in stems 62/125 alone would not imply them. -/
  connective : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n S.spectrum)
  finiteMod2Type : FiniteMod2Type H S.spectrum
  standard_labels : S.labels.Standard
  vanishing62 : ∀ x : HomotopyGroup (C := C) 62 S.spectrum, x = 0
  low_filtration63 : ∀ s : ℤ, s ≤ 0 → Subsingleton (E2 H S.spectrum s (63+s))
  kappaBar_detection : TowerDetection.Detects S.sphereConvergence (4,24)
    S.labels.g S.kappaBar
  w_detection : TowerDetection.Detects S.sphereConvergence (9,54)
    S.labels.delta_h_1_mul_g S.wClass
  high125_nonzero : S.high125 ≫ S.unit ≠ 0

/-- Existence of completed tmf source data satisfying the BMQ/IWX results.
Application to a given Adams/synthetic model requires `TmfDetectorComparison`, which
identifies the detector, its unit and its distinguished classes with these
source data. -/
def TmfSourceExistence (H : Mod2EilenbergMacLane (C := C)) : Prop :=
  ∃ S : TmfDetectionData H, TmfSourceResults S


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- Compatibility of the three normalized lifts for the cofiber of ν,
including their exponents, distinguished triangle and h₂ label. Main proves
this using Pstrągowski Lemma 4.23, BHS Lemma 9.15, Hopf detection and the
first-quotient comparison. -/
structure NuCofiberSourceResults (S : NuCofiberLifts D) : Prop where
  nu_exponent : normalizedExponent H D.hopfAndDetector.nuMap = 1
  bottom_exponent : normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g = 0
  top_exponent : normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.h = 0
  normalized_label :
    D.sphereFirstQuotient 1 4 (quotientClass 1 (sourceNormalizedNu D S nu_exponent)) =
      Sphere.Internal.hi H M 2
  triangle : ∀ he, sourceNormalizedTriangle D S he ∈ distTriang Syn

/-- Existence of compatible normalized lifts for the cofiber of ν.
Main proves this from the separate Pstrągowski/BHS hypotheses and then
compares these lifts with the normalized maps of `D`. -/
def NuCofiberSourceExistence : Prop :=
  ∃ S : NuCofiberLifts D, NuCofiberSourceResults D S


end
end KIP126.Literature.AdamsSynthetic

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn) (η : BiHom 1 2 (S_0_0 : Syn)) (L : TmfDetectionClasses H)

/-- Source objects and comparisons for one Adams/synthetic model: classical
Hopf classes, Toda data, tmf, BHS completion and the cofiber of ν.
Each comparison refers to the same specified source objects. -/
structure SourceComparisons (background : AlgebraRealizationComparison D) where
  todaSource : SyntheticH0Class (Syn := Syn)
  kernelSource : SyntheticCompletionAdjunction Syn
  kernelComparison : RealizationKernelComparison D kernelSource
  classicalSource : ClassicalHopfThetaClasses H
  hopfComparison : ClassicalHopfComparison D η classicalSource
  synthetic_eta : EtaChoice M D.toAdamsComparisonData η
  tmfSource : TmfDetectionData H
  tmfComparison : TmfDetectorComparison D L tmfSource
  bhsCompletion : BHSCompletionData D
  /-- Truth of the source hypotheses and of the transport along this same completion. -/
  completionApplicability : BHSCompletionApplicability D bhsCompletion
  completionComparison : BHSCompletionComparison D bhsCompletion
  realizationComparison : BHSRealizationComparison D background.realization bhsCompletion
  /-- The completion source for the detector is the SAME completed tmf,
  and its comparison carries the SAME actual ring unit. -/
  bhsDetectorIso : bhsCompletion.completed .detector ≅ tmfSource.spectrum
  bhsDetectorUnit : D.hopfAndDetector.detectorUnit ≫ bhsCompletion.map .detector ≫
    bhsDetectorIso.hom = tmfSource.unit
  nuSource : NuCofiberLifts D
  nuCofiberComparison : NuCofiberLiftComparison D nuSource

namespace SourceComparisons
variable {D η L} {background : AlgebraRealizationComparison D}
abbrev realization (_B : SourceComparisons D η L background) := background.realization
abbrev algebra (_B : SourceComparisons D η L background) := background.algebra
abbrev quotientCompatibility (_B : SourceComparisons D η L background) := background.quotientCompatibility
abbrev algebraDetectionCompatibility (_B : SourceComparisons D η L background) := background.algebraDetectionCompatibility
abbrev may (_B : SourceComparisons D η L background) := background.may
abbrev realizationAdditive (_B : SourceComparisons D η L background) := background.realizationAdditive
abbrev weights (_B : SourceComparisons D η L background) := background.weights
abbrev nuE2 (_B : SourceComparisons D η L background) := background.nuE2
end SourceComparisons

/-- The literature theorems on the source objects specified by `B`.
Applications to the objects of `D` use the comparisons recorded in `B`. -/
structure SourceTheorems {background : AlgebraRealizationComparison D} (B : SourceComparisons D η L background) where
  classical : ClassicalSourceResults M B.classicalSource
  bx : BXDistinguishedThetaTheorem D η
  synthetic : SyntheticSourceTheorems D
  realizationKernel : RealizationKernelSourceResults D B.kernelSource
  realization : BHSRealizationSourceResults D B.realization
  may : MaySourceResults Syn B.may
  toda : TodaSourceResults D η B.todaSource
  tmf : TmfSourceResults B.tmfSource


end KIP126.Literature.AdamsSynthetic

namespace KIP126.ExternalHypotheses
open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams SpectralSequence
universe u v w

section Moss

open StableHomotopy StableHomotopy.Cohomology Classical.Adams.Moss

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]
  [∀ A : C, (tensorLeft A).CommShift ℤ]

/-- Moss convergence for the specified family of mapping Adams spectral
sequences, with composition, detection and Massey indeterminacy comparisons.
This general structure is separate from the fixed Section 7 hypotheses. -/
structure MossConvergenceData {ι : Type w} (objects : ι → C) where
  composition : CompositionPairing H R
  coherent : composition.Coherent H R
  convergence : ∀ X Y : ι, MappingAdamsConvergence H.unit (objects X) (objects Y)
  weak_convergence : ∀ X Y : ι, MappingAdamsTower H.unit (objects X) (objects Y)
  detection : ∀ X Y Z : ι,
    composition.DetectionCompatible H R (objects X) (objects Y) (objects Z)
      (convergence X Y) (convergence Y Z) (convergence X Z)
  indeterminacy : ∀ (r : ℤ) (hr : 3 ≤ r) (W X Y Z : ι) (i j k : ℤ × ℤ)
    (a : (mappingSequence H.unit (objects W) (objects X)).Page r i)
    (b : (mappingSequence H.unit (objects X) (objects Y)).Page r j)
    (c : (mappingSequence H.unit (objects Y) (objects Z)).Page r k)
    (x₀ x : (mappingSequence H.unit (objects W) (objects Z)).Page r
      (PageMassey.degree r i j k)),
    PageMassey.Relation H R composition r hr x₀ a b c →
      (PageMassey.Relation H R composition r hr x a b c ↔
        PageMassey.Indeterminacy H R composition r (j := j) a c (x - x₀))
  moss : Classical.Adams.Moss.Statement H R composition objects convergence


end Moss

end KIP126.ExternalHypotheses
