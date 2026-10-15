module

public import KIP126.Literature.AdamsSynthetic.Statements

public import KIP126.Literature.Source
public import KIP126.Literature.Standard.AlgebraRealization
public import KIP126.Literature.Standard.Sphere.EInfty
public import KIP126.Literature.Tmf.Br21.Classes

@[expose] public section

/-! The cited literature results and their precise hypotheses on the fixed
Adams/synthetic background. Source objects, distinguished classes and
comparison isomorphisms are specified before the theorems that use them. -/
namespace KIP126.ExternalHypotheses
open CategoryTheory Classical.Adams SpectralSequence
open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open Literature.AdamsSynthetic Classical.Adams.PageRepresentatives AdamsSynthetic Synthetic
set_option autoImplicit false

/-- The literature source objects and their comparisons with the fixed
Adams/synthetic model, including tmf classes and E∞ descriptions. -/
structure LiteratureSources where
  tmfLabels : Literature.AdamsSynthetic.TmfDetectionClasses standardFoundation.hf2
  sourceComparisons : Literature.AdamsSynthetic.SourceComparisons standardAdamsComparison Def.standardEta
    tmfLabels Def.standardAdamsSyntheticComparisons
  br21Classes : Tmf.Br21Classes standardFoundation.hf2 sourceComparisons.tmfSource.spectrum
  eInfty_nu : NuEInftyFormula standardFoundation.hf2 standardAdamsComparison.nu standardAdamsComparison.family
  eInfty_quotient : FiniteEInftyFormula standardFoundation.hf2 standardAdamsComparison.nu standardAdamsComparison.family
  eInfty_specialFiber : ∀ (X : standardFoundation.Spectrum) (p : ℤ × ℤ) (w : ℤ),
    ((standardAdamsComparison.family.nuQuotient standardAdamsComparison.nu X 1).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      finiteEInftyModel standardFoundation.hf2 X 1 p w

namespace LiteratureSources

/-- The ν, finite λ-quotient and special-fiber E∞ descriptions on these sources. -/
noncomputable def eInftyPresentation (sources : LiteratureSources) :
    EInftyPresentation standardAdamsComparison where
  nu := sources.eInfty_nu
  quotient := sources.eInfty_quotient
  specialFiber := sources.eInfty_specialFiber

/-- The weight-shift comparison induced by the fixed Adams tower construction. -/
noncomputable def eInftyWeightShift (_sources : LiteratureSources) :
    EInftyWeightShift standardAdamsComparison.family :=
  Def.standardEInftyWeightShift

end LiteratureSources

/-- Cited theorems on these specified source objects: classical detections,
synthetic lifting and realization, and tmf calculations. Main transports
these results along the comparisons in `sources`. -/
structure LiteratureTheorems (sources : LiteratureSources) : Prop where
  /-- BR21 Table 5.4 / Theorem 5.18 on the source endpoint classes.
  This asserts only the differential equation, with no extra survival claim. -/
  br21 : HasDifferential
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
      sources.sourceComparisons.tmfSource.spectrum) 3 (16, 112) (19, 114)
    sources.br21Classes.v2Sixteen sources.br21Classes.betaGFour
  sphereVanishing : SphereVanishingLine standardFoundation.hf2
  adamsOneLine_d2 (j : ℕ) (hj : 4 ≤ j) :
      HasNonzeroDifferential sphereAdamsData 2
        (1, ((2 ^ j : ℕ) : ℤ)) (3, ((1 + 2 ^ (j - 1 + 1) : ℕ) : ℤ))
        (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations j)
        (Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations (j - 1))
  classical_h5Square_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum) (2,64)
      (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5)
  classical_theta5_detection : TowerDetection.Detects sources.sourceComparisons.classicalSource.convergence (2,64)
    (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5) sources.sourceComparisons.classicalSource.theta5
  classical_theta5_order_two : sources.sourceComparisons.classicalSource.theta5 + sources.sourceComparisons.classicalSource.theta5 = 0
  classical_stem62_exponent_two : ∀ a : HomotopyGroup (C := standardFoundation.Spectrum) 62 SphereSpectrum, a+a=0
  classical_theta5_filtration_gap : ∀ a b : HomotopyGroup (C := standardFoundation.Spectrum) 62 SphereSpectrum,
    TowerDetection.Detects sources.sourceComparisons.classicalSource.convergence (2,64) (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5) a →
    TowerDetection.Detects sources.sourceComparisons.classicalSource.convergence (2,64) (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5) b →
    a-b ∈ TowerDetection.filtrationSubmodule standardFoundation.hf2.unit SphereSpectrum 6 62
  classical_two_detection : TowerDetection.Detects sources.sourceComparisons.classicalSource.convergence (1,1) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 0)
    ((shiftFunctorZero standardFoundation.Spectrum ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _))
  classical_eta_detection : TowerDetection.Detects sources.sourceComparisons.classicalSource.convergence (1,2) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 1) sources.sourceComparisons.classicalSource.eta
  classical_nu_detection : TowerDetection.Detects sources.sourceComparisons.classicalSource.convergence (1,4) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 2) sources.sourceComparisons.classicalSource.nu
  classical_eta_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum) (1,2) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 1)
  classical_nu_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum) (1,4) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 2)
  bxTheta : BXDistinguishedThetaTheorem standardAdamsComparison Def.standardEta
  realizationKernel : RealizationKernelSourceResults standardAdamsComparison sources.sourceComparisons.kernelSource
  mayPushpull : MaySourceResults Def.standardSyntheticContext.Syn sources.sourceComparisons.may
  synthetic_nu_cofiber : NuCofiberCriterion standardFoundation.hf2 standardAdamsComparison.nu
  synthetic_lift : SyntheticLiftComparison standardFoundation.hf2 standardAdamsComparison.nu
  synthetic_triangle_lift : SyntheticTriangleLiftComparison standardFoundation.hf2 standardAdamsComparison.nu
  synthetic_finite_lift : FiniteLiftCriterion standardAdamsComparison
  synthetic_bockstein : BocksteinDifferential standardAdamsComparison
  synthetic_permanent_lift : ∀ (X : standardFoundation.Spectrum) (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X → BHSPermanentLiftAt standardAdamsComparison X
  synthetic_differentials : DifferentialRigidity standardAdamsComparison
  synthetic_filtration_lambda : ∀ (X : standardFoundation.Spectrum) (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X → BHSFiltrationLambdaAt standardAdamsComparison X
  synthetic_e2_weight_vanishing : E2WeightVanishing standardAdamsComparison
  synthetic_finite_quotient_page_vanishing : FiniteQuotientPageVanishing standardAdamsComparison
  eInfty_lambda_nu : ∀ (X : standardFoundation.Spectrum) (k : ℕ) (p : ℤ × ℤ) (w : ℤ) (hw : w ≤ p.2)
    (x : ((standardAdamsComparison.family.nu standardAdamsComparison.nu X).sequence.ssData (p.1, p.2, w)).eInfty),
    sources.eInftyPresentation.nuWindow X p (w - k) (by omega) (sources.eInftyWeightShift.lambdaMap (standardAdamsComparison.nu.functor.obj X) k p w x) =
      permanentQuotientMap standardFoundation.hf2 X (by omega) p (sources.eInftyPresentation.nuWindow X p w hw x)
  eInfty_lambda_finite : ∀ (X : standardFoundation.Spectrum) (q k : ℕ) (hkq : k < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < (q - k : ℕ))
    (x : ((standardAdamsComparison.family.nuQuotient standardAdamsComparison.nu X (q - k)).sequence.ssData (p.1, p.2, w)).eInfty),
    sources.eInftyPresentation.finiteWindow X q (by omega) p (w - k) (by constructor <;> omega)
        (sources.eInftyWeightShift.finiteLambdaMap (standardAdamsComparison.quotientTower (standardAdamsComparison.nu.functor.obj X)) q k hkq p w x) =
      quotientMap standardFoundation.hf2 X (by omega) (by omega) p
        (sources.eInftyPresentation.finiteWindow X (q - k) (by omega) p w hw x)
  eInfty_rho_finite : ∀ (X : standardFoundation.Spectrum) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
    (p : ℤ × ℤ) (w : ℤ) (hw : 0 ≤ p.2 - w ∧ p.2 - w < i)
    (x : ((standardAdamsComparison.family.nuQuotient standardAdamsComparison.nu X j).sequence.ssData (p.1, p.2, w)).eInfty),
    sources.eInftyPresentation.finiteWindow X i hi p w hw
        (((standardAdamsComparison.family.functor.map ((standardAdamsComparison.quotientTower (standardAdamsComparison.nu.functor.obj X)).rho i j hij)).eInftyMap (p.1, p.2, w)).hom x) =
      quotientMap standardFoundation.hf2 X (by omega) (le_refl (1 + p.2 - w)) p
        (sources.eInftyPresentation.finiteWindow X j (by omega) p w (by constructor <;> omega) x)
  eInfty_rho_nu : ∀ (X : standardFoundation.Spectrum) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < q)
    (x : ((standardAdamsComparison.family.nu standardAdamsComparison.nu X).sequence.ssData (p.1, p.2, w)).eInfty),
    sources.eInftyPresentation.finiteWindow X q hq p w hw
        (((standardAdamsComparison.family.quotientProjection (standardAdamsComparison.nu.functor.obj X) q).eInftyMap (p.1, p.2, w)).hom x) =
      permanentToFinite standardFoundation.hf2 X (q - p.2 + w) (1 + p.2 - w) p
        (sources.eInftyPresentation.nuWindow X p w (by omega) x)
  eInfty_labels : Literature.AdamsSynthetic.EInftyLabelAgreement standardAdamsComparison sources.eInftyPresentation
  realization_lifetime : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ _convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : E2 standardFoundation.hf2 X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardAdamsComparison.nu.functor.obj X))),
    x ∈ PageRepresentatives.permanentCycles standardFoundation.hf2 X (s,t) →
    SurvivesTo (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X)
      (r+1) (s,t) x → quotientClass 1 a = bhsFirstLabel standardAdamsComparison X s t x →
    lambdaMultiply (r-1) a ≠ 0
  realization_detection : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ)
    (x : E2 standardFoundation.hf2 X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardAdamsComparison.nu.functor.obj X))),
    NonzeroSurvival (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X)
      (s,t) x → quotientClass 1 a = bhsFirstLabel standardAdamsComparison X s t x →
    TowerDetection.Detects convergence (s,t) x (realizeNuZeroObject standardAdamsComparison sources.sourceComparisons.realization X a)
  realization_prescribed_lift : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ)
    (x : E2 standardFoundation.hf2 X s t) (α : HomotopyGroup (t-s) X),
    NonzeroSurvival (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X)
      (s,t) x → TowerDetection.Detects convergence (s,t) x α →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardAdamsComparison.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel standardAdamsComparison X s t x ∧ realizeNuZeroObject standardAdamsComparison sources.sourceComparisons.realization X a = α
  realization_boundary_lift : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ _convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ (y : E2 standardFoundation.hf2 X s t),
    y ∈ PageRepresentatives.permanentCycles standardFoundation.hf2 X (s,t) →
    HitOnPage (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X) r (s,t) y →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardAdamsComparison.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel standardAdamsComparison X s t y ∧ lambdaMultiply (r-1) a = 0
  toda_h0_label : standardAdamsComparison.sphereFirstQuotient 1 1 (quotientClass 1 sources.sourceComparisons.todaSource.h0) = Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 0
  toda_lambda_h0 : lambdaMultiply 1 sources.sourceComparisons.todaSource.h0 = syntheticTwo
  toda_h0_eta : sphereProduct sources.sourceComparisons.todaSource.h0 Def.standardEta = 0
  toda_low_indeterminacy : ∀ a : BiHom 2 3 (S_0_0 : Def.standardSyntheticContext.Syn), sphereProduct sources.sourceComparisons.todaSource.h0 a = 0
  tmf_connective : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n sources.sourceComparisons.tmfSource.spectrum)
  tmf_finiteMod2Type : FiniteMod2Type standardFoundation.hf2 sources.sourceComparisons.tmfSource.spectrum
  tmf_standard_labels : sources.sourceComparisons.tmfSource.labels.Standard
  tmf_vanishing62 : ∀ x : HomotopyGroup (C := standardFoundation.Spectrum) 62 sources.sourceComparisons.tmfSource.spectrum, x = 0
  tmf_low_filtration63 : ∀ s : ℤ, s ≤ 0 → Subsingleton (E2 standardFoundation.hf2 sources.sourceComparisons.tmfSource.spectrum s (63+s))
  tmf_kappaBar_detection : TowerDetection.Detects sources.sourceComparisons.tmfSource.sphereConvergence (4,24)
    sources.sourceComparisons.tmfSource.labels.g sources.sourceComparisons.tmfSource.kappaBar
  tmf_w_detection : TowerDetection.Detects sources.sourceComparisons.tmfSource.sphereConvergence (9,54)
    sources.sourceComparisons.tmfSource.labels.delta_h_1_mul_g sources.sourceComparisons.tmfSource.wClass
  tmf_high125_nonzero : sources.sourceComparisons.tmfSource.high125 ≫ sources.sourceComparisons.tmfSource.unit ≠ 0

/-- The literature hypotheses: specified sources and comparisons, together
with the cited theorems on those same sources. -/
structure LiteratureHypotheses where
  sources : LiteratureSources
  theorems : LiteratureTheorems sources

end KIP126.ExternalHypotheses
