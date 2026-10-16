module

public import KIP126.AdamsSynthetic.Standard.Background
public import KIP126.Literature.Delivery
import all KIP126.Literature.Delivery
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Triangles
import all KIP126.Literature.May

/-! Fixed literature objects and directly callable source theorems.

Each admitted declaration below is a separate, tracked source or comparison
obligation. No result package is required from consumers. Generic definitions
and established proofs are reused internally. Mathematical range, projectivity,
completeness and detection conditions are retained in their original statements.
Sources remain those recorded in metadata/literature-sources.json; the fixed upstream
review is bbac1fc05843bdf2d56057e6114a38839e939378 (Apache-2.0).
-/

@[expose] section
set_option autoImplicit false
noncomputable section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)

/-- Source or comparison proof remains to be supplied. -/
public theorem sphere_connected :
  IsConnected (SphereSpectrum (C := Spectrum)) (-1) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem connected_homology_vanishing :
  ∀ (X : Spectrum) (n : ℤ), IsConnected X n →
    ∀ i : ℤ, i ≤ n → Subsingleton (ModTwoHomology model.coefficients i X) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def universal_coefficient :
  ∀ (n : ℤ) (X : Spectrum),
    ModTwoCohomology model n X ≃+ (ModTwoHomology model.coefficients (-n) X →+ ZMod 2) := by
  sorry

/-- The specified realization is additive by its actual adjunction.
The same argument occurs in Kervaire126 8cb35dad5,
Main/Solution/StageInput/Toda/Low.lean:254–258. -/
public theorem realization_additive :
  model.recovery.realization.Additive := by
  letI := model.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    model.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The fixed mathematical object on the project background. -/
public def realization_sphere :
  ∀ m w : ℤ, Sphere (C := Spectrum) m ≅ model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m w) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem realization_unit :
  (realization_sphere 0 0).hom ≫ model.recovery.realization.map
      (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum)) =
    (shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫
      model.recovery.nuRealizationIso.inv.app SphereSpectrum ≫
      model.recovery.realization.map model.nu.unitIso.hom := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem realization_lambda :
  ∀ (m w : ℤ) (k : ℕ),
    (realization_sphere m (w-k)).hom ≫
      model.recovery.realization.map (lambdaMultiply k (𝟙 (Smn (Syn := SyntheticSpectrum) m w))) =
        (realization_sphere m w).hom := by
  sorry

public def realizationData : RealizationCoordinates model where
  additive := realization_additive
  sphere := realization_sphere
  unit := realization_unit
  lambda := realization_lambda

public def realizeSphere := RealizationCoordinates.sphereMap model realizationData

/-- The fixed mathematical object on the project background. -/
public def tmf :
  Spectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmfIso :
  tmf ≅ model.auxiliary.detector := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmfUnit :
  SphereSpectrum ⟶ tmf := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmfUnit_agrees :
  tmfUnit ≫ tmfIso.hom = model.auxiliary.detectorUnit := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def g :
  model.classical.sphere.Page 2 (4,24) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def deltaH1g :
  model.classical.sphere.Page 2 (9,54) := by
  sorry

private def tmfBindingData : TmfBindings model where
  source := tmf
  sourceIso := tmfIso
  sourceUnit := tmfUnit
  unit_agrees := tmfUnit_agrees
  g := g
  deltaH1g := deltaH1g

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_exponent :
  normalizedExponent model.classicalTower model.auxiliary.etaMap = 1 := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public def eta :
  BiHom 1 2 (S_0_0 : SyntheticSpectrum) := (etaSourceIso model eta_exponent).hom ≫
    (model.normalizedMap (.shift 1 .sphere) .sphere model.auxiliary.etaMap).map ≫ model.nu.unitIso.hom

/-- Derived from the fixed objects and previously established operations. -/
public theorem eta_normalized :
  eta = (etaSourceIso model eta_exponent).hom ≫
    (model.normalizedMap (.shift 1 .sphere) .sphere model.auxiliary.etaMap).map ≫ model.nu.unitIso.hom := rfl

/-- The fixed mathematical object on the project background. -/
public def theta5 :
  HomotopyGroup (C := Spectrum) 62 SphereSpectrum := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem h5Square_permanent :
  NonzeroSurvival model.classical.sphere (2,64)
    (model.standardClasses.standardHiSquare 5) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem theta5_detection :
  ClassicalTheta5Detected model theta5 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum, a+a=0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem theta5_filtration_gap :
  ∀ a b, ClassicalTheta5Detected model a → ClassicalTheta5Detected model b →
    a-b ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule 6 62 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (1,2)
    (model.standardClasses.standardHi 1) model.auxiliary.etaMap := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nu_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (1,4)
    (model.standardClasses.standardHi 2) model.auxiliary.nuMap := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_permanent :
  NonzeroSurvival model.classical.sphere (1,2) (model.standardClasses.standardHi 1) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nu_permanent :
  NonzeroSurvival model.classical.sphere (1,4) (model.standardClasses.standardHi 2) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_label :
  sphereFirstQuotient model 1 2 (quotientClass 1 eta) = model.standardClasses.standardHi 1 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_realization :
  realizeSphere 1 2 eta = model.auxiliary.etaMap := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem theta5_lift :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum),
    Theta5Detected model a ∧ realizeSphere 62 64 a = theta5 := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem theta5_order_two :
  theta5 + theta5 = 0 := stem62_exponent_two theta5

/-- Derived from the fixed objects and previously established operations. -/
public theorem theta5_detected_exists :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum), Theta5Detected model a := by
  obtain ⟨a, ha, _⟩ := theta5_lift
  exact ⟨a, ha⟩

/-- Source or comparison proof remains to be supplied. -/
public theorem sphereVanishing :
  SphereVanishingLine model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem two_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (1,1)
    (model.standardClasses.standardHi 0) (classicalTwo (C := Spectrum)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem adamsOneLine_d2 :
  ∀ (j : ℕ), 4 ≤ j →
    HasNonzeroDifferential model.classical.sphere 2
      (1,((2^j : ℕ) : ℤ)) (3,1+((2^(j-1+1) : ℕ) : ℤ))
      (model.standardClasses.standardHi j) (oneLineTarget model j) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmf_algebra :
  MonObj tmf := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_algebra_unit :
  tmf_algebra.one = tmfUnit := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmf_convergence :
  ClassicalTowerConvergence model.classicalTower tmf := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def kappaBar :
  HomotopyGroup (C := Spectrum) 20 SphereSpectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def wClass :
  HomotopyGroup (C := Spectrum) 45 SphereSpectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmfV2Sixteen :
  (model.classical.obj tmf).Page 2 (16,112) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmfBetaGFour :
  (model.classical.obj tmf).Page 2 (19,114) := by
  sorry

private def tmfSourceData : TmfSourceData model tmfBindingData where
  algebra := tmf_algebra
  algebra_unit := tmf_algebra_unit
  convergence := tmf_convergence
  kappaBar := kappaBar
  wClass := wClass
  v2Sixteen := tmfV2Sixteen
  betaGFour := tmfBetaGFour

public def high125 := classicalSphereProduct
  (classicalSphereProduct (classicalSphereProduct kappaBar kappaBar)
    (classicalSphereProduct kappaBar kappaBar)) wClass

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_connective :
  ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n tmf) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_finiteModTwoType :
  ∀ n : ℤ, Finite (ModTwoHomology model.coefficients n tmf) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem g_nonzero :
  g ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem g_unique :
  ∀ x : model.classical.sphere.Page 2 (4,24), x ≠ 0 → x = g := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem deltaH1g_nonzero :
  deltaH1g ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem deltaH1g_unique :
  ∀ x : model.classical.sphere.Page 2 (9,54), x ≠ 0 → x = deltaH1g := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_vanishing62 :
  ∀ x : HomotopyGroup (C := Spectrum) 62 tmf, x = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_low_filtration63 :
  ∀ s : ℤ, s ≤ 0 →
    Subsingleton ((model.classical.obj tmf).Page 2 (s,63+s)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem kappaBar_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (4,24) g kappaBar := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem w_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (9,54) deltaH1g wClass := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_high125_nonzero :
  high125 ≫ tmfUnit ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_br21 :
  HasDifferential (model.classical.obj tmf) 3 (16,112) (19,114)
    tmfV2Sixteen tmfBetaGFour := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem detector_d3 :
  HasDifferential (model.classical.obj model.auxiliary.detector) 3 (16,112) (19,114)
    ((model.classical.map tmfIso.hom).pageMap 2 (16,112) tmfV2Sixteen)
    ((model.classical.map tmfIso.hom).pageMap 2 (19,114) tmfBetaGFour) := (model.classical.map tmfIso.hom).hasDifferential tmf_br21

/-- The fixed mathematical object on the project background. -/
public def nuPage_weightShift :
  ∀ (X : ClassicalObject) (r s t w : ℤ),
    (model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w) ≅
      (model.family.obj ((SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).Page r (s,t,w-1) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nuPage_e2 :
  ∀ (X : ClassicalObject) (s t : ℤ) (k : ℕ)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    HEq ((nuPage_weightShift X 2 s t (t-k)).hom (targetNuLabel model X s t k x))
      (model.comparison.nuE2 X (-1) s t k x) := by
  sorry

public def nuPageData : NuPageCoordinates model where
  weightShift := nuPage_weightShift
  e2 := nuPage_e2

public def pageLambda := NuPageCoordinates.lambda model nuPageData

/-- The fixed mathematical object on the project background. -/
public def free_component :
  ∀ (X : ClassicalObject) (r : ℤ) (_hr : 2 ≤ r)
    (s t w : ℤ) (_h : r-2 ≤ t-w),
    (model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w) ≅
      (model.classical.obj (X.obj model.auxiliary)).Page r (s,t) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem free_e2 :
  ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    (free_component X 2 (by omega) s t w (by omega)).hom (nuWeightLabel model X s t w hw x) = x := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem free_lambda :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    pageLambda X r s t w ≫ (free_component X r hr s t (w-1) (by omega)).hom =
      (free_component X r hr s t w h).hom := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem free_differential :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    syntheticDifferential model X r s t w ≫
        (free_component X r hr (s+r) (t+r-1) w (by omega)).hom =
      (free_component X r hr s t w h).hom ≫ classicalDifferential model X r s t := by
  sorry

public def freeData : FreeLambdaPages model nuPageData where
  component := free_component
  e2 := free_e2
  lambda := free_lambda
  differential := free_differential

public def classicalLift := FreeLambdaPages.classicalLift model freeData

public abbrev classicalLift_differential := FreeLambdaPages.classicalLift_differential model freeData

public abbrev classicalLift_lambda := FreeLambdaPages.classicalLift_lambda model freeData

/-- The fixed mathematical object on the project background. -/
public def inversion_data :
  ∀ X : ClassicalObject,
    SSDataMorphism Tridegree
      (model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (fun i => (model.classical.obj (X.obj model.auxiliary)).ssData (i.1,i.2.1)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem inversion_e2 :
  ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    comparisonPageMap model X (inversion_data X) 2 s t w (nuWeightLabel model X s t w hw x) = x := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem inversion_differential :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun s t => comparisonPageMap model X (inversion_data X) r s t w
    syntheticDifferential model X r s t w ≫ map (s+r) (t+r-1) =
      map s t ≫ classicalDifferential model X r s t := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem inversion_lambda :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun w => comparisonPageMap model X (inversion_data X) r s t w
    pageLambda X r s t w ≫ map (w-1) = map w := by
  sorry

public def inversionData : LambdaInversionComparison model nuPageData where
  data := inversion_data
  e2 := inversion_e2
  differential := inversion_differential
  lambda := inversion_lambda

/-- Source or comparison proof remains to be supplied. -/
public theorem free_inversion :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (h : r-2 ≤ t-w),
    (free_component X r hr s t w h).hom = comparisonPageMap model X (inversion_data X) r s t w := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def finite_quotient_component :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ s t w : ℤ,
    (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) n).Page 2 (s,t,w) ≅
      quotientE2Component model X n s t w := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem finite_quotient_component_retained :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ) (h : 0 ≤ t-w ∧ t-w < n)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    HEq (((finite_quotient_component X n hn) s t w).hom
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) x))) x := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem finite_quotient_retained :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ), 0 ≤ t-w ∧ t-w < n →
    IsIso ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap 2 (s,t,w)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem finite_quotient_safe :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ (r s t w : ℤ), 2 ≤ r → 0 ≤ t-w → t-w+r-2 < n →
    IsIso ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap r (s,t,w)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem degeneration :
  ∀ (X : ClassicalObject) (N : ℤ),
    DegeneratesAt (model.classical.obj (X.obj model.auxiliary)) N →
    DegeneratesAt (model.family.nu model.nu (X.obj model.auxiliary)).sequence N := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem above_diagonal :
  ∀ (X : ClassicalObject) (r : ℤ), 2 ≤ r →
    ∀ (s t w : ℤ), t < w → IsZero ((model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w)) := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public def finite_quotient :
  ∀ (X : ClassicalObject) (n : ℕ), 0 < n → NuModLambdaPageData model X n := fun X n hn => { component := finite_quotient_component X n hn, component_retained := finite_quotient_component_retained X n hn, retained := finite_quotient_retained X n hn, safe := finite_quotient_safe X n hn }

/-- Source or comparison proof remains to be supplied. -/
public theorem finite_quotient_vanishing :
  ∀ (X : ClassicalObject) (n : ℕ), 0 < n →
    ∀ (r : ℤ), 2 ≤ r → ∀ (s t w : ℤ), (t-w < 0 ∨ (n : ℤ) ≤ t-w) →
      IsZero ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) n).Page r (s,t,w)) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def eInfinity_nu :
  ∀ (X : ClassicalObject) (p : Bidegree) (w : ℤ),
    ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      nuEInftyModel model X p w := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def eInfinity_finite :
  ∀ (X : ClassicalObject) (q : ℕ) (_hq : 0 < q) (p : Bidegree) (w : ℤ),
    ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      finiteEInftyModel model X q p w := by
  sorry

public def infinityPresentationData : EInfinityPresentation model where
  nu := eInfinity_nu
  finite := eInfinity_finite

/-- Derived from the fixed objects and previously established operations. -/
public def infinityShift_comparison :
  ∀ k : ℕ, SyntheticESSShiftComparison model (0,-(k:ℤ)) := fun k => KIP126.AdamsSynthetic.Standard.essShift (0,-(k:ℤ))

/-- Source or comparison proof remains to be supplied. -/
public theorem infinityShift_natural :
  ∀ (X Y : SyntheticObject) (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (k : ℕ) (p : Bidegree) (w : ℤ),
    (model.family.map f).eInftyMap (p.1,p.2,w) ≫ (infinityShift model infinityShift_comparison Y k p w).hom =
      (infinityShift model infinityShift_comparison X k p w).hom ≫
        (model.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap (p.1,p.2,w-k) := by
  sorry

public def infinityShiftData : InfinityShiftCoordinates model where
  comparison := infinityShift_comparison
  natural := infinityShift_natural

public def infinityLambda := InfinityShiftCoordinates.lambdaMap model infinityShiftData

public def infinityFiniteLambda := InfinityShiftCoordinates.finiteLambdaMap model infinityShiftData

public def infinityWeightMap := InfinityShiftCoordinates.weightMap model infinityShiftData

public def infinityNuWindow := EInfinityPresentation.nuWindow model infinityPresentationData

public def infinityFiniteWindow := EInfinityPresentation.finiteWindow model infinityPresentationData

public def infinityNuLinear := EInfinityPresentation.nuLinear model infinityPresentationData

public def infinityFiniteLinear := EInfinityPresentation.finiteLinear model infinityPresentationData

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_lambda_nu :
  ∀ (X : ClassicalObject) (k : ℕ) (p : Bidegree) (w : ℤ) (hw : w ≤ p.2)
      (x : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityNuWindow X p (w-k) (by omega) (infinityLambda (.nu X) k p w x) =
      permanentQuotientMap model X (by omega) p (infinityNuWindow X p w hw x) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_lambda_finite :
  ∀ (X : ClassicalObject) (q k : ℕ) (hkq : k < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < (q-k : ℕ))
      (x : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X q (by omega) p (w-k) (by constructor <;> omega)
        (infinityFiniteLambda X q k hkq p w x) =
      quotientMap model X (by omega) (by omega) p
        (infinityFiniteWindow X (q-k) (by omega) p w hw x) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_rho_finite :
  ∀ (X : ClassicalObject) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < i)
      (x : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) j).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X i hi p w hw
        ((model.family.map ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i j hij)).eInftyMap (p.1,p.2,w) x) =
      quotientMap model X (by omega) le_rfl p
        (infinityFiniteWindow X j (by omega) p w (by constructor <;> omega) x) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_rho_nu :
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < q)
      (x : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X q hq p w hw
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).eInftyMap (p.1,p.2,w) x) =
      permanentToFinite model X (q-p.2+w) (1+p.2-w) p
        (infinityNuWindow X p w (by omega) x) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_nu_labels :
  ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel model X s t w hw x) z ↔
      ∃ hx : x ∈ permanentCycles model X (s,t),
        infinityNuWindow X (s,t) w hw z = subquotientClass (permanentCycles model X (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨x,hx⟩ := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_finite_labels :
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (z : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) x)) z ↔
      ∃ hx : x ∈ cycles model X (q-t+w) (s,t),
        infinityFiniteWindow X q hq (s,t) w hw z = subquotientClass (cycles model X (q-t+w) (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨x,hx⟩ := by
  sorry

private def infinityCompatibilityData : EInfinityCompatibility model infinityPresentationData infinityShiftData where
  lambda_nu := eInfinity_lambda_nu
  lambda_finite := eInfinity_lambda_finite
  rho_finite := eInfinity_rho_finite
  rho_nu := eInfinity_rho_nu
  nu_labels := eInfinity_nu_labels
  finite_labels := eInfinity_finite_labels

public abbrev infinityLambda_zero := InfinityShiftCoordinates.lambdaMap_zero model infinityShiftData

public abbrev infinityFiniteLambda_zero := InfinityShiftCoordinates.finiteLambdaMap_zero model infinityShiftData

/-- Derived from the fixed objects and previously established operations. -/
public theorem infinityLambda_epi :
  ∀ (X : ClassicalObject) (k : ℕ) (p : Bidegree) (w : ℤ), w ≤ p.2 →
    Epi (infinityLambda (.nu X) k p w) := EInfinityCompatibility.lambda_epi model infinityCompatibilityData

/-- Derived from the fixed objects and previously established operations. -/
public theorem infinityWeightMap_epi :
  ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂), w₂ ≤ t →
    Epi (infinityWeightMap X s t w₁ w₂ hw) := EInfinityCompatibility.weight_epi model infinityCompatibilityData

/-- Source or comparison proof remains to be supplied. -/
public theorem weights_lambda :
  ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    KIP126.AdamsSynthetic.Standard.weight_map X s t w₁ w₂ hw ht =
      infinityWeightMap X s t w₁ w₂ hw := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem weight_epi :
  ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    Epi (KIP126.AdamsSynthetic.Standard.weight_map X s t w₁ w₂ hw ht) := by
  intro X s t w₁ w₂ hw ht
  rw [weights_lambda]
  exact infinityWeightMap_epi X s t w₁ w₂ hw ht

/-- Source or comparison proof remains to be supplied. -/
public theorem unshifted :
  ∀ T : TriangleData model.auxiliary,
    normalizedExponent model.classicalTower T.f +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1 →
    ∃ (f : model.nu.functor.obj (T.X.obj model.auxiliary) ⟶ model.nu.functor.obj (T.Y.obj model.auxiliary))
      (g : model.nu.functor.obj (T.Y.obj model.auxiliary) ⟶ model.nu.functor.obj (T.Z.obj model.auxiliary))
      (h : model.nu.functor.obj (T.Z.obj model.auxiliary) ⟶
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).obj (model.nu.functor.obj (T.X.obj model.auxiliary))),
      Triangle.mk f g h ∈ distTriang SyntheticSpectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def normalized_cofiber :
  ∀ T : TriangleData model.auxiliary, NormalizedCofiberComparison model T := by
  sorry

public def normalizedCofiberTriangle (T : TriangleData model.auxiliary) :=
  NormalizedCofiberComparison.triangle model (normalized_cofiber T)

public abbrev normalizedCofiberTriangle_distinguished (T : TriangleData model.auxiliary) :=
  NormalizedCofiberComparison.distinguished model (normalized_cofiber T)

/-- Source or comparison proof remains to be supplied. -/
public theorem nuCofiber_nu_exponent :
  normalizedExponent model.classicalTower model.auxiliary.nuMap = 1 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nuCofiber_bottom_exponent :
  normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nuCofiber_top_exponent :
  normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nuCofiber_normalized_label :
  sphereFirstQuotient model 1 4 (quotientClass 1 (normalizedNu model nuCofiber_nu_exponent)) =
    model.standardClasses.standardHi 2 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nuCofiber_triangle :
  ∀ he :
      (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 1,
    NormalizedTriangleCompatible model model.auxiliary.nuRouteTriangle he := by
  sorry

private def nuCofiberData : NuCofiberApplicability model where
  nu_exponent := nuCofiber_nu_exponent
  bottom_exponent := nuCofiber_bottom_exponent
  top_exponent := nuCofiber_top_exponent
  normalized_label := nuCofiber_normalized_label
  triangle := nuCofiber_triangle

/-- Derived from the fixed objects and previously established operations. -/
public theorem nuCofiber_exponent_sum :
  (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f : ℤ) +
    normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
    normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 1 := NuCofiberApplicability.exponent_sum model nuCofiberData

/-- Derived from the fixed objects and previously established operations. -/
public theorem nuCofiber_distinguished :
  normalizedTriangle model model.auxiliary.nuRouteTriangle nuCofiber_exponent_sum ∈ distTriang SyntheticSpectrum := nuCofiber_triangle _

/-- Source or comparison proof remains to be supplied. -/
public theorem nu_cofiber :
  NuCofiberCriterion model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem lift :
  SyntheticLiftComparison model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem triangle_lift :
  SyntheticTriangleLiftComparison model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_finite_lift :
  FiniteLiftCriterion model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_bockstein :
  BocksteinDifferential model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_differentials :
  DifferentialRigidity model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_permanent_lift :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) → PermanentLiftAt model X := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_filtration_lambda :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) → FiltrationLambdaAt model X := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_permanent_lift :
  ∀ X : ClassicalObject, PermanentLiftAt model X := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_filtration_lambda :
  ∀ X : ClassicalObject, FiltrationLambdaAt model X := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_kernel :
  RealizationKernel model := by
  sorry

public def realizeNu := realizeNuZero model realizationData

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_realization_lifetime :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero model X)),
    ClassicalPermanentCycle model X (s,t) x →
    SurvivesTo (model.classical.obj (X.obj model.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_realization_detection :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero model X)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x (realizeNu X a) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_realization_prescribed_lift :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : HomotopyGroup (t-s) (X.obj model.auxiliary)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x a →
    ∃ b : BiHom (t-s) t (nuZero model X), quotientClass 1 b = firstLabel model X s t x ∧
      realizeNu X b = a := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_realization_boundary_lift :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle model X (s,t) y →
    HitOnPage (model.classical.obj (X.obj model.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero model X), quotientClass 1 a = firstLabel model X s t y ∧
      lambdaMultiply (r-1) a = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_lifetime :
  ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero model X)),
    ClassicalPermanentCycle model X (s,t) x →
    SurvivesTo (model.classical.obj (X.obj model.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_detection :
  ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (nuZero model X)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x (realizeNu X a) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_prescribed_lift :
  ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (a : HomotopyGroup (t-s) (X.obj model.auxiliary)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x a →
    ∃ b : BiHom (t-s) t (nuZero model X), quotientClass 1 b = firstLabel model X s t x ∧
      realizeNu X b = a := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_boundary_lift :
  ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle model X (s,t) y →
    HitOnPage (model.classical.obj (X.obj model.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero model X), quotientClass 1 a = firstLabel model X s t y ∧
      lambdaMultiply (r-1) a = 0 := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def bxTheta5 :
  BiHom 62 64 (S_0_0 : SyntheticSpectrum) := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem bx_eta_label :
  sphereFirstQuotient model 1 2 (quotientClass 1 eta) = model.standardClasses.standardHi 1 := eta_label

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_theta_label :
  Theta5Detected model bxTheta5 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_order_two :
  bxTheta5 + bxTheta5 = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_finite :
  ∀ r : ℕ, 1 ≤ r →
    (SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
      model.standardClasses.standardH6Square ↔ quotientClass r (etaThetaSquare eta bxTheta5) = 0) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_total_boundary :
  deltaH6Square model = lambdaEtaThetaSquare eta bxTheta5 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_untruncated :
  model.H6SquarePermanent ↔ lambdaEtaThetaSquare eta bxTheta5 = 0 := by
  sorry

/-- The fixed mathematical object on the project background. -/
@[implicit_reducible] public def may_leftShift :
  ∀ X : SyntheticSpectrum, (tensorLeft X).CommShift ℤ := by
  sorry

/-- The fixed mathematical object on the project background. -/
@[implicit_reducible] public def may_rightShift :
  ∀ X : SyntheticSpectrum, (tensorRight X).CommShift ℤ := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem may_leftExact :
  ∀ X : SyntheticSpectrum, letI := may_leftShift X; (tensorLeft X).IsTriangulated := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem may_rightExact :
  ∀ X : SyntheticSpectrum, letI := may_rightShift X; (tensorRight X).IsTriangulated := by
  sorry

public def mayData : Route.MayContext SyntheticSpectrum where
  leftShift := may_leftShift
  rightShift := may_rightShift
  leftExact := may_leftExact
  rightExact := may_rightExact

/-- Source or comparison proof remains to be supplied. -/
public theorem may_pushpull :
  ∀ T U : HoCofiberSequence (C := SyntheticSpectrum), Nonempty (Route.MayPushpullData SyntheticSpectrum mayData T U) := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem may_signed_boundary :
  Route.MayContext.SignedBoundary SyntheticSpectrum mayData := Route.may_signed_boundary_of_source mayData may_pushpull

/-- Derived from the fixed objects and previously established operations. -/
public def closedTensor :
  ClosedSymmetricTensorTriangulated Spectrum := KIP126.AdamsSynthetic.Standard.closedBackground

/-- Derived from the fixed objects and previously established operations. -/
public def finiteMappingObject :
  MappingObject (fun X : Spectrum => X = SphereSpectrum) → MappingObject (IsFiniteSpectrum (C := Spectrum)) := fun X => ⟨X.val, by rw [X.property]; exact IsFiniteSpectrum.sphere⟩

/-- Derived from the fixed objects and previously established operations. -/
public def mapping :
  MappingSpectrumSystem closedTensor model.classicalTower (fun X : Spectrum => X = SphereSpectrum) := {
    convergence := fun X Y hX hY =>
      KIP126.AdamsSynthetic.Standard.mappingConvergence X Y
        (by rw [hX]; exact IsFiniteSpectrum.sphere) (by rw [hY]; exact IsFiniteSpectrum.sphere) }

/-- Derived from the fixed objects and previously established operations. -/
public def mappingComposition :
  MappingComposition mapping := {
    pairing := fun X Y Z => KIP126.AdamsSynthetic.Standard.mapping_pairing
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    parity := fun X Y Z => KIP126.AdamsSynthetic.Standard.mapping_parity
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    abutment_compatible := fun X Y Z => KIP126.AdamsSynthetic.Standard.mapping_abutment_compatible
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    page_associative := fun W X Y Z => KIP126.AdamsSynthetic.Standard.mapping_page_associative
      (finiteMappingObject W) (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    identity := fun X => KIP126.AdamsSynthetic.Standard.mapping_identity (finiteMappingObject X)
    identity_actual := fun X => KIP126.AdamsSynthetic.Standard.mapping_identity_actual (finiteMappingObject X)
    page_left_unital := fun X Y => KIP126.AdamsSynthetic.Standard.mapping_page_left_unital
      (finiteMappingObject X) (finiteMappingObject Y)
    page_right_unital := fun X Y => KIP126.AdamsSynthetic.Standard.mapping_page_right_unital
      (finiteMappingObject X) (finiteMappingObject Y) }

/-- Derived from the fixed objects and previously established operations. -/
public theorem mappingSphereCompatibility :
  MappingSphereCompatibility mappingComposition model.sphereAlgebra rfl := ⟨KIP126.AdamsSynthetic.Standard.mapping_sphere_product, KIP126.AdamsSynthetic.Standard.mapping_sphere_unit⟩

/-- Source or comparison proof remains to be supplied. -/
public theorem moss_weak_convergence :
  ∀ X Y : MappingObject (fun X : Spectrum => X = SphereSpectrum), Moss.WeakConvergence (P := model.classicalTower) (B := closedTensor) X Y := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem moss_detection :
  Moss.DetectionCompatible mapping mappingComposition := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem moss_indeterminacy :
  ∀ (r : ℤ) (hr : 3 ≤ r) (W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum)) (i j k : ℤ × ℤ)
    (a : (Moss.sequence mapping W X).Page r i) (b : (Moss.sequence mapping X Y).Page r j)
    (c : (Moss.sequence mapping Y Z).Page r k)
    (x₀ x : (Moss.sequence mapping W Z).Page r (Moss.PageMassey.degree r i j k)),
    Moss.PageMassey.Relation mapping mappingComposition r hr x₀ a b c →
      (Moss.PageMassey.Relation mapping mappingComposition r hr x a b c ↔
        Moss.PageMassey.Indeterminacy mapping mappingComposition r (j := j) a c (x-x₀)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem moss_convergence :
  ∀ W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum),
    Moss.StatementAt mapping mappingComposition W X Y Z := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem moss_at :
  ∀ W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum),
    Moss.StatementAt mapping mappingComposition W X Y Z := moss_convergence

/-- The fixed mathematical object on the project background. -/
public def syntheticH0 :
  BiHom 0 1 (S_0_0 : SyntheticSpectrum) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_h0_label :
  KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient
    1 1 (quotientClass 1 syntheticH0) = model.standardClasses.standardHi 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_lambda_h0 :
  lambdaMultiply 1 syntheticH0 = Route.syntheticTwo := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_h0_eta :
  sphereProduct syntheticH0 eta = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_low_indeterminacy :
  ∀ a : BiHom 2 3 (S_0_0 : SyntheticSpectrum), sphereProduct syntheticH0 a = 0 := by
  sorry

public abbrev IsConnected := KIP126.Literature.IsConnected (C := Spectrum)

public abbrev ModTwoCohomology := KIP126.Literature.ModTwoCohomology model

public abbrev sphereFirstQuotient := KIP126.Literature.sphereFirstQuotient model

public abbrev h6FirstQuotient := KIP126.Literature.h6FirstQuotient model

public abbrev h6FirstQuotient_label := KIP126.Literature.h6FirstQuotient_label model

public abbrev Theta5Detected := KIP126.Literature.Theta5Detected model

public abbrev ClassicalTheta5Detected := KIP126.Literature.ClassicalTheta5Detected model

public abbrev ClassicalPermanentCycle := KIP126.Literature.ClassicalPermanentCycle model

public abbrev BHSObjectApplicability := KIP126.Literature.BHSObjectApplicability model

public abbrev FiniteLiftCriterion := KIP126.Literature.FiniteLiftCriterion model

public abbrev PermanentLiftAt := KIP126.Literature.PermanentLiftAt model

public abbrev FiltrationLambdaAt := KIP126.Literature.FiltrationLambdaAt model

public abbrev LambdaDivisible := KIP126.Literature.LambdaDivisible model

public abbrev nuZero := KIP126.Literature.nuZero model

public abbrev firstLabel := KIP126.Literature.firstLabel model

public abbrev bocksteinArrow := KIP126.Literature.bocksteinArrow model

public abbrev bocksteinLabel := KIP126.Literature.bocksteinLabel model

public abbrev oneLineTarget := KIP126.Literature.oneLineTarget model

public abbrev classicalTwo := KIP126.Literature.classicalTwo (C := Spectrum)

public abbrev classicalSphereProduct := @KIP126.Literature.classicalSphereProduct Spectrum inferInstance

public abbrev etaThetaSquare := KIP126.Literature.etaThetaSquare eta

public abbrev lambdaEtaThetaSquare := KIP126.Literature.lambdaEtaThetaSquare eta

public abbrev deltaH6Square := KIP126.Literature.deltaH6Square model

public abbrev classicalDifferential := KIP126.Literature.classicalDifferential model

public abbrev syntheticDifferential := KIP126.Literature.syntheticDifferential model

public abbrev cycles := KIP126.Literature.cycles model

public abbrev boundaries := KIP126.Literature.boundaries model

public abbrev permanentCycles := KIP126.Literature.permanentCycles model

public abbrev CycleQuotient := KIP126.Literature.CycleQuotient model

public abbrev PermanentQuotient := KIP126.Literature.PermanentQuotient model

public abbrev quotientMap := @KIP126.Literature.quotientMap Spectrum inferInstance inferInstance SyntheticSpectrum inferInstance inferInstance model

public abbrev NuCofiberCriterion := KIP126.Literature.NuCofiberCriterion model

public abbrev SyntheticLiftComparison := KIP126.Literature.SyntheticLiftComparison model

public abbrev SyntheticTriangleLiftComparison := KIP126.Literature.SyntheticTriangleLiftComparison model

public abbrev NormalizedTriangleCompatible := KIP126.Literature.NormalizedTriangleCompatible model

public abbrev normalizedTriangle := KIP126.Literature.normalizedTriangle model

public abbrev normalizedNu := KIP126.Literature.normalizedNu model

public abbrev MossStatementAt := Moss.StatementAt mapping mappingComposition

public abbrev MossRelation := @Moss.PageMassey.Relation

public abbrev MossIndeterminacy := @Moss.PageMassey.Indeterminacy

public abbrev TripleToda := @Route.TripleToda

public abbrev TodaRelation := @KIP126.StableHomotopy.Toda.Relation

public abbrev toda_composable := @KIP126.StableHomotopy.Toda.composable

public abbrev toda_exists_relation := @KIP126.StableHomotopy.Toda.exists_relation

public abbrev toda_relation_iff_indeterminacy := @KIP126.StableHomotopy.Toda.relation_iff_indeterminacy

public abbrev toda_juggling := @KIP126.StableHomotopy.Toda.juggling

public abbrev toda_precompose := @KIP126.StableHomotopy.Toda.precompose

public abbrev toda_postcompose := @KIP126.StableHomotopy.Toda.postcompose

public abbrev toda_absorb_first := @KIP126.StableHomotopy.Toda.absorb_first

public abbrev toda_absorb_last := @KIP126.StableHomotopy.Toda.absorb_last

public abbrev toda_shuffle_iff := @KIP126.StableHomotopy.Toda.shuffle_iff

public abbrev toda_suspension_iff := @KIP126.StableHomotopy.Toda.suspension_iff

public abbrev toda_map := @KIP126.StableHomotopy.Toda.map

public abbrev toda_tensor_right := @KIP126.StableHomotopy.Toda.tensor_right

public abbrev toda_tensor_left := @KIP126.StableHomotopy.Toda.tensor_left

end KIP126.Literature.Standard
end
