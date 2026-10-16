module

public import KIP126.AdamsSynthetic

/-! Literature contracts on the supplied background. Source:
`KIP126/Interface/Challenge/Literature/Source.lean` and
`Def/Kervaire/Route/SourceLanguage.lean`, review commit bbac1fc05843.
The former KIPBase connectivity and universal-coefficient obligations are
kept as source results, not inferred from the abstract category axioms. -/

@[expose] section
set_option autoImplicit false
namespace KIP126.Literature
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- Connectivity uses the actual sphere shifts of this category. -/
public def IsConnected (X : C) (n : ℤ) : Prop :=
  ∀ i : ℤ, i ≤ n → Subsingleton (HomotopyGroup i X)

/-- Cohomology has the legacy sign convention: maps from `ΣⁿX` to HF₂. -/
public abbrev ModTwoCohomology (n : ℤ) (X : C) :=
  (shiftFunctor C n).obj X ⟶ D.coefficients.object

/-- The ordinary stable-connectivity and HF₂ universal-coefficient results.
Their applicability to this chosen background is a producer obligation. -/
private structure ClassicalFoundationResults where
  sphere_connected : IsConnected (SphereSpectrum (C := C)) (-1)
  connected_homology_vanishing : ∀ (X : C) (n : ℤ), IsConnected X n →
    ∀ i : ℤ, i ≤ n → Subsingleton (ModTwoHomology D.coefficients i X)
  universal_coefficient : ∀ (n : ℤ) (X : C),
    ModTwoCohomology D n X ≃+ (ModTwoHomology D.coefficients (-n) X →+ ZMod 2)

/-- The first λ-quotient coordinate is derived from the model's comparison. -/
public def sphereFirstQuotient (s t : ℤ) :=
  KIP126.AdamsSynthetic.sphereFirstQuotient D.nu D.quotients.functoriality
    D.firstQuotient s t

/-- Actual h₆ in the first quotient, with no lift to the synthetic sphere.
This repairs the unbound old `syntheticH6` constant and does not assume the
permanence of either h₆ or h₆². -/
public def h6FirstQuotient : BiHom 63 64 (XModLambdaN (S_0_0 : Syn) 1) :=
  (sphereFirstQuotient D 1 64).symm D.standardClasses.standardH6

public theorem h6FirstQuotient_label :
    sphereFirstQuotient D 1 64 (h6FirstQuotient D) = D.standardClasses.standardH6 :=
  (sphereFirstQuotient D 1 64).apply_symm_apply _

public def Theta5Detected (a : BiHom 62 64 (S_0_0 : Syn)) : Prop :=
  sphereFirstQuotient D 2 64 (quotientClass 1 a) = D.standardClasses.standardHiSquare 5

public def ClassicalTheta5Detected (a : HomotopyGroup (C := C) 62 SphereSpectrum) : Prop :=
  ClassicalDetects (D.classicalConvergence .sphere) (2,64)
    (D.standardClasses.standardHiSquare 5) a

/-- Realization coordinates use the existing λ-localization, unit and λ powers. -/
public structure RealizationCoordinates where
  additive : D.recovery.realization.Additive
  sphere : ∀ m w : ℤ, Sphere (C := C) m ≅ D.recovery.realization.obj (Smn (Syn := Syn) m w)
  unit : (sphere 0 0).hom ≫ D.recovery.realization.map
      (SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn)) =
    (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫
      D.recovery.nuRealizationIso.inv.app SphereSpectrum ≫
      D.recovery.realization.map D.nu.unitIso.hom
  lambda : ∀ (m w : ℤ) (k : ℕ),
    (sphere m (w-k)).hom ≫
      D.recovery.realization.map (lambdaMultiply k (𝟙 (Smn (Syn := Syn) m w))) =
        (sphere m w).hom

public def RealizationCoordinates.sphereMap (R : RealizationCoordinates D) (m w : ℤ) :
    BiHom m w (S_0_0 : Syn) →+ HomotopyGroup (C := C) m SphereSpectrum := by
  letI := R.additive
  exact
    { toFun := fun a => (R.sphere m w).hom ≫ D.recovery.realization.map a ≫
        D.recovery.realization.map D.nu.unitIso.inv ≫
        D.recovery.nuRealizationIso.hom.app SphereSpectrum
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp] }

/-- Normalized η is the normalized map of the model's actual classical η. -/
public def etaSourceIso (he : normalizedExponent D.classicalTower D.auxiliary.etaMap = 1) :
    Smn (Syn := Syn) 1 2 ≅
      (SyntheticCategory.biShift (0,(normalizedExponent D.classicalTower D.auxiliary.etaMap : ℤ))).obj
        (D.nu.functor.obj (Sphere (C := C) 1)) := by
  rw [he]
  exact ((SyntheticCategory.biShift (0,1)).mapIso
      (D.nu.suspensionIso SphereSpectrum ≪≫
        (SyntheticCategory.biShift (1,1)).mapIso D.nu.unitIso) ≪≫
      (SyntheticCategory.biShift_comp (1,1) (0,1)).app S_0_0).symm

/-- One tmf source, compared with the chosen detector and its actual unit. -/
private structure TmfBindings where
  source : C
  sourceIso : source ≅ D.auxiliary.detector
  sourceUnit : SphereSpectrum ⟶ source
  unit_agrees : sourceUnit ≫ sourceIso.hom = D.auxiliary.detectorUnit
  g : D.classical.sphere.Page 2 (4,24)
  deltaH1g : D.classical.sphere.Page 2 (9,54)

/-- All source choices are correlated with one actual model. -/
private structure ClassicalBindings where
  realization : RealizationCoordinates D
  eta : BiHom 1 2 (S_0_0 : Syn)
  eta_exponent : normalizedExponent D.classicalTower D.auxiliary.etaMap = 1
  eta_normalized : eta = (etaSourceIso D eta_exponent).hom ≫
    (D.normalizedMap (.shift 1 .sphere) .sphere D.auxiliary.etaMap).map ≫ D.nu.unitIso.hom
  theta5 : HomotopyGroup (C := C) 62 SphereSpectrum
  tmf : TmfBindings D

/-- Xu Corollary 1.3, IWX's 62-stem, and standard Hopf detections.
The stronger arbitrary-choice synthetic consequences are derived separately. -/
private structure ClassicalResults (B : ClassicalBindings D) : Prop where
  h5Square_permanent : NonzeroSurvival D.classical.sphere (2,64)
    (D.standardClasses.standardHiSquare 5)
  theta5_detection : ClassicalTheta5Detected D B.theta5
  stem62_exponent_two : ∀ a : HomotopyGroup (C := C) 62 SphereSpectrum, a+a=0
  theta5_filtration_gap : ∀ a b, ClassicalTheta5Detected D a → ClassicalTheta5Detected D b →
    a-b ∈ (D.classicalTower.tower SphereSpectrum).filtrationSubmodule 6 62
  eta_detection : ClassicalDetects (D.classicalConvergence .sphere) (1,2)
    (D.standardClasses.standardHi 1) D.auxiliary.etaMap
  nu_detection : ClassicalDetects (D.classicalConvergence .sphere) (1,4)
    (D.standardClasses.standardHi 2) D.auxiliary.nuMap
  eta_permanent : NonzeroSurvival D.classical.sphere (1,2) (D.standardClasses.standardHi 1)
  nu_permanent : NonzeroSurvival D.classical.sphere (1,4) (D.standardClasses.standardHi 2)
  eta_label : sphereFirstQuotient D 1 2 (quotientClass 1 B.eta) = D.standardClasses.standardHi 1
  eta_realization : B.realization.sphereMap D 1 2 B.eta = D.auxiliary.etaMap
  theta5_lift : ∃ a : BiHom 62 64 (S_0_0 : Syn),
    Theta5Detected D a ∧ B.realization.sphereMap D 62 64 a = B.theta5

/-- The chosen classical θ₅ has order dividing two by the 62-stem result. -/
private theorem ClassicalResults.theta5_order_two {B : ClassicalBindings D}
    (R : ClassicalResults D B) : B.theta5 + B.theta5 = 0 :=
  R.stem62_exponent_two B.theta5

/-- The precise additional comparison needed for arbitrary synthetic choices.
These transport obligations are explicit parameters, not silently upgraded
classical source facts or new unconditional Literature results. -/
private structure Theta5Transport (B : ClassicalBindings D) : Prop where
  detection : ∀ a, Theta5Detected D a →
    ClassicalTheta5Detected D (B.realization.sphereMap D 62 64 a)
  doubling_kernel : ∀ a, Theta5Detected D a →
    B.realization.sphereMap D 62 64 (a+a) = 0 → a+a=0
  filtration_reflection : ∀ a b, Theta5Detected D a → Theta5Detected D b →
    B.realization.sphereMap D 62 64 (a-b) ∈
      (D.classicalTower.tower SphereSpectrum).filtrationSubmodule 6 62 →
    FiltrationAtLeast D.syntheticTower 6 (a-b)

private theorem theta5_order_two {B : ClassicalBindings D} (R : ClassicalResults D B)
    (T : Theta5Transport D B) (a : BiHom 62 64 (S_0_0 : Syn)) (ha : Theta5Detected D a) : a+a=0 :=
  T.doubling_kernel a ha (by rw [map_add]; exact R.stem62_exponent_two _)

private theorem theta5_indeterminacy_AF_ge_6 {B : ClassicalBindings D} (R : ClassicalResults D B)
    (T : Theta5Transport D B) (a b : BiHom 62 64 (S_0_0 : Syn))
    (ha : Theta5Detected D a) (hb : Theta5Detected D b) : FiltrationAtLeast D.syntheticTower 6 (a-b) :=
  T.filtration_reflection a b ha hb (by
    rw [map_sub]
    exact R.theta5_filtration_gap _ _ (T.detection a ha) (T.detection b hb))

private theorem theta5_detected_exists {B : ClassicalBindings D} (R : ClassicalResults D B) :
    ∃ a : BiHom 62 64 (S_0_0 : Syn), Theta5Detected D a := by
  obtain ⟨a, ha, _⟩ := R.theta5_lift
  exact ⟨a, ha⟩

end
end KIP126.Literature
