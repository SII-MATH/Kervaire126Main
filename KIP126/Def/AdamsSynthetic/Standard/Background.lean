module

public import KIP126.Def.AdamsSynthetic.System
public import KIP126.Def.AdamsSynthetic.Context
public import KIP126.Def.AdamsSynthetic.Families
public import KIP126.Def.AdamsSynthetic.Sphere
public import KIP126.Def.AdamsSynthetic.Configuration
public import KIP126.Def.SpectralSequence

/-! The fixed classical and synthetic background used in this project.
Every unfinished construction is named at its mathematical boundary; the
assembled model below has no separate existence assumption. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route
noncomputable section

/-- The category of spectra; its concrete model is a deferred construction. -/
public def Spectrum : Type 1 := by sorry
/-- The category of HF₂-synthetic spectra; its construction is deferred. -/
public def SyntheticSpectrum : Type 1 := by sorry
public instance spectrumCategory : StableHomotopyCategory.{1,0} Spectrum := by sorry
public instance syntheticCategory : SyntheticCategory.{1,0} SyntheticSpectrum := by sorry
public instance spectrumCofiber : HasFunctorialCofiber (C := Spectrum) := by sorry
public instance syntheticCofiber : HasFunctorialCofiber (C := SyntheticSpectrum) := by sorry

/-- HF₂ and its homotopy identification on the fixed category. -/
public def coefficients : ModTwoCoefficients Spectrum := by sorry
/-- The classical Adams functor, including its first page and differential degree. -/
public def classical : ClassicalAdamsFamily Spectrum := by sorry
/-- The fixed ν functor, including its sphere and suspension comparisons. -/
public def nu : NuFunctorData Spectrum SyntheticSpectrum := by sorry
/-- The synthetic Adams functor on the fixed synthetic category. -/
public def family : SyntheticAdamsFamily SyntheticSpectrum := by sorry

/-- ν preserves a distinguished triangle under the complete HF₂ short-exactness hypothesis. -/
public theorem nu_preserves_triangle (T : CategoryTheory.Pretriangulated.Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients T) :
    ∃ h : nu.functor.obj T.obj₃ ⟶
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).obj (nu.functor.obj T.obj₁),
      CategoryTheory.Pretriangulated.Triangle.mk
        (nu.functor.map T.mor₁) (nu.functor.map T.mor₂) h ∈ distTriang SyntheticSpectrum := by
  sorry

/-- The λ-localization and its equivalence with this classical category. -/
public def recovery : LambdaRecovery nu := by sorry
/-- Exactness of the same suspension and realization functors. -/
public def exactness : StructuralExactness nu recovery := by sorry
/-- The fixed auxiliary spectra used in the selected object closure. -/
public def auxiliary : AuxiliaryData Spectrum := by sorry
/-- Multiplication on the actual sphere E₂, not an independent formal algebra. -/
public def sphereAlgebra : SphereE2Algebra classical := by sorry
/-- The designated standard hᵢ on this very sphere E₂. -/
public def standardHi (i : ℕ) : ActualE2At classical (hiDegree i) := by sorry
public def standardClasses : StandardSphereClasses classical sphereAlgebra := ⟨standardHi⟩
public def classicalTower : ClassicalTowerPresentation coefficients.unit classical := by sorry
public def classicalSuspension (X : ClassicalObject) :
    ClassicalTowerSuspension classicalTower (X.obj auxiliary) := by sorry
public def syntheticTower : SyntheticTowerPresentation (nuCoefficientUnit coefficients nu) family := by sorry
public def comparison : E2Comparison classical family nu auxiliary := by sorry
public def quotients : LambdaQuotientSystem SyntheticSpectrum := by sorry
public def normalizedMap (X Y : ClassicalObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary) :
    NormalizedSyntheticMap classicalTower nu f := by sorry
public def classicalConvergence (X : ClassicalObject) :
    ClassicalTowerConvergence classicalTower (X.obj auxiliary) := by sorry
public def convergence (X : SyntheticObject) :
    SyntheticTowerConvergence syntheticTower (X.obj nu auxiliary) := by sorry
public def firstQuotient : FirstQuotientComparison classical nu auxiliary := by sorry


public theorem convergence_natural : ∀ (X Y : SyntheticObject)
      (f : X.obj nu auxiliary ⟶ Y.obj nu auxiliary),
    Nonempty (ConvergentMap family f (convergence X).toConvergence
      (convergence Y).toConvergence) := by sorry

public theorem first_quotient : ∀ (X : ClassicalObject) (a s t : ℤ)
      (x : (classical.obj (X.obj auxiliary)).Page 2 (s,t)),
    KIP126.AdamsSynthetic.Detects
      (convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
      (family.pageMap
        (HasFunctorialCofiber.cofibι (lambdaPow 1
          ((SyntheticCategory.biShift (0,a)).obj (nu.functor.obj (X.obj auxiliary)))))
        2 (s,t,t+a) (by simpa only [Nat.cast_zero, sub_zero] using comparison.nuE2 X a s t 0 x))
      ((firstQuotient X a s t).symm x) := by sorry


public theorem sphere_first_quotient : ∀ (s t : ℤ) (x : classical.sphere.Page 2 (s,t)),
    Detects (convergence (.quotient 1 .sphere)) (s,t,t)
      (family.pageMap (XModLambdaN.incl S_0_0 1) 2 (s,t,t)
        (by simpa only [SyntheticAdamsFamily.sphere, SyntheticAdamsSS.Page,
          Nat.cast_zero, sub_zero] using comparison.sphereE2 s t 0 x))
      ((sphereFirstQuotient nu quotients.functoriality firstQuotient s t).symm x) := by sorry

public theorem sphere_homotopy_lambda : ∀ (s t : ℤ) (k : ℕ) (x : BiHom (t-s) t (S_0_0 : SyntheticSpectrum)),
    Detects (convergence .sphere) (s,t,t-k)
      (comparison.sphereE2 s t k (sphereFirstQuotient nu quotients.functoriality firstQuotient s t (quotientClass 1 x)))
      (lambdaMultiply k x) := by sorry

public theorem multiplicationCompatible :
    MultiplicationCompatible comparison sphereAlgebra (convergence .sphere) := by sorry
public theorem sphereProductCommutative : SphereProductCommutative (Syn := SyntheticSpectrum) := by sorry

/-- Internal organization of the already selected objects and named theorems.
Consumers never need to supply a model instance or prove this structure exists. -/
public def model : Model Spectrum SyntheticSpectrum where
  coefficients := coefficients
  classical := classical
  nu := nu
  family := family
  nuExactTriangle := ⟨nu_preserves_triangle⟩
  recovery := recovery
  exactness := exactness
  auxiliary := auxiliary
  sphereAlgebra := sphereAlgebra
  standardClasses := standardClasses
  classicalTower := classicalTower
  classicalSuspension := classicalSuspension
  syntheticTower := syntheticTower
  comparison := comparison
  quotients := quotients
  normalizedMap := normalizedMap
  classicalConvergence := classicalConvergence
  convergence := convergence
  firstQuotient := firstQuotient
  comparisonCompatible := ⟨convergence_natural, first_quotient⟩
  sphereDetectionCompatible := ⟨sphere_first_quotient, sphere_homotopy_lambda⟩
  multiplicationCompatible := multiplicationCompatible
  sphereProductCommutative := sphereProductCommutative

end
end KIP126.AdamsSynthetic.Standard
