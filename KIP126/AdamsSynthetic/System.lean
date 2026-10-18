module

public import KIP126.AdamsSynthetic.Comparisons
public import KIP126.AdamsSynthetic.Detection
public import KIP126.AdamsSynthetic.Extension
public import KIP126.AdamsSynthetic.Sphere
public import KIP126.AdamsSynthetic.Normalized
public import KIP126.AdamsSynthetic.Quotients
public import KIP126.AdamsSynthetic.Recovery
public import KIP126.AdamsSynthetic.Compatibility
public import KIP126.AdamsSynthetic.Suspension

/-! One parameter background for all consumers. Source results and computation
deliveries are not fields of this record. In particular filtration separation
and the final permanence result are not manufactured by this interface. -/

@[expose] section
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]

/-- The synthetic coefficient unit is the image of this very HF₂ unit. -/
public noncomputable def nuCoefficientUnit (H : ModTwoCoefficients C)
    (N : NuFunctorData C Syn) : S_0_0 ⟶ N.functor.obj H.object :=
  N.unitIso.inv ≫ N.functor.map H.unit
end KIP126.AdamsSynthetic

namespace KIP126.Kervaire.Route
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
universe u v w
variable (C : Type u) [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  (Syn : Type w) [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The same given background supplies every named object and comparison.
Towers and their presentations are inputs, not concrete implementations. -/
public structure ModelData where
  coefficients : ModTwoCoefficients C
  classical : ClassicalAdamsFamily C
  nu : NuFunctorData C Syn
  family : SyntheticAdamsFamily Syn
  /-- Preservation uses the complete homology short-exactness premise. -/
  nuExactTriangle : ∀ (T : CategoryTheory.Pretriangulated.Triangle C),
    T ∈ distTriang C → HomologyShortExact coefficients T →
    ∃ h : nu.functor.obj T.obj₃ ⟶ (shiftFunctor Syn (1 : ℤ)).obj (nu.functor.obj T.obj₁),
      CategoryTheory.Pretriangulated.Triangle.mk
        (nu.functor.map T.mor₁) (nu.functor.map T.mor₂) h ∈ distTriang Syn
  recovery : LambdaRecovery nu
  exactness : StructuralExactness nu recovery
  auxiliary : AuxiliaryData C
  sphereAlgebra : SphereE2Algebra classical
  standardClasses : StandardSphereClasses classical sphereAlgebra
  classicalTower : ClassicalTowerPresentation coefficients.unit classical
  classicalSuspension : ∀ X : ClassicalObject,
    ClassicalTowerSuspension classicalTower (X.obj auxiliary)
  syntheticTower : SyntheticTowerPresentation (nuCoefficientUnit coefficients nu) family
  comparison : E2Comparison classical family nu auxiliary
  quotients : LambdaQuotientSystem Syn
  normalizedMap : ∀ (X Y : ClassicalObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary),
    NormalizedSyntheticMap classicalTower nu f
  classicalConvergence : ∀ X : ClassicalObject,
    ClassicalTowerConvergence classicalTower (X.obj auxiliary)
  convergence : ∀ X : SyntheticObject,
    SyntheticTowerConvergence syntheticTower
      (X.obj nu auxiliary)
  /-- The first quotient comparison has the same shifted ν-object and E₂. -/
  firstQuotient : FirstQuotientComparison classical nu auxiliary

variable {C Syn}

/-- Compatibility on the selected object closure. No convergence on every
synthetic object is requested, and every induced map is the actual map. -/
public structure ComparisonCompatible (D : ModelData C Syn) : Prop where
  convergence_natural : ∀ (X Y : SyntheticObject)
      (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary),
    Nonempty (ConvergentMap D.family f (D.convergence X).toConvergence
      (D.convergence Y).toConvergence)
  first_quotient : ∀ (X : ClassicalObject) (a s t : ℤ)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)),
    KIP126.AdamsSynthetic.Detects
      (D.convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
      (D.family.pageMap
        (HasFunctorialCofiber.cofibι (lambdaPow 1
          ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.auxiliary)))))
        2 (s,t,t+a) (by simpa only [Nat.cast_zero, sub_zero] using D.comparison.nuE2 X a s t 0 x))
      ((D.firstQuotient X a s t).symm x)

variable (C Syn)

/-- The coherent consumer background. This does not assert an instance exists. -/
public structure Model extends ModelData C Syn where
  comparisonCompatible : ComparisonCompatible toModelData
  sphereDetectionCompatible : SphereDetectionCompatible comparison quotients.functoriality
    firstQuotient (convergence .sphere) (convergence (.quotient 1 .sphere))
  multiplicationCompatible : MultiplicationCompatible comparison sphereAlgebra (convergence .sphere)
  sphereProductCommutative : SphereProductCommutative (Syn := Syn)

variable {C Syn}
namespace Model
variable (D : Model C Syn)

/-- Naturality supplies one witness tied to this context and this map. -/
public noncomputable def convergentMap (X Y : SyntheticObject)
    (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary) :
    ConvergentMap D.family f (D.convergence X).toConvergence
      (D.convergence Y).toConvergence :=
  Classical.choice (D.comparisonCompatible.convergence_natural X Y f)

/-- The final statement, with its original common-representative semantics.
This definition is a target, never an input field guaranteeing its truth. -/
public def H6SquarePermanent : Prop :=
  KIP126.Core.SpectralSequence.NonzeroSurvival D.classical.sphere (2,128)
    D.standardClasses.standardH6Square

/-- The original separation obligation remains separate from the model. -/
public def HomotopySeparated : Prop :=
  ∀ X : SyntheticObject,
    KIP126.AdamsSynthetic.HomotopySeparated D.syntheticTower (X.obj D.nu D.auxiliary)

end Model
end KIP126.Kervaire.Route
