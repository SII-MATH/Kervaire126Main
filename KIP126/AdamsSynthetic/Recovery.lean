module

public import KIP126.AdamsSynthetic.Context
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Reflective

@[expose] section

/-! Recovery through the given λ-localization, with the same ν and actual
λ-invertible full subcategory. Adapted from the fixed review input records. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The actual component `λ_X : Σ^(0,-1)X ⟶ X` is invertible. -/
public def IsLambdaInvertible : ObjectProperty Syn :=
  fun X => IsIso (SyntheticCategory.lam.app X)

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

/-- The full subcategory cut out by invertibility of the existing λ map. -/
public abbrev LambdaInvertibleObjects (Syn : Type u) [SyntheticCategory.{u, v} Syn] :=
  (IsLambdaInvertible (Syn := Syn)).FullSubcategory

/-- The actual full-subcategory inclusion; its object map forgets only the proof. -/
public abbrev lambdaInclusion (Syn : Type u) [SyntheticCategory.{u, v} Syn] :
    LambdaInvertibleObjects Syn ⥤ Syn :=
  (IsLambdaInvertible (Syn := Syn)).ι

/-- A left adjoint to the specified inclusion. Its unit and universal
property are determined by this adjunction, not chosen independently. -/
public structure LambdaLocalization (Syn : Type u) [SyntheticCategory.{u, v} Syn] where
  reflector : Syn ⥤ LambdaInvertibleObjects Syn
  adjunction : reflector ⊣ lambdaInclusion Syn

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The resulting reflective-subcategory witness, with the same reflector. -/
public abbrev LambdaLocalization.reflective (L : LambdaLocalization Syn) :
    Reflective (lambdaInclusion Syn) where
  L := L.reflector
  adj := L.adjunction

/-- Localization viewed as an endofunctor of the ambient synthetic category. -/
public def LambdaLocalization.endofunctor (L : LambdaLocalization Syn) : Syn ⥤ Syn :=
  L.reflector ⋙ lambdaInclusion Syn

/-- The unit of this specific adjunction. -/
public def LambdaLocalization.unit (L : LambdaLocalization Syn) :
    𝟭 Syn ⟶ L.endofunctor := L.adjunction.unit

/-- The uniquely determined factorization of a map to a λ-invertible object. -/
public def LambdaLocalization.lift (L : LambdaLocalization Syn) {X Y : Syn}
    (hY : IsLambdaInvertible Y) (f : X ⟶ Y) : L.endofunctor.obj X ⟶ Y :=
  ((L.adjunction.homEquiv X ⟨Y, hY⟩).symm f).hom

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v u' v'

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]

/-- The specified localization recovers the same classical category and ν. -/
public structure LambdaRecovery (N : NuFunctorData C Syn) where
  localization : LambdaLocalization Syn
  equivalence : LambdaInvertibleObjects Syn ≌ C
  nuLocalization : N.functor ⋙ localization.reflector ≅ equivalence.inverse

variable {N : NuFunctorData C Syn}

/-- Underlying-spectrum realization, with the source and target fixed. -/
public def LambdaRecovery.realization (R : LambdaRecovery N) : Syn ⥤ C :=
  R.localization.reflector ⋙ R.equivalence.functor

/-- The spectral Yoneda embedding determined by the same equivalence. -/
public def LambdaRecovery.spectralYoneda (R : LambdaRecovery N) : C ⥤ Syn :=
  R.equivalence.inverse ⋙ lambdaInclusion Syn

/-- The spectral Yoneda embedding is fully faithful by the equivalence and
the actual full-subcategory inclusion. -/
public def LambdaRecovery.fullyFaithfulSpectralYoneda (R : LambdaRecovery N) :
    R.spectralYoneda.FullyFaithful :=
  R.equivalence.fullyFaithfulInverse.comp
    (IsLambdaInvertible (Syn := Syn)).fullyFaithfulι

/-- Realization is left adjoint to spectral Yoneda, not to ν. -/
public def LambdaRecovery.adjunction (R : LambdaRecovery N) :
    R.realization ⊣ R.spectralYoneda :=
  R.localization.adjunction.comp R.equivalence.toAdjunction

/-- Applying realization after the specified ν recovers the identity functor. -/
public def LambdaRecovery.nuRealizationIso (R : LambdaRecovery N) :
    N.functor ⋙ R.realization ≅ 𝟭 C :=
  (Functor.associator N.functor R.localization.reflector R.equivalence.functor).symm ≪≫
    Functor.isoWhiskerRight R.nuLocalization R.equivalence.functor ≪≫ R.equivalence.counitIso

/-- The canonical map from ν to spectral Yoneda factors through the actual
localization unit and the supplied natural comparison. -/
public def LambdaRecovery.nuToSpectralYoneda (R : LambdaRecovery N) :
    N.functor ⟶ R.spectralYoneda :=
  Functor.whiskerLeft N.functor R.localization.unit ≫
    (Functor.isoWhiskerRight R.nuLocalization (lambdaInclusion Syn)).hom

end KIP126.Synthetic.Context

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]

/-- The exactness conditions of the fixed review model, applied to the same
specified suspension and realization functors. No extra ν exactness is inferred. -/
public structure StructuralExactness (N : NuFunctorData C Syn) (R : LambdaRecovery N) where
  classicalTriangulated : IsTriangulated C
  syntheticTriangulated : IsTriangulated Syn
  shiftAdditive : ∀ p, (SyntheticCategory.biShift (Syn := Syn) p).Additive
  shiftCommShift : ∀ p, (SyntheticCategory.biShift (Syn := Syn) p).CommShift ℤ
  shiftExact : ∀ p, letI := shiftCommShift p;
    (SyntheticCategory.biShift (Syn := Syn) p).IsTriangulated
  realizationShift : R.realization.CommShift ℤ
  realizationExact : letI := realizationShift; R.realization.IsTriangulated
end KIP126.AdamsSynthetic
