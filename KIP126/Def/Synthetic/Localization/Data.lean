module

public import KIP126.Def.Synthetic.Localization.Objects.Predicates
public import Mathlib.CategoryTheory.Adjunction.Reflective

@[expose] public section

/-! The full subcategory of actual λ-invertible objects and explicitly
supplied reflection data. No localization is selected globally.
Source: Pstrągowski, `prop:tau_inversion_functor_exists`.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

/-- The full subcategory cut out by invertibility of the existing λ map. -/
abbrev LambdaInvertibleObjects (Syn : Type u) [SyntheticCategory.{u, v} Syn] :=
  (IsLambdaInvertible (Syn := Syn)).FullSubcategory

/-- The actual full-subcategory inclusion; its object map forgets only the proof. -/
abbrev lambdaInclusion (Syn : Type u) [SyntheticCategory.{u, v} Syn] :
    LambdaInvertibleObjects Syn ⥤ Syn :=
  (IsLambdaInvertible (Syn := Syn)).ι

/-- A left adjoint to the specified inclusion. Its unit and universal
property are determined by this adjunction, not chosen independently. -/
structure LambdaLocalization (Syn : Type u) [SyntheticCategory.{u, v} Syn] where
  reflector : Syn ⥤ LambdaInvertibleObjects Syn
  adjunction : reflector ⊣ lambdaInclusion Syn

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The resulting reflective-subcategory witness, with the same reflector. -/
abbrev LambdaLocalization.reflective (L : LambdaLocalization Syn) :
    Reflective (lambdaInclusion Syn) where
  L := L.reflector
  adj := L.adjunction

/-- Localization viewed as an endofunctor of the ambient synthetic category. -/
def LambdaLocalization.endofunctor (L : LambdaLocalization Syn) : Syn ⥤ Syn :=
  L.reflector ⋙ lambdaInclusion Syn

/-- The unit of this specific adjunction. -/
def LambdaLocalization.unit (L : LambdaLocalization Syn) :
    𝟭 Syn ⟶ L.endofunctor := L.adjunction.unit

/-- The uniquely determined factorization of a map to a λ-invertible object. -/
def LambdaLocalization.lift (L : LambdaLocalization Syn) {X Y : Syn}
    (hY : IsLambdaInvertible Y) (f : X ⟶ Y) : L.endofunctor.obj X ⟶ Y :=
  ((L.adjunction.homEquiv X ⟨Y, hY⟩).symm f).hom

end KIP126.Synthetic.Context
