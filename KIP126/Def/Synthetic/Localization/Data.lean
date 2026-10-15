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

/-- Localization viewed as an endofunctor of the ambient synthetic category. -/
def LambdaLocalization.endofunctor (L : LambdaLocalization Syn) : Syn ⥤ Syn :=
  L.reflector ⋙ lambdaInclusion Syn

end KIP126.Synthetic.Context
