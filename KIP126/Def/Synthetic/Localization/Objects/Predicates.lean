module

public import KIP126.Def.Synthetic.Context.Data
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-! λ-invertibility of the already specified deformation map.
This is the ordinary categorical property used in the abstract homotopy
background, not a construction of an infinity-category model.
Source: Pstrągowski, `synthetic_spectra.tex`, §τ-invertible synthetic spectra,
definition immediately before `prop:tau_inversion_functor_exists`.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The actual component `λ_X : Σ^(0,-1)X ⟶ X` is invertible. -/
def IsLambdaInvertible : ObjectProperty Syn :=
  fun X => IsIso (SyntheticCategory.lam.app X)

end KIP126.Synthetic.Context
