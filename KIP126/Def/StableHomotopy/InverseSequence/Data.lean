module

public import KIP126.Def.StableHomotopy.Context.Data
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

/-!
# Sequential homotopy limits in the stable background

The homotopy limit is specified by the Milnor distinguished triangle for
`1 - shift` on the countable product. This is not a categorical limit of
the inverse sequence in the ordinary homotopy category. In particular,
the triangle retains the derived-limit contribution to mapping groups.

Only the adjacent arrows are needed: they generate the sequential diagram.
No full model of an infinity-category is constructed here.
-/

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable (C : Type u) [Category.{v} C]

/-- An inverse sequence given by its actual adjacent maps. -/
structure InverseSequence where
  obj : ℕ → C
  step : ∀ n, obj (n + 1) ⟶ obj n

variable {C}

/-- Apply a functor to the objects and actual adjacent maps of a sequence. -/
def InverseSequence.map (D : InverseSequence C) (F : C ⥤ C) : InverseSequence C where
  obj := fun n => F.obj (D.obj n)
  step := fun n => F.map (D.step n)

variable [HasProductsOfShape ℕ C]

/-- The endomorphism whose `n`th projection is the `(n+1)`st projection
followed by the actual transition map. -/
noncomputable def InverseSequence.shiftMap (D : InverseSequence C) :
    ∏ᶜ D.obj ⟶ ∏ᶜ D.obj :=
  Pi.lift (fun n => Pi.π D.obj (n + 1) ≫ D.step n)

/-- The map defining a sequential homotopy limit by its fiber. -/
noncomputable def InverseSequence.oneSubShift [Preadditive C] (D : InverseSequence C) :
    ∏ᶜ D.obj ⟶ ∏ᶜ D.obj :=
  𝟙 _ - D.shiftMap

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A Milnor triangle exhibiting the specified vertex `L` as the
sequential homotopy limit. The first arrow, not just the object, is data. -/
structure SequentialHomotopyLimit (D : InverseSequence C) (L : C) where
  toProduct : L ⟶ ∏ᶜ D.obj
  boundary : ∏ᶜ D.obj ⟶ L⟦(1 : ℤ)⟧
  distinguished :
    Triangle.mk toProduct D.oneSubShift boundary ∈ distTriang C

/-- The projections belonging to this specific homotopy-limit witness. -/
noncomputable def SequentialHomotopyLimit.π {D : InverseSequence C} {L : C}
    (H : SequentialHomotopyLimit D L) (n : ℕ) : L ⟶ D.obj n :=
  H.toProduct ≫ Pi.π D.obj n

end KIP126.StableHomotopy
