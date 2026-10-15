module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

/-!
# Stable homotopy categories and their structure

A stable homotopy category carries additive, shifted, monoidal and
triangulated structures. Functorial cofibers and a closed structure are
recorded separately. The final `StableHomotopyContext` record specifies the
objects and maps required by the classical Adams construction.
-/

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

/-- The structural part of a stable homotopy category.

The fields are bundled so a concrete model can supply its additive, shifted,
monoidal, and triangulated structures together.  In particular, this class
does not assert the extra closedness, cofiber choices, or sign conventions
used by particular constructions; those belong to separate witness records.
-/
class StableHomotopyCategory (C : Type u) extends
    Category.{v} C,
    Preadditive C,
    HasShift C ℤ,
    MonoidalCategory C where
  /-- Every shift functor is additive. -/
  shiftAdditive : ∀ (n : ℤ), (shiftFunctor C n).Additive
  /-- The category has a zero object. -/
  hasZeroObject : HasZeroObject C
  /-- The category is pretriangulated. -/
  pretriangulated : Pretriangulated C

attribute [instance] StableHomotopyCategory.shiftAdditive
attribute [instance] StableHomotopyCategory.hasZeroObject
attribute [reducible] StableHomotopyCategory.pretriangulated
attribute [instance] StableHomotopyCategory.pretriangulated

/-! ### Explicit cofiber and tensor-triangulated witnesses -/

section CofiberChoices

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Chosen cofiber triangles and completions of commuting squares in a
pretriangulated category.

This is data supplied by a concrete model.  Keeping it as a class preserves
the convenient Mathlib notation without introducing a global postulate that
would silently choose a cofiber for every map.
The fields select triangle completions of commuting squares; they do not
require identity or composition laws for those choices.
-/
class HasFunctorialCofiber where
  cofib : {X Y : C} → (X ⟶ Y) → C
  cofibι : {X Y : C} → (f : X ⟶ Y) → Y ⟶ cofib f
  cofibδ : {X Y : C} → (f : X ⟶ Y) → cofib f ⟶ (shiftFunctor C (1 : ℤ)).obj X
  cofib_distinguished : ∀ {X Y : C} (f : X ⟶ Y),
    Triangle.mk f (cofibι f) (cofibδ f) ∈ distTriang C
  cofibMap : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂), α ≫ f₂ = f₁ ≫ β →
    (cofib f₁ ⟶ cofib f₂)
  cofibMap_ι : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    β ≫ cofibι f₂ = cofibι f₁ ≫ cofibMap f₁ f₂ α β h
  cofibMap_δ : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    cofibMap f₁ f₂ α β h ≫ cofibδ f₂ =
      cofibδ f₁ ≫ (shiftFunctor C (1 : ℤ)).map α

end CofiberChoices

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The sphere spectrum is the monoidal unit. -/
abbrev SphereSpectrum : C := 𝟙_ C

/-- The `n`-sphere is the `n`-fold shift of the sphere spectrum. -/
abbrev Sphere (n : ℤ) : C := (shiftFunctor C n).obj SphereSpectrum

/-- Stable homotopy classes represented by maps from the `n`-sphere. -/
abbrev HomotopyGroup (n : ℤ) (X : C) : Type v := Sphere n ⟶ X

/-! ### Distinguished cofiber triangles and induced maps -/

/-- A chosen distinguished triangle `X → Y → Z → ΣX`. -/
structure HoCofiberSequence where
  X : C
  Y : C
  Z : C
  f : X ⟶ Y
  g : Y ⟶ Z
  h : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X
  distinguished : Triangle.mk f g h ∈ distTriang C

/-- The map on homotopy groups induced by postcomposition with `f`. -/
def inducedMap {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    HomotopyGroup n X →+ HomotopyGroup n Y where
  toFun := fun α => α ≫ f
  map_zero' := Limits.zero_comp
  map_add' := fun a b => Preadditive.add_comp _ _ _ a b f

end KIP126.StableHomotopy
