module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

@[expose] public section

/-!
Composition for the selected closed structure. These operations are Mathlib's
canonical enriched composition, not additional choices of a pairing. They use
only closed monoidal structure and therefore apply to the stable context
without any universally quantified shift or exactness assumption.
-/

namespace KIP126.StableHomotopy.Mapping

open CategoryTheory MonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The actual internal hom for this chosen closed structure. -/
abbrev object (X Y : C) : C := (ihom X).obj Y

/-- Evaluate the first internal map and then the second, using the associator. -/
abbrev compositionTranspose (X Y Z : C) : X ⊗ (object X Y ⊗ object Y Z) ⟶ Z :=
  MonoidalClosed.compTranspose X Y Z

/-- The adjoint transpose of successive evaluation. -/
abbrev composition (X Y Z : C) : object X Y ⊗ object Y Z ⟶ object X Z :=
  MonoidalClosed.comp X Y Z

/-- The internal identity is the transpose of the right unitor. -/
abbrev identity (X : C) : 𝟙_ C ⟶ object X X := MonoidalClosed.id X

/-- The name of an actual morphism under the same closed adjunction. -/
abbrev name {X Y : C} (f : X ⟶ Y) : 𝟙_ C ⟶ object X Y :=
  MonoidalClosed.curry' f

/-- Names recover actual morphisms, rather than merely specifying unrelated
elements of an internal hom. -/
abbrev nameEquiv (X Y : C) : (X ⟶ Y) ≃ (𝟙_ C ⟶ object X Y) :=
  MonoidalClosed.curryHomEquiv'

/-- Composition of unit-valued points by the actual internal composition. -/
def composeNames {X Y Z : C} (f : 𝟙_ C ⟶ object X Y)
    (g : 𝟙_ C ⟶ object Y Z) : 𝟙_ C ⟶ object X Z :=
  (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ composition X Y Z

end KIP126.StableHomotopy.Mapping
