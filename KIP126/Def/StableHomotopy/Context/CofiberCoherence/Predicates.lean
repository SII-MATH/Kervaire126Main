module

public import KIP126.Def.StableHomotopy.Context.Data

@[expose] public section

/-! Functoriality conditions on the already chosen cofiber maps.
The minimal cofiber class only supplies the inclusion and boundary squares;
these equations are additional, explicit model conditions, not new choices.
No exactness of a suspension functor or octahedral compatibility is asserted.
-/

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

variable (C : Type u) [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Identity and composition for the specified `cofibMap` operation.
The commuting-square proofs are explicit and proof irrelevant. -/
structure FunctorialCofiberCoherence : Prop where
  map_id : ∀ {X Y : C} (f : X ⟶ Y) (h : 𝟙 X ≫ f = f ≫ 𝟙 Y),
    HasFunctorialCofiber.cofibMap f f (𝟙 X) (𝟙 Y) h =
      𝟙 (HasFunctorialCofiber.cofib f)
  map_comp : ∀ {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
      (α₁ : X₁ ⟶ X₂) (β₁ : Y₁ ⟶ Y₂) (α₂ : X₂ ⟶ X₃) (β₂ : Y₂ ⟶ Y₃)
      (h₁ : α₁ ≫ f₂ = f₁ ≫ β₁) (h₂ : α₂ ≫ f₃ = f₂ ≫ β₂)
      (h₁₂ : (α₁ ≫ α₂) ≫ f₃ = f₁ ≫ (β₁ ≫ β₂)),
    HasFunctorialCofiber.cofibMap f₁ f₂ α₁ β₁ h₁ ≫
        HasFunctorialCofiber.cofibMap f₂ f₃ α₂ β₂ h₂ =
      HasFunctorialCofiber.cofibMap f₁ f₃ (α₁ ≫ α₂) (β₁ ≫ β₂) h₁₂

end KIP126.StableHomotopy
