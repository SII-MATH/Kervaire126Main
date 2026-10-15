module

public import KIP126.Def.StableHomotopy.Context.CofiberCoherence.Predicates

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Equal component maps give the same chosen cofiber map, independently of
the proofs used to exhibit their commuting squares. -/
theorem HasFunctorialCofiber.cofibMap_congr {X₁ Y₁ X₂ Y₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    {α α' : X₁ ⟶ X₂} {β β' : Y₁ ⟶ Y₂} (hα : α = α') (hβ : β = β')
    (h : α ≫ f₂ = f₁ ≫ β) (h' : α' ≫ f₂ = f₁ ≫ β') :
    HasFunctorialCofiber.cofibMap f₁ f₂ α β h =
      HasFunctorialCofiber.cofibMap f₁ f₂ α' β' h' := by
  subst α' β'
  rfl

/-- The composition law with the composite square filled by its two given
commutativities, from which the stated cofiber identities follow. -/
theorem FunctorialCofiberCoherence.cofibMap_comp (coh : FunctorialCofiberCoherence C)
    {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (α₁ : X₁ ⟶ X₂) (β₁ : Y₁ ⟶ Y₂) (α₂ : X₂ ⟶ X₃) (β₂ : Y₂ ⟶ Y₃)
    (h₁ : α₁ ≫ f₂ = f₁ ≫ β₁) (h₂ : α₂ ≫ f₃ = f₂ ≫ β₂) :
    HasFunctorialCofiber.cofibMap f₁ f₂ α₁ β₁ h₁ ≫
        HasFunctorialCofiber.cofibMap f₂ f₃ α₂ β₂ h₂ =
      HasFunctorialCofiber.cofibMap f₁ f₃ (α₁ ≫ α₂) (β₁ ≫ β₂)
        (by rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]) :=
  coh.map_comp f₁ f₂ f₃ α₁ β₁ α₂ β₂ h₁ h₂ _

end KIP126.StableHomotopy
