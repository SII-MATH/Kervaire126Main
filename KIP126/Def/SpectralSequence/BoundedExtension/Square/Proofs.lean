module

public import KIP126.Def.SpectralSequence.BoundedExtension.Square.Data

@[expose] public section

namespace KIP126.Core.SpectralSequence.BoundedExtension
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem twoTermMap_comm {X₁ X₂ Y₁ Y₂ : C}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (h : a ≫ g = f ≫ b) (k : ℤ) :
    twoTermMap a b k ≫ twoTermDiff Y₁ Y₂ g k =
      twoTermDiff X₁ X₂ f k ≫ twoTermMap a b (k - 1) := by
  by_cases hk : k = 1
  · subst k
    simp [twoTermMap, twoTermDiff]
    rw [← Category.assoc a g, h, Category.assoc]
  · simp [twoTermDiff, hk]

end KIP126.Core.SpectralSequence.BoundedExtension
