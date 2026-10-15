module

public import KIP126.Def.ClassicalAdams.TowerSmash.Step.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The iterated smash model `bar H ⊗ (bar H ⊗ ... ⊗ X)`, with s factors.
It is a comparison model for the existing tower, not a replacement SSData. -/
def adamsSmashTower : ℕ → C
  | 0 => X
  | s + 1 => fiber unit ⊗ adamsSmashTower s

/-- Remove the outer unit-fiber factor using its actual fiber inclusion. -/
def adamsSmashTowerStep (s : ℕ) :
    adamsSmashTower unit X (s + 1) ⟶ adamsSmashTower unit X s :=
  (fiberι unit ▷ adamsSmashTower unit X s) ≫ (λ_ _).hom

/-- Composite transitions in the iterated smash model. -/
def adamsSmashTowerComposite (s : ℕ) :
    (length : ℕ) → (adamsSmashTower unit X (s + length) ⟶ adamsSmashTower unit X s)
  | 0 => 𝟙 _
  | length + 1 =>
      adamsSmashTowerStep unit X (s + length) ≫ adamsSmashTowerComposite s length

variable [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Recursively compare the existing iterated-fiber Adams tower with smash
powers of the unit fiber. Every one-step comparison comes from exactness. -/
def adamsTowerSmashIso : (s : ℕ) → adamsTower unit X s ≅ adamsSmashTower unit X s
  | 0 => Iso.refl _
  | s + 1 => adamsFiberTensorIso unit (adamsTower unit X s) ≪≫
      (tensorLeft (fiber unit)).mapIso (adamsTowerSmashIso s)

end
end KIP126.Classical.Adams
