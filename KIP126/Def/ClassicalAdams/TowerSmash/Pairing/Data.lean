module

public import KIP126.Def.ClassicalAdams.TowerSmash.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

/-- Reassociate the s unit-fiber factors and remove the terminal sphere unit. -/
def adamsSmashSphereTensorIso (Y : C) : (s : ℕ) →
    adamsSmashTower unit (𝟙_ C) s ⊗ Y ≅ adamsSmashTower unit Y s
  | 0 => λ_ Y
  | s + 1 => (α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s) Y) ≪≫
      (tensorLeft (fiber unit)).mapIso (adamsSmashSphereTensorIso Y s)

/-- Flatten nested smash powers. The order `t+s` makes recursion in the
outer number of factors definitionally compatible with the target tower. -/
def adamsSmashTowerNestingIso (X : C) (t : ℕ) : (s : ℕ) →
    adamsSmashTower unit (adamsSmashTower unit X t) s ≅
      adamsSmashTower unit X (t + s)
  | 0 => Iso.refl _
  | s + 1 => (tensorLeft (fiber unit)).mapIso (adamsSmashTowerNestingIso X t s)

/-- Concatenate the factors of two sphere stages. The sum is written `t+s`.
This is a concrete pairing map; both transition laws and multiplicative
spectral-sequence compatibility are separate proof obligations. -/
def adamsSmashSpherePairingIso (s t : ℕ) :
    adamsSmashTower unit (𝟙_ C) s ⊗ adamsSmashTower unit (𝟙_ C) t ≅
      adamsSmashTower unit (𝟙_ C) (t + s) :=
  adamsSmashSphereTensorIso unit (adamsSmashTower unit (𝟙_ C) t) s ≪≫
    adamsSmashTowerNestingIso unit (𝟙_ C) t s

end
end KIP126.Classical.Adams
