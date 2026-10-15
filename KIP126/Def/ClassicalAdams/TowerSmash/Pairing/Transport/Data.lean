module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Data
public import KIP126.Def.ClassicalAdams.TowerSmash.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- A concrete pairing on the existing sphere tower, transported from
concatenation of the unit-fiber factors. It is not yet a multiplicative
spectral-sequence structure or a comparison with the Lin product. -/
def adamsTowerSpherePairingIso (s t : ℕ) :
    adamsTower unit (𝟙_ C) s ⊗ adamsTower unit (𝟙_ C) t ≅
      adamsTower unit (𝟙_ C) (t + s) :=
  tensorIso (adamsTowerSmashIso unit (𝟙_ C) s) (adamsTowerSmashIso unit (𝟙_ C) t) ≪≫
    adamsSmashSpherePairingIso unit s t ≪≫ (adamsTowerSmashIso unit (𝟙_ C) (t + s)).symm

end
end KIP126.Classical.Adams
