module

public import KIP126.Def.ClassicalAdams.TowerFiltration.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Forgetting the redundant `Z₂` membership identifies internal stage-`n`
cycle representatives with the tower's classical `(n + 2)`-cycles. -/
def adamsFiniteCycleEquiv (s t : ℤ) (n : ℕ) :
    adamsFiniteCycleSubmodule unit X s t n ≃ₗ[ℤ]
      adamsCycles unit X (n + 2) (by omega) s t where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, adamsCycles_le_of_le unit X s t 2 (n + 2)
    (by omega) (by omega) (by omega) x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end KIP126.Classical.Adams
