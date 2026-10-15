module

public import KIP126.Def.ClassicalAdams.Moss.Convergence.Data

@[expose] public section

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- Moss's residual-injectivity condition, now on the constructed mapping
tower. A graded E∞ identification alone does not imply this condition. -/
def MappingAdamsTower (X Y : C) : Prop :=
  ∀ (s : ℕ) (n : ℤ) (f : HomotopyGroup n (mappingStage unit X Y (s + 1))),
    (∀ (t : ℕ) (hst : s + 1 ≤ t),
      ∃ g : HomotopyGroup n (mappingStage unit X Y t),
        g ≫ mappingRestrict unit X Y (s + 1) t hst = f) →
    f ≫ mappingRestrict unit X Y s (s + 1) (Nat.le_succ s) = 0 → f = 0

end KIP126.Classical.Adams.Moss
