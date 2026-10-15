module

public import KIP126.Def.ClassicalAdams.Tower.Data

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  {H : C} (unit : 𝟙_ C ⟶ H)

theorem adamsUnit_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ adamsUnit unit Y = adamsUnit unit X ≫ H ◁ f := by
  simp only [adamsUnit, ← Category.assoc, leftUnitor_inv_naturality]
  simp only [Category.assoc, whisker_exchange]

end KIP126.Classical.Adams
