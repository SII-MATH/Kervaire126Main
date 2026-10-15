module

public import KIP126.Def.ClassicalAdams.Detection.Data

@[expose] public section
namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
theorem filtrationSubmodule_antitone (n : ℤ) :
    Antitone (fun s => filtrationSubmodule unit X s n) := by
  intro s t hst x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y ≫ adamsTowerMap unit X s.toNat t.toNat (by omega), ?_⟩
  change (y ≫ adamsTowerMap unit X s.toNat t.toNat _) ≫
    adamsTowerMap unit X 0 s.toNat _ = x
  rw [Category.assoc, adamsTowerMap_comp]
  exact hy
end KIP126.Classical.Adams.TowerDetection
