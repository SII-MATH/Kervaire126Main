module

public import KIP126.Def.ClassicalAdams.Convergence.Tower.Raw.Data
public import KIP126.Def.ClassicalAdams.Detection.Proofs

@[expose] public section

/-! The actual images decrease because the tower maps factor through the
preceding level. This property introduces no alternative filtration. -/

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

theorem adamsHomotopyFiltrationSubmodule_decreasing (s n : ℤ) :
    adamsHomotopyFiltrationSubmodule unit X (s + 1) n ≤
      adamsHomotopyFiltrationSubmodule unit X s n := by
  exact TowerDetection.filtrationSubmodule_antitone unit X n (by omega : s ≤ s + 1)

end KIP126.Classical.Adams
