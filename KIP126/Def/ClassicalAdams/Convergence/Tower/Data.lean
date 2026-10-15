module

public import KIP126.Def.ClassicalAdams.Convergence.Tower.Raw.Proofs

@[expose] public section

/-! Bundle the specified image filtration on the same spectrum's homotopy. -/

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The Adams filtration of `π_* X`, defined by the actual tower images. -/
noncomputable def adamsHomotopyFiltration : Algebra.Filtration (towerAbutment X) where
  F s n := (ModuleCat.subobjectModule _).symm (adamsHomotopyFiltrationSubmodule unit X s n)
  decreasing s n := (ModuleCat.subobjectModule _).symm.monotone
    (adamsHomotopyFiltrationSubmodule_decreasing unit X s n)

end KIP126.Classical.Adams
