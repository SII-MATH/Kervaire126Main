module

public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Data

@[expose] public section

/-! Derived F₂ scalars preserve the represented groups and their original maps. -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

@[simp] theorem cooperationCounitF2_apply (n : ℤ) (x : Mod2Cooperations H n) :
    cooperationCounitF2 H R n x = cooperationCounit H R n x := rfl

end KIP126.StableHomotopy.Cohomology
