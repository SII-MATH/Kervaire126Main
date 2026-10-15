module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Data

@[expose] public section

/-! Representative formulas for the descended cobar cohomology product. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Multiplication of specified cocycle classes uses precisely their cobar
concatenation, with no independent choice of a representative. -/
theorem cup_ofCocycle {s t s' t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : IsCycle x) (hy : IsCycle y) :
    cup H M (ofCocycle H M x hx) (ofCocycle H M y hy) =
      ofCocycle H M (KIP126.Steenrod.Milnor.cup x y) (cup_isCycle x y hx hy) := rfl

end
end KIP126.Classical.Adams.MilnorCohomology
