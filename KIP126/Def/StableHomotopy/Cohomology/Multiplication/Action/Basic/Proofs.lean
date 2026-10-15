module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Data
public import KIP126.Def.ClassicalAdams.Tower.Data

@[expose] public section

/-! The free-action unit law does not require Adams pages or tower exactness. -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- After smashing with `H`, the Adams unit has an explicit retraction. -/
theorem mod2FreeAction_unit (X : C) :
    H.HF2 ◁ adamsUnit H.unit X ≫ mod2FreeAction H R X = 𝟙 _ := by
  letI := R.monoid
  simp only [adamsUnit, mod2FreeAction, whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight, ← R.one_eq,
    MonObj.mul_one, triangle_assoc_comp_right]
  rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]

end KIP126.StableHomotopy.Cohomology
