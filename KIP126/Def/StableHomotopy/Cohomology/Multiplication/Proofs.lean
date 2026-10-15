module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Data
public import KIP126.Def.ClassicalAdams.Tower.Data

@[expose] public section

/-! # Unit and multiplication identities used by the Adams comparison -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The Adams unit on `H` is split by its multiplication. -/
theorem adamsUnit_mul : adamsUnit H.unit H.HF2 ≫ R.monoid.mul = 𝟙 H.HF2 := by
  letI := R.monoid
  simp only [adamsUnit, Category.assoc, ← R.one_eq, MonObj.one_mul, Iso.inv_hom_id]

end KIP126.StableHomotopy.Cohomology
