module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- Multiplication on the first two factors of the free `H`-object. -/
def mod2FreeAction (X : C) : H.HF2 ⊗ (H.HF2 ⊗ X) ⟶ H.HF2 ⊗ X :=
  (α_ H.HF2 H.HF2 X).inv ≫ R.monoid.mul ▷ X

end KIP126.StableHomotopy.Cohomology
