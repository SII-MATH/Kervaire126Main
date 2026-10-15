module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Data
public import KIP126.Def.ClassicalAdams.Tower.Data

@[expose] public section

/-! The cooperation coaction before Künneth: insert the specified unit into
the middle smash factor. No tensor decomposition of homology is assumed. -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- The spectrum-level map underlying the coefficient coaction. -/
def mod2Coaction (X : C) : H.HF2 ⊗ X ⟶ H.HF2 ⊗ (H.HF2 ⊗ X) :=
  H.HF2 ◁ adamsUnit H.unit X

/-- The coaction on represented homology, prior to a Künneth comparison. -/
def mod2CoactionMap (X : C) (n : ℤ) :
    Mod2Homology H n X →+ Mod2Homology H n (H.HF2 ⊗ X) :=
  inducedMap (mod2Coaction H X) n

end KIP126.StableHomotopy.Cohomology
