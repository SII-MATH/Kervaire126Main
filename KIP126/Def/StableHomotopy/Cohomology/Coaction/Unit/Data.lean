module

public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- The actual Adams unit as a natural transformation. Its compatibility
with shifts can now be stated separately as `NatTrans.CommShift`. -/
def mod2UnitNatTrans : 𝟭 C ⟶ tensorLeft H.HF2 where
  app X := adamsUnit H.unit X
  naturality _ _ f := (mod2AdamsUnit_naturality H f).symm

/-- Insert a unit before the existing coefficient factor. This is distinct
from `mod2CoactionMap`, which inserts the unit after that factor. -/
def mod2OuterUnitMap (X : C) (n : ℤ) :
    Mod2Homology H n X →+ Mod2Homology H n (H.HF2 ⊗ X) :=
  inducedMap (adamsUnit H.unit (H.HF2 ⊗ X)) n

end KIP126.StableHomotopy.Cohomology
