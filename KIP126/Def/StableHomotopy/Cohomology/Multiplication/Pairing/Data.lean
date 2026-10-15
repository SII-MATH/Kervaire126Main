module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Data
public import KIP126.Def.ClassicalAdams.Tower.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory BraidedCategory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- Multiply the two coefficient factors and apply a specified map to the
other two factors. Only the chosen ring object and braiding are used. -/
def mod2CoefficientPairing {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    (H.HF2 ⊗ X) ⊗ (H.HF2 ⊗ Y) ⟶ H.HF2 ⊗ Z :=
  tensorμ H.HF2 X H.HF2 Y ≫ (R.monoid.mul ⊗ₘ f)

end KIP126.StableHomotopy.Cohomology
