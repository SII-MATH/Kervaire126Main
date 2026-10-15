module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)

/-- The remaining below-page coproduct comparison, tested only on the
given reduced basis. The left side uses actual middle-unit insertion and
Künneth; the right side uses the existing Milnor polynomial formula.
No value for this predicate is postulated for the fixed sphere foundation. -/
def Mod2MilnorCoproductCompatible : Prop :=
  ∀ n (d : PositiveMonomial n),
    cooperationTensorMilnorPolynomial H R B n
      (cooperationTensorDiagonal H R K n ((B.basis n) d).val) =
    splitSlot (0 : Fin 1)
      (milnorMonomialPolynomial (⟨d.val, d.property.1⟩ : MilnorMonomial n))

end KIP126.StableHomotopy.Cohomology
