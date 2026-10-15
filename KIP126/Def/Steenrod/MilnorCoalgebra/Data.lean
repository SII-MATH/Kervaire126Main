module

public import KIP126.Def.Steenrod.MilnorCoalgebra.Operations.Proofs

@[expose] public section

/-!
The fixed, coaugmented Milnor coalgebra in integer-graded F₂ vector spaces.
Its maps are constructed from the polynomial formula; the required laws
remain separate property declarations, not freely supplied operations.
-/

namespace KIP126.Steenrod.Milnor.Coalgebra

noncomputable section
open CategoryTheory MonoidalCategory KIP126.Algebra
  KIP126.Algebra.GradedVectorSpace

/-- The actual full Milnor graded coalgebra, with the prescribed polynomial
coproduct and constant-coefficient counit. -/
def dualSteenrod : Comon (GrVect F2) where
  X := dualSteenrodGraded
  comon :=
    { counit := counit
      comul := comultiplication
      counit_comul := comultiplication_counit_left
      comul_counit := comultiplication_counit_right
      comul_assoc := comultiplication_assoc }

/-- The constant polynomial, as a morphism of actual graded coalgebras. -/
def coaugmentation : Comon.trivial (GrVect F2) ⟶ dualSteenrod :=
  Comon.Hom.mk' coaugmentationMap coaugmentationMap_counit
    coaugmentationMap_comultiplication

end
end KIP126.Steenrod.Milnor.Coalgebra
