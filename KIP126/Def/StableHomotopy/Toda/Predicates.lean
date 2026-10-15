module

public import KIP126.Def.StableHomotopy.Context.Data
public import Mathlib.CategoryTheory.Triangulated.Triangulated

@[expose] public section

/-!
# The shifted Toda relation

This is the cone-based relation from the historical
`KIPBase/multiplicativeSS/TriangulatedTodaBracket.lean`, expressed without
importing the historical spectral-sequence model. It is only the relation:
the full Toda-bracket laws and the Moss comparison remain separate work.
-/

namespace KIP126.StableHomotopy.Toda

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- A shifted Toda representative obtained from a distinguished cofiber
triangle for `f`. The extension `gbar` of `g` composes with `h` through the
triangle's connecting map to give `x`. -/
def Relation {X Y Z W : C} (x : X⟦(1 : ℤ)⟧ ⟶ W)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) : Prop :=
  ∃ (Q : C) (i : Y ⟶ Q) (p : Q ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f i p ∈ distTriang C ∧
      ∃ gbar : Q ⟶ Z, i ≫ gbar = g ∧ p ≫ x = gbar ≫ h

end KIP126.StableHomotopy.Toda
