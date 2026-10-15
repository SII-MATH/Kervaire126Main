module

public import KIP126.Def.ClassicalAdams.TowerLayer.Data

@[expose] public section

/-! Coefficient-homology resolution maps constructed directly from the Adams
unit and its chosen cofiber. No first-page coordinates are assumed. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
  KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The boundary of the unit fiber triangle, with the sign dictated by the
positive `fiberι` convention. Defined before any page differential comparison. -/
def adamsResolutionConnecting (s : ℕ) :
    H ⊗ adamsTower unit X s ⟶ (adamsTower unit X (s + 1))⟦(1 : ℤ)⟧ :=
  -(adamsFiberTriangle (adamsUnit unit (adamsTower unit X s))).mor₃

/-- The unit fiber triangle with the positive tower inclusion convention. -/
def adamsResolutionTriangle (s : ℕ) : Triangle C :=
  Triangle.mk (adamsTowerStep unit X s)
    (adamsUnit unit (adamsTower unit X s)) (adamsResolutionConnecting unit X s)

end

end KIP126.Classical.Adams
