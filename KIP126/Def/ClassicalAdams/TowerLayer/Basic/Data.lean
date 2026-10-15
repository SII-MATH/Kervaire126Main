module

public import KIP126.Def.ClassicalAdams.Tower.Data

@[expose] public section

/-! Triangles used to compare the chosen tower layers with `H ⊗ Tₛ`.
Inverse rotation uses the negative of the existing positive `fiberι`. -/

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The inverse rotation of the chosen cofiber triangle of a map. -/
def adamsFiberTriangle {X Y : C} (f : X ⟶ Y) : Triangle C :=
  (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)).invRotate

/-- The exact triangle that actually defines an integer-indexed tower layer. -/
def adamsLayerTriangle {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (s : ℤ) : Triangle C :=
  Triangle.mk (adamsTowerMapAt unit X s (s + 1) (by omega))
    (HasFunctorialCofiber.cofibι (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (HasFunctorialCofiber.cofibδ (adamsTowerMapAt unit X s (s + 1) (by omega)))

end KIP126.Classical.Adams
