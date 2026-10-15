module

public import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs
public import Mathlib.CategoryTheory.Monoidal.Preadditive

@[expose] public section

/-! One Adams fiber step compared with smashing by the unit's fiber.
The comparison is built from exact triangles; it is not an extra chosen
cofiber/tensor comparison axiom. -/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  (X : C) [(tensorRight X).CommShift ℤ] [(tensorRight X).IsTriangulated]

/-- Compare the entire smashed fiber triangle with the defining Adams fiber
triangle. The components on `𝟙 ⊗ X` and `H ⊗ X` are the unitor and identity. -/
def adamsTensorFiberTriangleIso :
    (tensorRight X).mapTriangle.obj (adamsFiberTriangle unit) ≅
      adamsFiberTriangle (adamsUnit unit X) :=
  (rotCompInvRot.app _ : _ ≅ _ ) ≪≫
    (invRotate C).mapIso
      (isoTriangleOfIso₁₂ _ _
        (rot_of_distTriang _ ((tensorRight X).map_distinguished _
          (adamsFiberTriangle_distinguished unit)))
        (rot_of_distTriang _ (adamsFiberTriangle_distinguished (adamsUnit unit X)))
        (λ_ X) (Iso.refl _) (by
          change (unit ▷ X) ≫ 𝟙 _ = (λ_ X).hom ≫ adamsUnit unit X
          simp only [adamsUnit, Iso.hom_inv_id_assoc, Category.comp_id])) ≪≫
    (rotCompInvRot.app _).symm

/-- The actual fiber of `X → H ⊗ X` is the tensor of the unit fiber with X. -/
def adamsFiberTensorIso : fiber (adamsUnit unit X) ≅ fiber unit ⊗ X :=
  (Triangle.π₁.mapIso (adamsTensorFiberTriangleIso unit X)).symm

end
end KIP126.Classical.Adams
