module

public import KIP126.Def.ClassicalAdams.TowerSmash.Step.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  (X : C) [(tensorRight X).CommShift ℤ] [(tensorRight X).IsTriangulated]

@[simp] theorem adamsTensorFiberTriangleIso_hom₂ :
    (adamsTensorFiberTriangleIso unit X).hom.hom₂ = (λ_ X).hom := by
  simp [adamsTensorFiberTriangleIso, invRotate, adamsFiberTriangle, Triangle.invRotate,
    Triangle.mk]
  change 𝟙 (𝟙_ C ⊗ X) ≫ (λ_ X).hom ≫ 𝟙 X = (λ_ X).hom
  simp only [Category.id_comp, Category.comp_id]

@[simp] theorem adamsTensorFiberTriangleIso_hom₃ :
    (adamsTensorFiberTriangleIso unit X).hom.hom₃ = 𝟙 (H ⊗ X) := by
  simp [adamsTensorFiberTriangleIso, invRotate, rotate, adamsFiberTriangle,
    Triangle.invRotate, Triangle.rotate, Triangle.mk]
  change 𝟙 (H ⊗ X) ≫ 𝟙 (H ⊗ X) = 𝟙 (H ⊗ X)
  exact Category.id_comp _

/-- The full triangle comparison also retains the actual connecting map,
including the exact functor's suspension comparison. -/
theorem adamsFiberTensorIso_inv_δ :
    (tensorRight X).map (adamsFiberTriangle unit).mor₃ ≫
        (Functor.commShiftIso (tensorRight X) (1 : ℤ)).hom.app (fiber unit) ≫
        (adamsFiberTensorIso unit X).inv⟦(1 : ℤ)⟧' =
      (adamsFiberTriangle (adamsUnit unit X)).mor₃ := by
  have h := (adamsTensorFiberTriangleIso unit X).hom.comm₃
  rw [adamsTensorFiberTriangleIso_hom₃] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.id_comp _))

variable [MonoidalPreadditive C]

/-- The object comparison intertwines the actual positive fiber inclusion
with the smashed inclusion; the inverse-rotation signs cancel. -/
theorem adamsFiberTensorIso_inv_ι :
    (adamsFiberTensorIso unit X).inv ≫ fiberι (adamsUnit unit X) =
      (fiberι unit ▷ X) ≫ (λ_ X).hom := by
  have h := (adamsTensorFiberTriangleIso unit X).hom.comm₁
  change (tensorRight X).map (adamsFiberTriangle unit).mor₁ ≫
    (adamsTensorFiberTriangleIso unit X).hom.hom₂ =
      (adamsFiberTensorIso unit X).inv ≫ (adamsFiberTriangle (adamsUnit unit X)).mor₁ at h
  rw [adamsTensorFiberTriangleIso_hom₂, adamsFiberTriangle_mor₁,
    adamsFiberTriangle_mor₁] at h
  change (tensorRight X).map (-fiberι unit) ≫ (λ_ X).hom =
    (adamsFiberTensorIso unit X).inv ≫ (-fiberι (adamsUnit unit X)) at h
  simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg] at h
  exact (neg_inj.mp h).symm

theorem adamsFiberTensorIso_hom_ι :
    (adamsFiberTensorIso unit X).hom ≫ (fiberι unit ▷ X) ≫ (λ_ X).hom =
      fiberι (adamsUnit unit X) := by
  rw [← adamsFiberTensorIso_inv_ι, Iso.hom_inv_id_assoc]

end
end KIP126.Classical.Adams
