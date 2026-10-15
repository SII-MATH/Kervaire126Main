module

public import KIP126.Def.ClassicalAdams.TowerLayer.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

variable {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Under the layer comparison, the tower-to-layer map is exactly the unit. -/
theorem adamsLayerIso_ι (s : ℕ) :
    HasFunctorialCofiber.cofibι (adamsTowerMapAt unit X s ((s : ℤ) + 1) (by omega)) ≫
      (adamsLayerIso unit X s).hom = adamsUnit unit (adamsTower unit X s) := by
  have h := (adamsLayerTriangleIso unit X s).hom.comm₂
  simpa [adamsLayerIso, adamsLayerTriangleIso, adamsFiberTriangle, adamsLayerTriangle] using h

/-- The connecting map comparison includes the sign forced by the positive
fiber inclusion. This is not an object-only comparison. -/
theorem adamsLayerIso_δ (s : ℕ) :
    HasFunctorialCofiber.cofibδ (adamsTowerMapAt unit X s ((s : ℤ) + 1) (by omega)) =
      -((adamsLayerIso unit X s).hom ≫
        (adamsFiberTriangle (adamsUnit unit (adamsTower unit X s))).mor₃) := by
  have h := (adamsLayerTriangleIso unit X s).hom.comm₃
  have h' : -(HasFunctorialCofiber.cofibδ
      (adamsTowerMapAt unit X s ((s : ℤ) + 1) (by omega))) =
        (adamsLayerIso unit X s).hom ≫
          (adamsFiberTriangle (adamsUnit unit (adamsTower unit X s))).mor₃ := by
    simpa [adamsLayerIso, adamsLayerTriangleIso, adamsLayerTriangle] using h
  exact neg_eq_iff_eq_neg.mp h'

end

end KIP126.Classical.Adams
