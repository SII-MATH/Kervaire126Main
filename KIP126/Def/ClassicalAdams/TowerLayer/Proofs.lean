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

theorem cofiberFiberIso_ι {X Y : C} (f : X ⟶ Y) :
    HasFunctorialCofiber.cofibι (fiberι f) ≫ (cofiberFiberIso f).hom = f := by
  have h := (cofiberFiberTriangleIso f).hom.comm₂
  simpa [cofiberFiberIso, cofiberFiberTriangleIso, adamsFiberTriangle] using h

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

@[simp] theorem adamsE1HomologyEquiv_apply (s : ℕ) (t : ℤ)
    (x : adamsE1 unit X s t) :
    adamsE1HomologyEquiv unit X s t x = x ≫ (adamsLayerIso unit X s).hom := rfl

theorem adamsE1HomologyEquiv_J (s : ℕ) (t : ℤ)
    (x : HomotopyGroup (t - s) (adamsTower unit X s)) :
    adamsE1HomologyEquiv unit X s t (adamsJ unit X s t x) =
      x ≫ adamsUnit unit (adamsTower unit X s) := by
  change (x ≫ _) ≫ _ = _
  rw [Category.assoc, adamsLayerIso_ι]

@[simp] theorem adamsPageOneEquiv_mkQ (s t : ℤ)
    (x : adamsCycles unit X 1 (by decide) s t) :
    adamsPageOneEquiv unit X s t
      ((adamsCycleBoundaries unit X 1 (by decide) s t).mkQ x) = x := rfl

@[simp] theorem adamsPageOneHomologyEquiv_mkQ (s : ℕ) (t : ℤ)
    (x : adamsCycles unit X 1 (by decide) s t) :
    adamsPageOneHomologyEquiv unit X s t
      ((adamsCycleBoundaries unit X 1 (by decide) s t).mkQ x) =
        x.val ≫ (adamsLayerIso unit X s).hom := rfl

end

end KIP126.Classical.Adams
