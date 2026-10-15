module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory BraidedCategory KIP126.Classical.Adams

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

omit [BraidedCategory C] in
/-- The coefficient multiplication sends two unit factors to one unit. -/
theorem mod2Unit_tensor_mul :
    (H.unit ⊗ₘ H.unit) ≫ R.monoid.mul = (λ_ (𝟙_ C)).hom ≫ H.unit := by
  letI := R.monoid
  rw [← R.one_eq]
  simp only [tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality,
    ← unitors_equal]

/-- The coefficient pairing preserves the actual Adams unit insertion.
This is a map-level formula, with no Adams-page multiplication assumed. -/
theorem mod2CoefficientPairing_unit {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    (adamsUnit H.unit X ⊗ₘ adamsUnit H.unit Y) ≫ mod2CoefficientPairing H R f =
      f ≫ adamsUnit H.unit Z := by
  have hunitors :
      ((λ_ X).inv ⊗ₘ (λ_ Y).inv) ≫ tensorμ (𝟙_ C) X (𝟙_ C) Y ≫
        ((λ_ (𝟙_ C)).hom ▷ (X ⊗ Y)) = (λ_ (X ⊗ Y)).inv := by
    apply (cancel_mono (λ_ (X ⊗ Y)).hom).mp
    simp only [Category.assoc]
    rw [← leftUnitor_monoidal, tensorHom_comp_tensorHom]
    simp only [Iso.inv_hom_id, id_tensorHom_id]
  unfold mod2CoefficientPairing adamsUnit
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← tensorHom_id, ← tensorHom_id, tensorμ_natural_assoc]
  rw [tensorHom_comp_tensorHom, mod2Unit_tensor_mul]
  simp only [id_tensorHom_id, Category.id_comp]
  rw [← whiskerRight_comp_tensorHom, ← Category.assoc, ← Category.assoc]
  rw [Category.assoc _ (tensorμ (𝟙_ C) X (𝟙_ C) Y), hunitors,
    leftUnitor_inv_comp_tensorHom]

end KIP126.StableHomotopy.Cohomology
