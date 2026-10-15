module

public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- The free action also retracts outer unit insertion, by the left unit law. -/
theorem mod2FreeAction_outerUnit (R : Mod2RingStructure H) (X : C) :
    adamsUnit H.unit (H.HF2 ⊗ X) ≫ mod2FreeAction H R X = 𝟙 _ := by
  letI := R.monoid
  simp only [adamsUnit, mod2FreeAction, Category.assoc,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight, ← R.one_eq,
    MonObj.one_mul, ← leftUnitor_tensor_hom, Iso.inv_hom_id]

variable [(tensorLeft H.HF2).CommShift ℤ] [(mod2UnitNatTrans H).CommShift ℤ]

/-- Spell out the exact unit/shift coherence used in the boundary comparison.
It is not inferred merely from a shift structure on the tensor functor. -/
theorem mod2Unit_shift (X : C) (n : ℤ) :
    adamsUnit H.unit (X⟦n⟧) ≫ ((tensorLeft H.HF2).commShiftIso n).hom.app X =
      (adamsUnit H.unit X)⟦n⟧' := by
  have h := (NatTrans.shift_app_comm (mod2UnitNatTrans H) n X).symm
  rw [Functor.commShiftIso_id_hom_app] at h
  change adamsUnit H.unit (X⟦n⟧) ≫ ((tensorLeft H.HF2).commShiftIso n).hom.app X =
    𝟙 (X⟦n⟧) ≫ (adamsUnit H.unit X)⟦n⟧' at h
  simpa only [Category.id_comp] using h

end KIP126.StableHomotopy.Cohomology
