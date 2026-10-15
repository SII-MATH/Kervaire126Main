module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Basic.Proofs
public import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs

@[expose] public section

/-! Adams tower transitions are `H`-homology-zero. The structural inputs are
an actual multiplication with the specified unit and preservation of zero
morphisms by `H ⊗ -`. They are arguments, not new global axioms. -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

variable [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).PreservesZeroMorphisms]

include R in
theorem mod2_fiberι_eq_zero (X : C) :
    H.HF2 ◁ fiberι (adamsUnit H.unit X) = 0 := by
  calc
    H.HF2 ◁ fiberι (adamsUnit H.unit X) =
        H.HF2 ◁ fiberι (adamsUnit H.unit X) ≫
          (H.HF2 ◁ adamsUnit H.unit X ≫ mod2FreeAction H R X) := by
            rw [mod2FreeAction_unit, Category.comp_id]
    _ = H.HF2 ◁ (fiberι (adamsUnit H.unit X) ≫ adamsUnit H.unit X) ≫
        mod2FreeAction H R X := by simp only [whiskerLeft_comp, Category.assoc]
    _ = 0 := by
      rw [fiberι_comp_eq_zero]
      change (tensorLeft H.HF2).map 0 ≫ _ = 0
      rw [Functor.map_zero, Limits.zero_comp]

include R in
theorem mod2_adamsTowerStep_eq_zero (X : C) (s : ℕ) :
    H.HF2 ◁ adamsTowerStep H.unit X s = 0 :=
  mod2_fiberι_eq_zero H R (adamsTower H.unit X s)

include R in
theorem mod2_adamsTowerStep_homology_eq_zero (X : C) (s : ℕ) (n : ℤ) :
    Mod2Homology.pushforward H (adamsTowerStep H.unit X s) n = 0 := by
  ext x
  change x ≫ (H.HF2 ◁ adamsTowerStep H.unit X s) = 0
  rw [mod2_adamsTowerStep_eq_zero H R, Limits.comp_zero]

include R in
/-- Every strictly descending map of the natural-indexed tower is killed by `H ⊗ -`. -/
theorem mod2_adamsTowerMap_eq_zero (X : C) (s t : ℕ) (hst : s < t) :
    H.HF2 ◁ adamsTowerMap H.unit X s t hst.le = 0 := by
  cases t with
  | zero => omega
  | succ t =>
    rw [adamsTowerMap_succ H.unit X s t (by omega), whiskerLeft_comp,
      mod2_adamsTowerStep_eq_zero H R, Limits.zero_comp]

include R in
/-- The homological consequence of positive Adams filtration, stated using
an actual lift through a positive tower stage rather than an unrelated
numerical filtration oracle. -/
theorem mod2_homology_eq_zero_of_tower_lift {X Y : C} (f : X ⟶ Y)
    (s : ℕ) (hs : 0 < s) (lift : X ⟶ adamsTower H.unit Y s)
    (hlift : lift ≫ adamsTowerMap H.unit Y 0 s (Nat.zero_le s) = f) (n : ℤ) :
    Mod2Homology.pushforward H f n = 0 := by
  ext x
  change x ≫ (H.HF2 ◁ f) = 0
  rw [← hlift, whiskerLeft_comp, mod2_adamsTowerMap_eq_zero H R Y 0 s hs,
    Limits.comp_zero, Limits.comp_zero]

end KIP126.StableHomotopy.Cohomology
