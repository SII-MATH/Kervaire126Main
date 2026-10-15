module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Proofs
public import Mathlib.CategoryTheory.Monoidal.Preadditive

@[expose] public section

/-! Mod-two scalar structures derived from the specified H-ring and additive tensor.
No page, differential, scalar action, or Milnor coordinates are postulated. -/

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- The specified unit is of additive order dividing two, from its π₀ coordinate. -/
theorem mod2Unit_add_self : H.unit + H.unit = 0 := by
  have h : H.pi0Equiv.symm 1 + H.pi0Equiv.symm 1 = 0 := by
    apply H.pi0Equiv.injective
    simp only [map_add, AddEquiv.apply_symm_apply, map_zero]
    decide
  simp only [Mod2EilenbergMacLane.unit, ← Preadditive.comp_add, h, Limits.comp_zero]

variable [MonoidalPreadditive C] (R : Mod2RingStructure H)

/-- Tensor additivity transports the unit's characteristic-two relation. -/
theorem adamsUnit_add_self (X : C) : adamsUnit H.unit X + adamsUnit H.unit X = 0 := by
  simp only [adamsUnit, ← Preadditive.comp_add, ← MonoidalPreadditive.add_whiskerRight,
    mod2Unit_add_self, MonoidalPreadditive.zero_whiskerRight, Limits.comp_zero]

include R in
/-- The ring unit law forces the identity of H to have additive order dividing two. -/
theorem mod2_id_add_self : (𝟙 H.HF2) + 𝟙 H.HF2 = 0 := by
  rw [← adamsUnit_mul H R, ← Preadditive.add_comp, adamsUnit_add_self, Limits.zero_comp]

include R in
/-- Every free H-object has characteristic-two endomorphism identity. -/
theorem mod2Free_id_add_self (X : C) : (𝟙 (H.HF2 ⊗ X)) + 𝟙 (H.HF2 ⊗ X) = 0 := by
  have h := congrArg (fun f : H.HF2 ⟶ H.HF2 => f ▷ X) (mod2_id_add_self H R)
  simpa only [MonoidalPreadditive.add_whiskerRight, id_whiskerRight,
    MonoidalPreadditive.zero_whiskerRight] using h

include R in
/-- Coefficient-homology classes are killed by doubling. -/
theorem mod2Homology_add_self (n : ℤ) (X : C) (x : Mod2Homology H n X) : x + x = 0 := by
  calc
    x + x = x ≫ (𝟙 (H.HF2 ⊗ X) + 𝟙 (H.HF2 ⊗ X)) := by simp [Preadditive.comp_add]
    _ = 0 := by rw [mod2Free_id_add_self H R, Limits.comp_zero]

include R in
/-- The torsion witness used to construct the mod-two scalar action. -/
theorem mod2Homology_two_nsmul_zero (n : ℤ) (X : C) (x : Mod2Homology H n X) : 2 • x = 0 := by
  simpa only [two_nsmul] using mod2Homology_add_self H R n X x

include R in
/-- Represented cohomology is also killed by doubling. -/
theorem mod2Cohomology_two_nsmul_zero (n : ℤ) (X : C) (x : Mod2Cohomology H n X) : 2 • x = 0 := by
  rw [two_nsmul]
  calc
    x + x = x ≫ (𝟙 H.HF2 + 𝟙 H.HF2) := by simp [Preadditive.comp_add]
    _ = 0 := by rw [mod2_id_add_self H R, Limits.comp_zero]

include R in
/-- The coefficient spectrum's actual homotopy groups retain their homological
index. In particular this theorem does not identify πₙHF₂ with Hⁿ(S⁰). -/
theorem mod2HF2Homotopy_two_nsmul_zero (n : ℤ)
    (x : HomotopyGroup n H.HF2) : 2 • x = 0 := by
  rw [two_nsmul]
  calc
    x + x = x ≫ (𝟙 H.HF2 + 𝟙 H.HF2) := by simp [Preadditive.comp_add]
    _ = 0 := by rw [mod2_id_add_self H R, Limits.comp_zero]

end

end KIP126.StableHomotopy.Cohomology
