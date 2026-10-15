module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126Main, commit
a966fa8f8ee3f501f1f157b7f55fd4250c2a6359,
KIP126/Def/AdamsSynthetic/Internal/Milnor/Cohomology.lean.
-/

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Data

@[expose] public section

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Every class has an actual normalized cocycle representative. -/
theorem ofCocycle_surjective {s t : ℕ} (z : Cohomology H M s t) :
    ∃ (x : cochains s t) (hx : differential s t x = 0), ofCocycle H M x hx = z := by
  obtain ⟨x, rfl⟩ := (boundariesInCycles H M s t).mkQ_surjective z
  exact ⟨x.val, x.property, rfl⟩

end
end KIP126.Classical.Adams.MilnorCohomology
