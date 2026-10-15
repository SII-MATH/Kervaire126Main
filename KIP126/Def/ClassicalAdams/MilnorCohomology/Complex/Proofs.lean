module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Complex.Data
public import KIP126.Def.ClassicalAdams.MilnorCooperations.Proofs

@[expose] public section

/-! The boundary inclusion uses the proved first-page Milnor comparison. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

@[simp] theorem boundaries_zero (t : ℕ) : boundaries 0 t = ⊥ := rfl

include H M in
/-- There is no independent square-zero assumption here: the actual first
Adams differential and the given Milnor coordinates prove this inclusion. -/
theorem boundaries_le_cycles (s t : ℕ) : boundaries s t ≤ cycles s t := by
  cases s with
  | zero => exact bot_le
  | succ s =>
      rintro x ⟨y, rfl⟩
      exact milnor_differential_squared H M s t y

end
end KIP126.Classical.Adams.MilnorCohomology
