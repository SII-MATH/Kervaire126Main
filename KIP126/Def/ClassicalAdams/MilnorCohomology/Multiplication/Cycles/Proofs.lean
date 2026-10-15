module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Cycles.Data
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Proofs

@[expose] public section

/-! Concatenation with a cycle preserves the actual incoming boundaries. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

theorem reindex_mem_boundaries_iff {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
    (x : cochains s t) : reindex hs ht x ∈ boundaries s' t' ↔ x ∈ boundaries s t := by
  subst s'
  subst t'
  rfl

/-- A boundary times a cycle is a boundary. At degree zero, the boundary
is zero; at positive degree its primitive is concatenated with the cycle. -/
theorem cup_boundary_cycle {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : x ∈ boundaries s t) (hy : IsCycle y) :
    cup x y ∈ boundaries (s + s') (t + t') := by
  cases s with
  | zero =>
      have hx0 : x = 0 := hx
      rw [hx0, cup_zero_left]
      exact Submodule.zero_mem _
  | succ s =>
      obtain ⟨b, rfl⟩ := hx
      have hd : differential (s + s') (t + t') (cup b y) =
          reindex (by omega) rfl (cup (differential s t b) y) := by
        rw [differential_cup, hy, cup_zero_right, map_zero, add_zero]
      apply (reindex_mem_boundaries_iff (by omega : (s + 1) + s' = (s + s') + 1)
        rfl _).mp
      exact ⟨cup b y, hd⟩

/-- A cycle times a boundary is a boundary, including the zero incoming
boundary module in degree zero. -/
theorem cup_cycle_boundary {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : IsCycle x) (hy : y ∈ boundaries s' t') :
    cup x y ∈ boundaries (s + s') (t + t') := by
  cases s' with
  | zero =>
      have hy0 : y = 0 := hy
      rw [hy0, cup_zero_right]
      exact Submodule.zero_mem _
  | succ s' =>
      obtain ⟨b, rfl⟩ := hy
      have hd : differential (s + s') (t + t') (cup x b) =
          reindex (by omega) rfl (cup x (differential s' t' b)) := by
        rw [differential_cup, hx, cup_zero_left, map_zero, zero_add]
      apply (reindex_mem_boundaries_iff (by omega : s + (s' + 1) = (s + s') + 1)
        rfl _).mp
      exact ⟨cup x b, hd⟩

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

theorem boundaries_le_cycleCupClass_ker (s t s' t' : ℕ) :
    boundariesInCycles H M s t ≤ (cycleCupClass H M s t s' t').ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  apply (classOf_eq_zero_iff H M _).mpr
  exact cup_boundary_cycle x.val y.val ((mem_boundariesInCycles H M x).mp hx) y.property

theorem boundaries_le_cycleCupClass_flip_ker (s t s' t' : ℕ) :
    boundariesInCycles H M s' t' ≤ (cycleCupClass H M s t s' t').flip.ker := by
  intro y hy
  apply LinearMap.ext
  intro x
  apply (classOf_eq_zero_iff H M _).mpr
  exact cup_cycle_boundary x.val y.val x.property ((mem_boundariesInCycles H M y).mp hy)

end
end KIP126.Classical.Adams.MilnorCohomology
