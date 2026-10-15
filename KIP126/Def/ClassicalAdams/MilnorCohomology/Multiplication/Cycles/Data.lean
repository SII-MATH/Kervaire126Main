module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Data
public import KIP126.Def.Steenrod.MilnorCobar.Multiplication.Proofs
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section

/-! The explicit normalized cobar concatenation, restricted to cycles. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

/-- Concatenation of actual cycles, with closedness proved by Leibniz. -/
def cycleCup (s t s' t' : ℕ) :
    cycles s t →ₗ[F2] cycles s' t' →ₗ[F2] cycles (s + s') (t + t') where
  toFun x :=
    { toFun := fun y => ⟨cup x.val y.val, cup_isCycle _ _ x.property y.property⟩
      map_add' := fun y z => Subtype.ext (cup_add_right x.val y.val z.val)
      map_smul' := fun a y => Subtype.ext (cup_smul_right a x.val y.val) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact Subtype.ext (cup_add_left x.val y.val z.val)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (cup_smul_left a x.val y.val)

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The cohomology class of concatenation, before descending either input. -/
def cycleCupClass (s t s' t' : ℕ) :
    cycles s t →ₗ[F2] cycles s' t' →ₗ[F2] Cohomology H M (s + s') (t + t') :=
  (cycleCup s t s' t').compr₂ (classOf H M (s + s') (t + t'))

end
end KIP126.Classical.Adams.MilnorCohomology
