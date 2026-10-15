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

/-! The constant normalized cochain and its class in the existing Milnor
cohomology quotient. The quotient retains the specified cooperation comparison. -/

namespace KIP126.Steenrod.Milnor

open KIP126.Algebra

noncomputable section

/-- The constant polynomial in the zero-fold tensor power. -/
def unitCochain : cochains 0 0 := by
  refine ⟨1, ?_, ?_⟩
  · exact MvPolynomial.isWeightedHomogeneous_one F2 weight
  · change (1 : TensorPower 0) ∈
      (⨅ slot : Fin 0, LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    exact Fin.elim0 slot

/-- The two coaugmentations cancel over F₂. -/
theorem unitCochain_isCycle : IsCycle unitCochain := by
  apply Subtype.ext
  change differentialPolynomial 0 1 = 0
  simp [differentialPolynomial, CharTwo.add_self_eq_zero]

end
end KIP126.Steenrod.Milnor

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The cohomological unit is represented by the specified constant polynomial. -/
def unit : Cohomology H M 0 0 := ofCocycle H M unitCochain unitCochain_isCycle

end
end KIP126.Classical.Adams.MilnorCohomology
