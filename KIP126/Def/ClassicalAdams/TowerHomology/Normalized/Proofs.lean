module

public import KIP126.Def.ClassicalAdams.TowerHomology.Normalized.Data

@[expose] public section

/-! Derived coefficient-homology descriptions of the actual Adams tower.
Tensor exactness and a multiplication are explicit structural arguments;
no global instance, Milnor coordinates, or independently chosen pages are supplied. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
  KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The inverse equivalence normalizes a lift by subtracting its unit-action part. -/
theorem adamsHomologyKernelEquiv_symm_boundary (R : Mod2RingStructure H) (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    ((adamsHomologyKernelEquiv H R X n).symm (adamsHomologyBoundary H X n x) :
      Mod2Homology H n (H.HF2 ⊗ X)) =
        x - adamsHomologyUnit H X n (adamsHomologyAction H R X n x) := by
  have hm : x - adamsHomologyUnit H X n (adamsHomologyAction H R X n x) ∈
      LinearMap.ker (adamsHomologyAction H R X n) := by
    change adamsHomologyAction H R X n (_ - _) = 0
    rw [map_sub, adamsHomologyAction_unit, sub_self]
  have he : adamsHomologyKernelEquiv H R X n ⟨_, hm⟩ = adamsHomologyBoundary H X n x := by
    change adamsHomologyBoundary H X n (_ - _) = _
    rw [map_sub, adamsHomologyBoundary_unit, sub_zero]
  rw [← he, LinearEquiv.symm_apply_apply]

/-- The sphere identification sends a boundary class to the normalized cooperation. -/
theorem sphereFirstTowerHomologyEquiv_boundary (R : Mod2RingStructure H) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ SphereSpectrum)) :
    (sphereFirstTowerHomologyEquiv H R n (adamsHomologyBoundary H SphereSpectrum n x) :
      Mod2Cooperations H n) =
      sphereCoefficientHomologyEquiv H n
        (x - adamsHomologyUnit H SphereSpectrum n (adamsHomologyAction H R SphereSpectrum n x)) := by
  change sphereCoefficientHomologyEquiv H n
    ((adamsHomologyKernelEquiv H R SphereSpectrum n).symm (adamsHomologyBoundary H SphereSpectrum n x)).val = _
  rw [adamsHomologyKernelEquiv_symm_boundary]

end

end KIP126.Classical.Adams
