module

public import KIP126.Def.ClassicalAdams.TowerHomology.Proofs
public import Mathlib.LinearAlgebra.Isomorphisms

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

/-- The next fiber's coefficient homology is the normalized action kernel.
The isomorphism is constructed from exactness and the unit retraction. -/
def adamsHomologyKernelEquiv (R : Mod2RingStructure H) (X : C) (n : ℤ) :
    LinearMap.ker (adamsHomologyAction H R X n) ≃ₗ[ℤ]
      Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X)) :=
  LinearEquiv.ofBijective ((adamsHomologyBoundary H X n).domRestrict _)
    (adamsHomologyBoundary_ker_action_bijective H R X n)

/-- Restrict the unitor-induced equivalence to the two corresponding kernels. -/
def sphereHomologyActionKernelEquiv (R : Mod2RingStructure H) (n : ℤ) :
    LinearMap.ker (adamsHomologyAction H R SphereSpectrum n) ≃ₗ[ℤ]
      LinearMap.ker (cooperationCounit H R n).toIntLinearMap :=
  (sphereCoefficientHomologyEquiv H n).ofSubmodules _ _
    (sphereCoefficientHomologyEquiv_map_ker H R n)

/-- The homology of the first actual sphere tower stage is the shifted
cooperation counit kernel. No Milnor coordinates or Künneth formula are assumed. -/
def sphereFirstTowerHomologyEquiv (R : Mod2RingStructure H) (n : ℤ) :
    Mod2Homology H (n - 1) (adamsTower H.unit SphereSpectrum 1) ≃ₗ[ℤ]
      LinearMap.ker (cooperationCounit H R n).toIntLinearMap :=
  (adamsHomologyKernelEquiv H R SphereSpectrum n).symm.trans (sphereHomologyActionKernelEquiv H R n)

end

end KIP126.Classical.Adams
