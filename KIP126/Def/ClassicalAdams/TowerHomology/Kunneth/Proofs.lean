module

public import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)
  [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The derived tensor coordinate of an actual boundary is the Künneth
coordinate of its normalized lift. No differential-coordinate law is assumed. -/
theorem adamsNextHomologyTensorEquiv_boundary (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
      (adamsNextHomologyTensorEquiv H R K X n (adamsHomologyBoundary H X n x)) =
        K.comparison X n (x - adamsHomologyUnit H X n (adamsHomologyAction H R X n x)) := by
  change reducedCooperationTensorInclusion H R _ n
    ((reducedCooperationAugmentationEquiv H R _ n).symm
      (adamsHomologyKunnethKernelEquiv H R K X n
        ((adamsHomologyKernelF2Equiv H R X n).symm (adamsHomologyBoundary H X n x)))) = _
  rw [reducedCooperationTensorInclusion_symm]
  change K.comparison X n
    ((adamsHomologyKernelEquiv H R X n).symm (adamsHomologyBoundary H X n x)).val = _
  rw [adamsHomologyKernelEquiv_symm_boundary]

end

end KIP126.Classical.Adams
