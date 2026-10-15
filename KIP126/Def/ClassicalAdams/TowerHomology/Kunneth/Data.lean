module

public import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Basic.Proofs

@[expose] public section

/-! The reduced tensor recurrence is derived from homology-level Künneth and
the actual fiber triangle. Neither tower coordinates nor later pages are inputs. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- Restrict the homology-level comparison to the two corresponding kernels. -/
def adamsHomologyKunnethKernelEquiv (X : C) (n : ℤ) :
    letI := mod2HomologyModule H R n X
    letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
    LinearMap.ker ((adamsHomologyAction H R X n).toAddMonoidHom.toZModLinearMap 2) ≃ₗ[ZMod 2]
      LinearMap.ker (cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n) :=
  letI := mod2HomologyModule H R n X
  letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
  (K.comparison X n).ofSubmodules _ _ (adamsHomologyKunneth_map_ker H R K X n)

variable [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The next actual fiber's homology is the reduced cooperation tensor product.
Only lower-level Künneth, multiplication, and tensor exactness are assumed. -/
def adamsNextHomologyTensorEquiv (X : C) (n : ℤ) :
    mod2HomologyF2 H R (n - 1) (fiber (adamsUnit H.unit X)) ≃ₗ[ZMod 2]
      reducedCooperationTensor H R (fun i => mod2HomologyF2 H R i X) n :=
  (adamsHomologyKernelF2Equiv H R X n).symm.trans
    ((adamsHomologyKunnethKernelEquiv H R K X n).trans
      (reducedCooperationAugmentationEquiv H R (fun i => mod2HomologyF2 H R i X) n).symm)

/-- The same derived recurrence, at every actual tower stage. -/
def adamsTowerHomologyTensorEquiv (X : C) (s : ℕ) (n : ℤ) :
    mod2HomologyF2 H R (n - 1) (adamsTower H.unit X (s + 1)) ≃ₗ[ZMod 2]
      reducedCooperationTensor H R
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit X s)) n :=
  adamsNextHomologyTensorEquiv H R K (adamsTower H.unit X s) n

end

end KIP126.Classical.Adams
