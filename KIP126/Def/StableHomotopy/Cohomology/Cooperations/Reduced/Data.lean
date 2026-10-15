module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- The reduced tensor is the kernel of augmentation into the remaining factor. -/
def reducedCooperationAugmentationEquiv (n : ℤ) :
    reducedCooperationTensor H R V n ≃ₗ[ZMod 2]
      LinearMap.ker (cooperationTensorAugmentation H R V n) :=
  (reducedCooperationTensorEquiv H R V n).trans
    (LinearEquiv.ofEq _ _ (cooperationTensorAugmentation_ker H R V n).symm)

end

end KIP126.StableHomotopy.Cohomology
