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

/-- The inclusion of the reduced tensors into the unreduced tensors. -/
def reducedCooperationTensorInclusion (n : ℤ) :
    reducedCooperationTensor H R V n →ₗ[ZMod 2] cooperationTensor H R V n :=
  (LinearMap.ker (cooperationTensorCounit H R V n)).subtype.comp
    (reducedCooperationTensorEquiv H R V n).toLinearMap

/-- Transport only the remaining graded factor, keeping the genuine reduced cooperations. -/
def reducedCooperationTensorCongr {W : ℤ → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
    (e : ∀ i, V i ≃ₗ[ZMod 2] W i) (n : ℤ) :
    reducedCooperationTensor H R V n ≃ₗ[ZMod 2] reducedCooperationTensor H R W n :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  DirectSum.congrLinearEquiv fun i =>
    TensorProduct.congr (LinearEquiv.refl (ZMod 2) (LinearMap.ker (cooperationCounitF2 H R i)))
      (e (n - i))

end

end KIP126.StableHomotopy.Cohomology
