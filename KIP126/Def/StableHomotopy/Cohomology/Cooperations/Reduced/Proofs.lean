module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

theorem reducedCooperationTensorInclusion_injective (n : ℤ) :
    Function.Injective (reducedCooperationTensorInclusion H R V n) :=
  Subtype.val_injective.comp (reducedCooperationTensorEquiv H R V n).injective

theorem reducedCooperationTensorInclusion_symm (n : ℤ)
    (x : LinearMap.ker (cooperationTensorAugmentation H R V n)) :
    reducedCooperationTensorInclusion H R V n
      ((reducedCooperationAugmentationEquiv H R V n).symm x) = x.val := by
  change (reducedCooperationAugmentationEquiv H R V n
    ((reducedCooperationAugmentationEquiv H R V n).symm x)).val = x.val
  rw [LinearEquiv.apply_symm_apply]

end

end KIP126.StableHomotopy.Cohomology
