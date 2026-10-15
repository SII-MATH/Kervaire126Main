module

public import KIP126.Def.Algebra.Graded.Tensor.Lowering.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Algebra

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- Tensor the identity on genuine cooperations with a degree-minus-one map. -/
def cooperationTensorLowerMap (V W : ℤ → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
    [∀ i, Module (ZMod 2) (V i)] [∀ i, Module (ZMod 2) (W i)]
    (g : ∀ i, V i →ₗ[ZMod 2] W (i - 1)) (n : ℤ) :
    cooperationTensor H R V n →ₗ[ZMod 2] cooperationTensor H R W (n - 1) :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  gradedTensorLowerMap (Mod2Cooperations H) g n

end

end KIP126.StableHomotopy.Cohomology
