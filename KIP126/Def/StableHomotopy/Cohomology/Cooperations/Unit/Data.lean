module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Data
public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory KIP126.Classical.Adams
open scoped TensorProduct DirectSum

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- The degree-zero cooperation obtained from the specified coefficient
unit. No polynomial generator or basis is used. -/
def cooperationUnit : Mod2Cooperations H 0 :=
  H.pi0Equiv.symm 1 ≫ adamsUnit H.unit H.HF2

variable [MonoidalPreadditive C] (R : Mod2RingStructure H)

/-- The elementary tensor `1 ⊗ x` in total degree `n`, with the actual
cooperation unit and the required zero-degree cast. -/
def cooperationTensorUnit (V : ℤ → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)] (n : ℤ) :
    V n →ₗ[ZMod 2] cooperationTensor H R V n :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  (DirectSum.lof (ZMod 2) ℤ _ 0).comp
    ((TensorProduct.mk (ZMod 2) (Mod2Cooperations H 0) (V (n - 0))
      (cooperationUnit H)).comp
        (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero n).symm).toLinearMap)

end

end KIP126.StableHomotopy.Cohomology
