module

public import KIP126.Def.Algebra.Graded.Tensor.Associator.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Coaction.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory KIP126.Algebra

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The actual cooperation diagonal in tensor coordinates. This is obtained
by applying Künneth to the middle unit insertion, not by prescribing the
Milnor coproduct. -/
def cooperationTensorDiagonal (n : ℤ) :
    mod2HomologyF2 H R n H.HF2 →ₗ[ZMod 2]
      cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n :=
  mod2TensorCoaction H R K H.HF2 n

/-- Apply the actual tensor-coordinate coproduct to the first cooperation
factor and reassociate. The remaining graded module is arbitrary. -/
def cooperationTensorComultiply (V : ℤ → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)] (n : ℤ) :
    cooperationTensor H R V n →ₗ[ZMod 2]
      cooperationTensor H R (cooperationTensor H R V) n :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  (gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H) V n).comp
    (gradedTensorMap (cooperationTensorDiagonal H R K) V n)

end

end KIP126.StableHomotopy.Cohomology
