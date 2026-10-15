module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- Künneth intertwines the coaction on the free coefficient object with
the cooperation coproduct on the first tensor factor. This is a below-page
coherence condition: it mentions no Adams tower, differential, Milnor basis,
or permanence. No witness on the fixed foundation is assumed here. -/
def Mod2KunnethDiagonalCompatible : Prop :=
  ∀ (X : C) (n : ℤ) (z : mod2HomologyF2 H R n (H.HF2 ⊗ X)),
    cooperationTensorMap H R (fun i => mod2HomologyF2 H R i (H.HF2 ⊗ X))
      (fun i => (K.comparison X i).toLinearMap) n
      (mod2TensorCoaction H R K (H.HF2 ⊗ X) n z) =
        cooperationTensorComultiply H R K (fun i => mod2HomologyF2 H R i X) n
          (K.comparison X n z)

end KIP126.StableHomotopy.Cohomology
