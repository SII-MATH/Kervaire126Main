module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Data
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Data

@[expose] public section

/-! The remaining Künneth input is below the Adams pages. It concerns all
represented homology groups, their naturality, and the specified multiplication.
No value of this structure is postulated for the fixed foundation. A complete
Milnor comparison also needs compatibility with the cooperation diagonal. -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- A natural Künneth comparison for `H ∧ X`, compatible with multiplication.
This is explicit lower-level input, not a constructed or fixed instance. -/
structure Mod2CooperationKunneth where
  comparison : ∀ (X : C) (n : ℤ),
    mod2HomologyF2 H R n (H.HF2 ⊗ X) ≃ₗ[ZMod 2]
      cooperationTensor H R (fun i => mod2HomologyF2 H R i X) n
  naturality : ∀ {X Y : C} (f : X ⟶ Y) (n : ℤ)
      (x : mod2HomologyF2 H R n (H.HF2 ⊗ X)),
    comparison Y n (Mod2Homology.pushforward H (H.HF2 ◁ f) n x) =
      cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
        (fun i => (mod2HomologyF2Map H R f i).hom) n (comparison X n x)
  action_comparison : ∀ (X : C) (n : ℤ)
      (x : mod2HomologyF2 H R n (H.HF2 ⊗ X)),
    cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n
      (comparison X n x) = inducedMap (mod2FreeAction H R X) n x

end KIP126.StableHomotopy.Cohomology
