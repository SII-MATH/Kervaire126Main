module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Data
public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The actual outer unit insertion becomes the elementary tensor `1 ⊗ x`
under Künneth. This is a coherence condition on all spectra, below Adams
pages and differentials. No fixed witness is postulated. -/
def Mod2KunnethUnitCompatible : Prop :=
  ∀ (X : C) (n : ℤ) (x : mod2HomologyF2 H R n X),
    K.comparison X n (mod2OuterUnitMap H X n x) =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x

end KIP126.StableHomotopy.Cohomology
