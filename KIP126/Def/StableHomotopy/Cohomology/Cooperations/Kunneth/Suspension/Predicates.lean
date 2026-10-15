module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Lowering.Data
public import KIP126.Def.StableHomotopy.Cohomology.Suspension.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) [(tensorLeft H.HF2).CommShift ℤ]

/-- Compatibility of the homology Künneth comparison with actual suspension.
This condition mentions only spectra, shift maps, and graded cooperations;
it contains no triangle boundary, Adams page, or differential. No fixed
witness is postulated. Boundary compatibility will be derived from it. -/
def Mod2KunnethSuspensionCompatible : Prop :=
  ∀ (X : C) (n : ℤ) (x : Mod2Homology H n (H.HF2 ⊗ (X⟦(1 : ℤ)⟧))),
    K.comparison X (n - 1) (mod2DoubleHomologyDesuspend H X n x) =
      cooperationTensorLowerMap H R
        (fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧)) (fun i => mod2HomologyF2 H R i X)
        (mod2HomologyDesuspendF2 H R X) n (K.comparison (X⟦(1 : ℤ)⟧) n x)

end KIP126.StableHomotopy.Cohomology
