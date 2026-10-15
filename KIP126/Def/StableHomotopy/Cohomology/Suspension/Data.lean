module

public import KIP126.Def.StableHomotopy.Context.Suspension.Data
public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ]

/-- Desuspension for the actual represented coefficient homology. -/
def mod2HomologyDesuspend (X : C) (n : ℤ) :
    Mod2Homology H n (X⟦(1 : ℤ)⟧) →+ Mod2Homology H (n - 1) X :=
  (homotopyDesuspend (H.HF2 ⊗ X) n).comp
    (inducedMap (((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app X) n)

/-- Desuspend after both coefficient factors; the inner factor's shift
comparison is applied through coefficient homology first. -/
def mod2DoubleHomologyDesuspend (X : C) (n : ℤ) :
    Mod2Homology H n (H.HF2 ⊗ (X⟦(1 : ℤ)⟧)) →+
      Mod2Homology H (n - 1) (H.HF2 ⊗ X) :=
  (mod2HomologyDesuspend H (H.HF2 ⊗ X) n).comp
    (Mod2Homology.pushforward H (((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app X) n)

def mod2HomologyDesuspendF2 [MonoidalPreadditive C] (R : Mod2RingStructure H)
    (X : C) (n : ℤ) :
    mod2HomologyF2 H R n (X⟦(1 : ℤ)⟧) →ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) X :=
  letI := mod2HomologyModule H R n (X⟦(1 : ℤ)⟧)
  letI := mod2HomologyModule H R (n - 1) X
  (mod2HomologyDesuspend H X n).toZModLinearMap 2

end

end KIP126.StableHomotopy.Cohomology
