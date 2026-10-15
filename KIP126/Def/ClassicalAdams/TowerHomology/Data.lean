module

public import KIP126.Def.ClassicalAdams.TowerResolution.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Data

@[expose] public section

/-! Derived coefficient-homology descriptions of the actual Adams tower.
Tensor exactness and a multiplication are explicit structural arguments;
no global instance, Milnor coordinates, or independently chosen pages are supplied. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
  KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The actual unit fiber triangle after applying the exact functor `H ⊗ -`.
Its connecting map includes the supplied shift compatibility. -/
def adamsHomologySequence (X : C) : HoCofiberSequence (C := C) where
  X := H.HF2 ⊗ fiber (adamsUnit H.unit X)
  Y := H.HF2 ⊗ X
  Z := H.HF2 ⊗ (H.HF2 ⊗ X)
  f := H.HF2 ◁ fiberι (adamsUnit H.unit X)
  g := H.HF2 ◁ adamsUnit H.unit X
  h := (tensorLeft H.HF2).map (adamsResolutionConnecting H.unit X 0) ≫
    ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app (fiber (adamsUnit H.unit X))
  distinguished := (tensorLeft H.HF2).map_distinguished _
    (adamsResolutionTriangle_distinguished H.unit X 0)

/-- The unit-induced map on coefficient homology. -/
def adamsHomologyUnit (X : C) (n : ℤ) :
    Mod2Homology H n X →ₗ[ℤ] Mod2Homology H n (H.HF2 ⊗ X) :=
  (inducedMap (H.HF2 ◁ adamsUnit H.unit X) n).toIntLinearMap

/-- The homology retraction induced by multiplication on the first two factors. -/
def adamsHomologyAction (R : Mod2RingStructure H) (X : C) (n : ℤ) :
    Mod2Homology H n (H.HF2 ⊗ X) →ₗ[ℤ] Mod2Homology H n X :=
  (inducedMap (mod2FreeAction H R X) n).toIntLinearMap

/-- The connecting homomorphism of the smashed unit triangle. -/
def adamsHomologyBoundary (X : C) (n : ℤ) :
    Mod2Homology H n (H.HF2 ⊗ X) →ₗ[ℤ]
      Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X)) :=
  (connectingHomomorphism (adamsHomologySequence H X) n).toIntLinearMap

/-- Remove the final sphere factor to identify the middle homology with cooperations. -/
def sphereCoefficientHomologyEquiv (n : ℤ) :
    Mod2Homology H n (H.HF2 ⊗ SphereSpectrum) ≃ₗ[ℤ] Mod2Cooperations H n :=
  ((homotopyGroupFunctor n).mapIso ((tensorLeft H.HF2).mapIso (ρ_ H.HF2))).addCommGroupIsoToAddEquiv.toIntLinearEquiv

end

end KIP126.Classical.Adams
