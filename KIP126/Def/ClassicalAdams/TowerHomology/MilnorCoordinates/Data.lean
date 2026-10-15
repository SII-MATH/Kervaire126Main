module

public import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Basic.Data
public import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Proofs

@[expose] public section

/-! Derive all first-page Milnor vector-space coordinates from a basis on the
actual reduced cooperations and homology Künneth. No page-coordinate input
is used. Differential compatibility is not asserted by this construction. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
  [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The all-filtration word coordinates are recursively constructed from the
actual tower boundary isomorphism, not supplied as fields. -/
def sphereTowerHomologyWordEquiv : ∀ (s : ℕ) (n : ℤ),
    mod2HomologyF2 H R n (adamsTower H.unit SphereSpectrum s) ≃ₗ[ZMod 2]
      (MilnorWord s (n + s) →₀ ZMod 2)
  | 0, n => (sphereHomologyEmptyWordEquiv H R n).trans
      (LinearEquiv.cast (R := ZMod 2) (M := fun t => MilnorWord 0 t →₀ ZMod 2)
        (show n = n + (0 : ℕ) by simp))
  | s + 1, n =>
    (LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum (s + 1)))
      (show n = (n + 1) - 1 by omega)).trans
      ((adamsTowerHomologyTensorEquiv H R K SphereSpectrum s (n + 1)).trans
        (reducedTensorMilnorWordEquiv H R B
          (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s))
          s (sphereTowerHomologyWordEquiv s) n))

/-- Actual first-page coordinates in the existing polynomial Milnor cochains,
derived from below-page data in every nonnegative bidegree. -/
def sphereFirstPageMilnorEquiv (s t : ℕ) :
    letI := adamsPageF2Module H R SphereSpectrum 1 le_rfl s t
    adamsPage H.unit SphereSpectrum 1 le_rfl s t ≃ₗ[ZMod 2] cochains s t :=
  letI := adamsPageF2Module H R SphereSpectrum 1 le_rfl s t
  (adamsPageOneHomologyF2Equiv H R SphereSpectrum s t).trans
    ((sphereTowerHomologyWordEquiv H R K B s (t - s)).trans
      ((LinearEquiv.cast (R := ZMod 2) (M := fun n => MilnorWord s n →₀ ZMod 2)
        (show (t : ℤ) - s + s = t by omega)).trans (cochainsWordEquiv s t).symm))

end

end KIP126.Classical.Adams
