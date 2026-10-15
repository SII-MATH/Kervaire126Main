module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.CycleMap.Data

@[expose] public section

/-!
# Standard `hᵢ` classes on the internal tower spectral sequence

The Milnor cocycle goes through the actual first-page homology quotient and
the already constructed isomorphism to the same tower's internal `SSData` page.
This does not introduce a comparison of independently chosen spectral sequences,
and the Milnor input is the same one used to construct the representative.
-/

namespace KIP126.Classical.Adams.Sphere.Internal

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The standard `hᵢ` on the internal second page of the actual sphere tower. -/
def hi (i : ℕ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (1, ((2 ^ i : ℕ) : ℤ)) :=
  MilnorCohomology.internalClassOfCocycle H M (KIP126.Steenrod.Milnor.hiCochain i)
    (KIP126.Steenrod.Milnor.hiCochain_isCycle i)

/-- The actual Milnor concatenation square on the same internal second page. -/
def hiSquare (i : ℕ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      (2, ((2 ^ (i + 1) : ℕ) : ℤ)) :=
  MilnorCohomology.internalClassOfCocycle H M (KIP126.Steenrod.Milnor.hiSquareCochain i)
    (KIP126.Steenrod.Milnor.hiSquareCochain_isCycle i)

end

end KIP126.Classical.Adams.Sphere.Internal
