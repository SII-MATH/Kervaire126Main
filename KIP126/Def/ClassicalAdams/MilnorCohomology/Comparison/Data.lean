module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.CycleMap.Proofs
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

/-!
# Actual cobar cohomology and the internal Adams E₂ page

The equivalence is induced by the fixed Milnor coordinates and the actual
first-page homology quotient. It is constructed from the proved kernel and
surjectivity of that canonical class map, including cohomological degree zero.
This does not define or identify a separate derived-functor Ext object.
-/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The canonical comparison, for every nonnegative cobar bidegree, with
the second page of this very Adams tower. -/
def comparison (s t : ℕ) : Cohomology H M s t ≃ₗ[ℤ]
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      ((s : ℤ), (t : ℤ)) :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ (boundariesInCycles H M s t)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (boundariesInCycles_restrictScalars_eq_ker H M s t)).trans
      ((cycleClassMap H M s t).quotKerEquivOfSurjective (cycleClassMap_surjective H M s t)))

end
end KIP126.Classical.Adams.MilnorCohomology
