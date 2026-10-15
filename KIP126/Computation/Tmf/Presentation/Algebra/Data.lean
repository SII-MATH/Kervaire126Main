module

public import KIP126.Computation.Tmf.Model.Data
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section
/-!
# Chosen tmf algebra and coordinates

The algebra object is supplied together with a comparison to the fixed tmf
coordinate algebra. This is part of the external computation input.
-/

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams SpectralSequence

universe u v w

/-- The chosen algebra object and fixed tmf coordinates, before the BR21 claim. -/
structure TmfAdamsPresentation {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)) where
  target : Mon C
  coordinates : Tmf.E2Presentation H target

end KIP126.Classical.Adams
