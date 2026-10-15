module

public import KIP126.Def.StableHomotopy.Cohomology.Data
public import KIP126.Def.ClassicalAdams.Detection.Data

@[expose] public section

namespace KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Conservative positive-stem Adams vanishing region. The zero stem is
excluded so the h₀ tower is retained. Supplying this premise on the actual
sphere tower requires a separate source theorem and comparison; a finite
CSV table cannot establish it. No witness is provided by this definition. -/
def SphereVanishingLine (H : Mod2EilenbergMacLane (C := C)) : Prop :=
  ∀ s t : ℤ, 0 < t - s → t - s < 2 * s - 3 →
    Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s,t))

/-- Separation of the actual sphere's Adams filtration, distinct from
an arbitrary associated-graded identification and synthetic separation. -/
def ClassicalSphereSeparated (H : Mod2EilenbergMacLane (C := C)) : Prop :=
  ∀ (n : ℤ) (a : HomotopyGroup (C := C) n SphereSpectrum),
    (∀ s : ℕ, a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum s n) → a = 0

end KIP126.Classical.Adams
