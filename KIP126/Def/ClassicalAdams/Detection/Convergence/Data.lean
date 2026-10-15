module

public import KIP126.Def.ClassicalAdams.Detection.Convergence.Canonical.Predicates

@[expose] public section

namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
/-- Convergence to the actual homotopy of the *same* object, with the
filtration already constructed. No F₂-vector-space structure is imposed on π. -/
structure Convergence (X : C) where
  identification : ∀ p : ℤ × ℤ,
    ((adamsTowerInternalSpectralSequence unit X).ssData p).eInfty ≅
      (filtration unit X).associatedGraded p.1 (p.2 - p.1)
  canonical : CanonicalIdentification unit X identification
end
end KIP126.Classical.Adams.TowerDetection
