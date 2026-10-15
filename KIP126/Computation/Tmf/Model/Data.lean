module

public import KIP126.Def.ClassicalAdams.Tmf.Model.Data
public import KIP126.Computation.Tmf.CsvE2.Classes.Data

@[expose] public section

namespace KIP126.Classical.Adams.Tmf

noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- A bounded coordinate comparison for an explicit tmf realization.
No named class is independently chosen: all are transported from the fixed
polynomial quotient. The coordinate comparison is an explicit hypothesis. -/
structure E2Presentation (H : Mod2EilenbergMacLane (C := C)) (T : Mon C) where
  comparison : ∀ (s t : ℕ), t ≤ 261 →
    CsvE2.E2At s t ≃ₗ[ℤ]
      (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 ((s : ℤ), (t : ℤ))

variable {H : Mod2EilenbergMacLane (C := C)} {T : Mon C}

/-- The fixed w₂² class, on this realization's actual internal E₂. -/
def E2Presentation.v2Sixteen (P : E2Presentation H T) :
    (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 (16, 112) :=
  P.comparison 16 112 (by decide) CsvE2.v2Sixteen

/-- The fixed β⁵g class on the same actual internal E₂. -/
def E2Presentation.betaFiveG (P : E2Presentation H T) :
    (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 (19, 114) :=
  P.comparison 19 114 (by decide) CsvE2.betaFiveG

/-- BR21's target transported through the very same E₂ comparison. -/
def E2Presentation.betaGFour (P : E2Presentation H T) :
    (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 (19, 114) :=
  P.comparison 19 114 (by decide) CsvE2.betaGFour


end
end KIP126.Classical.Adams.Tmf
