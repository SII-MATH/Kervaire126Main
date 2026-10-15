module

public import KIP126.Computation.Tmf.Model.Data
public import KIP126.Main.Computation.Tmf.CsvE2.Classes.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.Tmf

noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

variable {H : Mod2EilenbergMacLane (C := C)} {T : Mon C}

/-- Coordinate transport respects the proved quotient identity; no new choice. -/
theorem E2Presentation.betaGFour_eq_betaFiveG (P : E2Presentation H T) :
    P.betaGFour = P.betaFiveG :=
  congrArg (P.comparison 19 114 (by decide)) CsvE2.betaGFour_eq_betaFiveG

end
end KIP126.Classical.Adams.Tmf
