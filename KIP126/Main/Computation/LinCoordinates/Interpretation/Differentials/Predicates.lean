module

public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Main.Computation.LinCoordinates.Interpretation.Classes.Data

@[expose] public section

namespace KIP126.Computation.LinCalculations

/-- Coordinates of a class in the basis specified by the external computation hypotheses. -/
def HasCoordinates {s t : Nat} (x : KIP126.LinE2.E2At s t)
    (indices : List Nat) : Prop :=
  KIP126.ExternalHypotheses.HasCoordinates x indices

/-- The finite-page sphere differential specified by one table row,
interpreted through the common E₂ presentation. -/
noncomputable def DifferentialStatement (row : DifferentialRow) : Prop :=
  KIP126.ExternalHypotheses.DifferentialStatement
    KIP126.Classical.Adams.linE2Presentation row

end KIP126.Computation.LinCalculations
