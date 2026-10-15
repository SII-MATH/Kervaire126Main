module

public import KIP126.Main.Computation.LinCoordinates.Certificates.SquareDetection.Data
public import KIP126.Main.Computation.LinCoordinates.Interpretation.Classes.Data

@[expose] public section

namespace KIP126.Classical.Adams

-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- The computed h₆² is nonzero on E₂ by the external computation hypothesis.
The finite-check argument is retained in this statement, but the proof uses
the nonvanishing hypothesis for the actual sphere class. -/
theorem computedH6Square_ne_zero_of_check
    (h : KIP126.LinE2.SquareDetection.allRelationsCheck = true) :
    computedH6Square ≠ 0 := by
  exact KIP126.Main.externalHypotheses.computation.theorems.sphereSquare.nonzero

/-- The fixed computed h₆² is nonzero on E₂, by the sphere-square
nonvanishing statement in the common external hypotheses. -/
theorem computedH6Square_ne_zero : computedH6Square ≠ 0 :=
  KIP126.Main.externalHypotheses.computation.theorems.sphereSquare.nonzero

end KIP126.Classical.Adams
