module

public import KIP126.Main.AdamsSynthetic.Context
public import KIP126.Main.Computation.LinCoordinates.Interpretation.Differentials.Predicates

@[expose] public section

namespace KIP126.Computation.LinCalculations

/-- A row of the differential table gives the stated sphere differential.
The external computation hypotheses supply this result with respect to
the same E₂ presentation used to interpret the row. -/
theorem sphereTable_sound (shard offset : Nat) (row : DifferentialRow)
    (h : RawData.lookup shard offset = some row) : DifferentialStatement row :=
  KIP126.Main.AdamsSynthetic.computation.theorems.sphereTable_sound shard offset row h

end KIP126.Computation.LinCalculations
