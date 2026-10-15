module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- Traverse an interval during the second half of the parameter. -/
noncomputable def delayedCoordinate (t : I) : I :=
  Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)

/-- Traverse an interval during the first half of the parameter. -/
noncomputable def advancedCoordinate (t : I) : I :=
  Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))

end KIP126.Topology.Cube
