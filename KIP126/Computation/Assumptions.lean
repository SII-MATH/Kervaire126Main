module

public import KIP126.Computation.Hypotheses
public import KIP126.Literature.Assumptions

@[expose] public section

namespace KIP126.Computation

/-- The external calculations interpreted on the fixed Adams sequences.
The tmf classes and source comparisons are those of `Literature.adamsSyntheticResults`;
the dependence in the type keeps these calculations on the same objects. -/
axiom adamsComputations : KIP126.ExternalHypotheses.ComputationHypotheses KIP126.Literature.adamsSyntheticResults

end KIP126.Computation
