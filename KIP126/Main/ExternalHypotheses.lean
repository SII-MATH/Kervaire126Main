module

public import KIP126.Computation.Hypotheses.Joint
public import KIP126.Literature.Assumptions
public import KIP126.Computation.Assumptions

@[expose] public section

namespace KIP126.Main

/-- The literature hypotheses and the calculations on their specified objects,
combined from the two external-result axioms. All applications in Main
use this same dependent pair. -/
noncomputable def externalHypotheses : KIP126.ExternalHypotheses where
  literature := KIP126.Literature.adamsSyntheticResults
  computation := KIP126.Computation.adamsComputations

end KIP126.Main
