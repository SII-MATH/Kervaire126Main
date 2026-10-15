module

public import KIP126.Literature.Hypotheses
public import KIP126.Computation.Hypotheses

@[expose] public section

/-! External hypotheses for the Kervaire argument: cited literature theorems
and the mathematical interpretation of the fixed computations. Both refer to
the classical and synthetic Adams sequences selected in Literature.Standard. The dependent
computation hypothesis identifies its tmf classes with the specified
literature classes. The paper's conclusions are proved from these hypotheses
in Main. -/
namespace KIP126

/-- Literature and computation hypotheses on the same Adams/synthetic
background, with a common choice of source objects and distinguished classes. -/
structure ExternalHypotheses where
  literature : ExternalHypotheses.LiteratureHypotheses
  computation : ExternalHypotheses.ComputationHypotheses literature

end KIP126
