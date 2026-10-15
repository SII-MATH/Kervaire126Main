module

public import KIP126.Literature.Standard.Foundation
public import KIP126.Def.ClassicalAdams.Convergence.BHS.Predicates

@[expose] public section

namespace KIP126.Def

/-- Standard completeness and strong convergence for the fixed 2-completed
sphere and its existing HF₂ Adams tower. This is accepted background for the
Section 7 proof, separately from the literature and computation hypotheses.
The axiom does not assert any differential or permanent-cycle conclusion. -/
axiom standardSphereApplicability : Classical.Adams.BHSObjectApplicability
    standardHF2AdamsContext.stableContext.countableProducts
    standardHF2AdamsContext.stableContext.hf2.unit
    (StableHomotopy.SphereSpectrum
      (C := standardHF2AdamsContext.stableContext.Spectrum))

end KIP126.Def
