module

public import KIP126.AdamsComputation.Table.D2
public import KIP126.SSComputation.Table.Data

/-! SS propagation records, including derived d2 equations and later-page claims.
The direct Adams d2-column partition is certified independently upstream. -/

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

public theorem result (c : Raw.Claim) (hc : c ∈ Raw.claims) : Statement c := by
  sorry

end
end KIP126.Computation.Table
