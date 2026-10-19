module

public import KIP126.E2Computation.Table
public import KIP126.AdamsCalculations.Table.Data

/-! Claims on later Adams pages, with their actual-page decoding. -/

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The same successful decoding and page-specific mathematical claims as
the original certification, including refutations as negated equations. -/
public def Statement (c : Raw.Claim) : Prop :=
  ∃ x, decode c.spectrum c.s c.t c.x = some x ∧
    match c.kind with
    | .reaches => ReachesPage (sequence c.spectrum) c.r (c.s,c.t) x
    | .boundaryBy => IsBoundaryBy (sequence c.spectrum) c.r (c.s,c.t) x
    | .equation => ∃ y, decode c.spectrum c.ts c.tt c.y = some y ∧
        HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y
    | .refutation => ∃ y, decode c.spectrum c.ts c.tt c.y = some y ∧
        ¬ HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y

public theorem result (c : Raw.Claim) (hc : c ∈ Raw.claims) : Statement c := by
  sorry

end
end KIP126.Computation.Table
