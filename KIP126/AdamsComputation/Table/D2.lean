module

public import KIP126.AdamsComputation.Table
public import KIP126.AdamsComputation.Table.ClaimSyntax

/-! The selected records exported directly from the Adams E2-basis d2 column.
Their actual-page certification is the four-row partition of the previously
registered combined table obligation; it is not supplied by SS propagation. -/

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard
noncomputable section

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

namespace Raw
/-- Direct Adams outputs; origin strings and database row identifiers are unchanged. -/
public def directD2Claims : List Claim := [
  ⟨.sphere, .equation, 2, 7, 70, [2], 9, 71, [0], "S0_AdamsE2_basis/d2", 513⟩,
  ⟨.sphere, .equation, 2, 10, 136, [0], 12, 137, [2], "S0_AdamsE2_basis/d2", 2855⟩,
  ⟨.sphere, .equation, 2, 11, 137, [0], 13, 138, [3], "S0_AdamsE2_basis/d2", 2923⟩,
  ⟨.sphere, .equation, 2, 11, 137, [3], 13, 138, [4], "S0_AdamsE2_basis/d2", 2926⟩
]
end Raw

/-- Actual-sphere certification for precisely the four direct Adams d2 records. -/
public theorem direct_d2_result (c : Raw.Claim) (hc : c ∈ Raw.directD2Claims) : Statement c := by
  sorry

end
end KIP126.Computation.Table
