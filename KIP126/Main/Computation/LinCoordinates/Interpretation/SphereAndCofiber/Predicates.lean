module

public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Predicates

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Different provenance records can impose the same mathematical obligation.
Keep their origin and record identifiers for traceability; they do not change
the decoded claim or supply a proof of it. -/
theorem statement_with_provenance {D : AdamsComparison H M Syn} (R : E2Interpretation D)
    (c : Raw.Claim) (origin : String) (record : Nat) :
    AdamsStatement R { c with origin := origin, record := record } ↔ AdamsStatement R c :=
  Iff.rfl


end
end KIP126.Computation.SphereAndCofiber
