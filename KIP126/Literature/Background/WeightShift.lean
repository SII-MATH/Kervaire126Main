module

public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Predicates
public import KIP126.Def.Synthetic.EInfty.Shift.Predicates

@[expose] public section

/-! BHS weight-regrading naturality for the specified synthetic Adams tower.
This is an external hypothesis. The canonical quotient construction and its
existence proof remain in Def. -/
namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn}

/-- Standard background naturality for the comparison induced by the same
actual tower presentation. The canonicality premise is retained: this does
not assume that an arbitrary family of weight isomorphisms is natural.
The source construction and its object/tower comparison are outside the
current proof scope; the canonical existence and quotient transports
remain proved separately in Def. -/
axiom CanonicalWeightShift.natural (P : TowerPresentation unit F)
    (S : EInftyWeightShift F) (canonical : CanonicalWeightShift P S) :
    S.Natural

end KIP126.Synthetic.SpectralSequence
