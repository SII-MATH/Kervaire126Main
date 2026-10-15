module

public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Proofs
public import KIP126.Literature.Standard.SyntheticComparison

@[expose] public section

/-! The E∞ weight-shift comparison selected from `canonicalWeightShift_exists`
for the specified standard Adams tower. Full-category naturality is a
separate assumption, `CanonicalWeightShift.natural`. -/
namespace KIP126.Def

/-- The prescribed quotient of the actual standard weight-tower map. -/
noncomputable def standardEInftyWeightShift :
    KIP126.Synthetic.SpectralSequence.EInftyWeightShift
      KIP126.Classical.Adams.standardAdamsComparison.family :=
  Classical.choose
    (KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists
      KIP126.Classical.Adams.standardAdamsComparison.towerPresentation)

end KIP126.Def
