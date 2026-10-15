module

public import KIP126.Literature.Background.WeightShift

public import KIP126.Literature.Standard.Sphere.EInfty

@[expose] public section

namespace KIP126.Def

/-- Naturality of the weight comparison fixed by the standard Adams tower.
This specializes the explicit standard-background naturality axiom for the
same canonical comparison; it does not choose unrelated weight isomorphisms. -/
theorem standardEInftyWeightShift_natural : standardEInftyWeightShift.Natural := by
  exact KIP126.Synthetic.SpectralSequence.CanonicalWeightShift.natural
    KIP126.Classical.Adams.standardAdamsComparison.towerPresentation
    standardEInftyWeightShift
    (Classical.choose_spec
      (KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists
        KIP126.Classical.Adams.standardAdamsComparison.towerPresentation))

end KIP126.Def
