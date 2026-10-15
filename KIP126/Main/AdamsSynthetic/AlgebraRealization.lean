module

public import KIP126.Literature.Standard.AlgebraRealization

public import KIP126.Def.AdamsSynthetic.AlgebraRealization.Data
public import KIP126.Literature.Standard.Milnor
public import KIP126.Def.Comparison.Cobar.Proofs
public import KIP126.Literature.Background.AlgebraRealization

@[expose] public section

/-! Comparisons on the one standard sphere background. The selected proof
does not require a separate mapping-tower Moss context. -/

namespace KIP126.Def

/-- The generic cobar/derived-Ext comparison specialized to the same fixed
HF₂ and Milnor construction used by every downstream sphere statement. -/
theorem standardCobarDerivedExt_exists :
    Nonempty (KIP126.Comparison.CobarDerivedExtComparison
      KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations) :=
  KIP126.Comparison.cobarDerivedExtComparison
    KIP126.Classical.Adams.standardFoundation.hf2
    KIP126.Classical.Adams.standardMilnorCooperations

/-- The selected classical Hopf map has the precise filtration needed to
regrade its actual normalized synthetic lift to bidegree (1,2). This is a
property of the fixed Adams comparison, not a property of an arbitrary
inhabitant of `SyntheticAdamsContext`; the proof below derives it from the HF₂ groups. -/
theorem standardEtaExponent :
    KIP126.Synthetic.Context.normalizedExponent
      KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardAdamsComparison.hopfAndDetector.etaMap = 1 :=
  KIP126.Synthetic.Context.normalizedExponent_sphere_degree_one
    KIP126.Classical.Adams.standardFoundation.hf2
    KIP126.Classical.Adams.standardAdamsComparison.hopfAndDetector.etaMap

/-- All detector comparisons preserve the specified Hurewicz unit. -/
theorem standardTmfTarget_unit :
    KIP126.Classical.Adams.Tmf.unit standardTmfTarget =
      KIP126.Classical.Adams.standardAdamsComparison.hopfAndDetector.detectorUnit := by
  letI := standardAdamsSyntheticComparisons.algebra.classicalSymmetric
  letI := standardAdamsSyntheticComparisons.algebra.syntheticSymmetric
  exact standardAdamsSyntheticComparisons.algebra.detector.classical_unit

end KIP126.Def
