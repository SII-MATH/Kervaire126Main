module

public import KIP126.Literature.Background.AlgebraRealization
public import KIP126.Literature.Standard.Milnor
public import KIP126.Def.Comparison.Cobar.Proofs
public import KIP126.Def.Synthetic.NormalizedMap.SphereDegreeOne

@[expose] public section

/-! The assumed algebra and realization comparisons on the fixed synthetic
Adams context. The detector algebra, its unit and the normalized η lift all
refer to the same specified objects and functors. -/

namespace KIP126.Def

open CategoryTheory

/-- The assumed algebra, realization and weight comparisons on the fixed
synthetic Adams context. -/
noncomputable abbrev standardAdamsSyntheticComparisons := KIP126.AdamsSynthetic.standardAdamsSyntheticComparisons

/-- The detector algebra has the specified detecting spectrum as its carrier.
No CSV coordinates or BR21 theorem are built into this algebra object. -/
noncomputable def standardTmfTarget :
    CategoryTheory.Mon KIP126.Classical.Adams.standardFoundation.Spectrum :=
  letI := standardAdamsSyntheticComparisons.algebra.classicalSymmetric
  letI := standardAdamsSyntheticComparisons.algebra.syntheticSymmetric
  { X := KIP126.Classical.Adams.standardAdamsComparison.hopfAndDetector.detector
    mon := standardAdamsSyntheticComparisons.algebra.detector.classical }

/-- The chosen synthetic η is the normalized lift of the specified
classical η, regraded by its stated filtration property. -/
noncomputable def standardEta :
    KIP126.Synthetic.Context.BiHom 1 2
      (KIP126.Synthetic.Context.S_0_0 : standardSyntheticContext.Syn) :=
  let D := KIP126.Classical.Adams.standardAdamsComparison
  (KIP126.AdamsSynthetic.etaSourceIso D
    (KIP126.Synthetic.Context.normalizedExponent_sphere_degree_one
      KIP126.Classical.Adams.standardFoundation.hf2 D.hopfAndDetector.etaMap)).hom ≫
    (D.normalizedMap (.shift 1 .sphere) .sphere D.hopfAndDetector.etaMap).map ≫ D.nu.unitIso.hom

/-- The fixed comparison preserves the prescribed actual cobar cocycles. -/
noncomputable def standardCobarDerivedExt :
    KIP126.Comparison.CobarDerivedExtComparison
      KIP126.Classical.Adams.standardFoundation.hf2
      KIP126.Classical.Adams.standardMilnorCooperations :=
  Classical.choice (KIP126.Comparison.cobarDerivedExtComparison
    KIP126.Classical.Adams.standardFoundation.hf2
    KIP126.Classical.Adams.standardMilnorCooperations)

end KIP126.Def
