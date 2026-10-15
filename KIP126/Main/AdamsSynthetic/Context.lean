module

public import KIP126.Main.ExternalHypotheses

@[expose] public section

/-! The fixed Adams/synthetic model, its distinguished classes, and the
literature and computation hypotheses used throughout the Section 7 proof.
All source comparisons come from `Main.externalHypotheses`. -/
namespace KIP126.Main.AdamsSynthetic

/-- Cited theorems and source comparisons for the fixed Adams/synthetic model. -/
noncomputable def literature :
    KIP126.ExternalHypotheses.LiteratureHypotheses :=
  KIP126.Main.externalHypotheses.literature

/-- Calculations on the actual Adams sequences, using the source objects
and distinguished classes specified by `literature`. -/
noncomputable def computation :
    KIP126.ExternalHypotheses.ComputationHypotheses literature :=
  KIP126.Main.externalHypotheses.computation

/-- The classical and synthetic Adams sequences with their comparison data. -/
noncomputable abbrev adamsComparison := KIP126.Classical.Adams.standardAdamsComparison
/-- The four sphere E₂ classes specified by the fixed computation coordinates. -/
noncomputable abbrev sphereClasses := computation.interpretation.sphereClasses
/-- Distinguished tmf classes identified with the literature source classes. -/
noncomputable abbrev tmfLabels := literature.sources.tmfLabels
/-- The fixed synthetic lift of the classical Hopf class η. -/
noncomputable abbrev etaClass := KIP126.Def.standardEta

/-- The computation theorems in the form used by the Section 7 argument,
with the same sphere and tmf classes as the external hypotheses. -/
noncomputable def computationTheorems :
    KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems adamsComparison sphereClasses tmfLabels :=
  computation.sphereAndCofiber

/-- The literature vanishing line for the actual sphere Adams spectral sequence. -/
theorem sphereVanishing :
    KIP126.Classical.Adams.SphereVanishingLine KIP126.Classical.Adams.standardFoundation.hf2 :=
  literature.theorems.sphereVanishing

/-- The BHS completion hypotheses for the specified source objects. -/
theorem completionApplicability :
    KIP126.Literature.AdamsSynthetic.BHSCompletionApplicability adamsComparison
      literature.sources.sourceComparisons.bhsCompletion :=
  literature.sources.sourceComparisons.completionApplicability

/-- Comparison of the fixed Adams/synthetic model with those BHS completions. -/
theorem completionComparison :
    KIP126.Literature.AdamsSynthetic.BHSCompletionComparison adamsComparison
      literature.sources.sourceComparisons.bhsCompletion :=
  literature.sources.sourceComparisons.completionComparison

/-- Compatibility of realization with the same BHS completion comparison. -/
theorem realizationComparison :
    KIP126.Literature.AdamsSynthetic.BHSRealizationComparison adamsComparison
      literature.sources.sourceComparisons.realization
      literature.sources.sourceComparisons.bhsCompletion :=
  literature.sources.sourceComparisons.realizationComparison

end KIP126.Main.AdamsSynthetic
