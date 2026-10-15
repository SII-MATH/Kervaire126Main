module

public import KIP126.Main.AdamsSynthetic.Context
public import KIP126.Main.AdamsSynthetic.Toda
public import KIP126.Main.AdamsSynthetic.NuSource
public import KIP126.Main.Computation.Tmf
public import KIP126.Main.Computation.Tmf.Br21
public import KIP126.Main.AdamsSynthetic.SphereConvergence
public import KIP126.Main.AdamsSynthetic.WeightShift
public import KIP126.Main.Literature.SourceComparisons.Theorems

@[expose] public section

/-! Literature theorems and computation consequences on the fixed
Adams/synthetic comparison, including Toda relations and tmf detection. -/
namespace KIP126.Main.AdamsSynthetic

theorem sphereSeparated :
    KIP126.Classical.Adams.ClassicalSphereSeparated KIP126.Classical.Adams.standardFoundation.hf2 :=
  KIP126.Def.standardSphereSeparated

/-- Main combines the same source results with Def's naturality of the
fixed synthetic weight comparison. -/
noncomputable def sourceTheorems :
    KIP126.Literature.AdamsSynthetic.SourceTheorems adamsComparison etaClass tmfLabels
      literature.sources.sourceComparisons :=
  literature.theorems.sourceTheorems
    KIP126.Def.standardEInftyWeightShift_natural

/-- The completion, realization and Toda comparisons, together with the
ν-cofiber results, identify the literature statements on the fixed
Adams–synthetic model. -/
theorem sourceApplicability :
    KIP126.Literature.AdamsSynthetic.SourceApplicability adamsComparison etaClass tmfLabels
      literature.sources.sourceComparisons := by
  exact KIP126.Main.Literature.SourceComparisons.application_of_parts
    adamsComparison etaClass tmfLabels literature.sources.sourceComparisons sourceTheorems
    completionApplicability completionComparison realizationComparison
    todaSecondaryComparison nuSourceResults

/-- The tmf detection statements follow from the literature source, the
computation results, the vanishing line and separation on the same sphere.
In particular, stem-125 survival is a deduction in Main. -/
theorem tmfDetectionTheorems :
    KIP126.Literature.AdamsSynthetic.TmfDetectionTheorems adamsComparison tmfLabels :=
  KIP126.Main.Computation.tmf_inputs_of_computation adamsComparison
    computationTheorems sphereVanishing sphereSeparated
    literature.sources.sourceComparisons.tmfSource sourceTheorems.tmf
    literature.sources.sourceComparisons.tmfComparison
    literature.sources.sourceComparisons.algebraDetectionCompatibility.classical_detection

/-- Literature consequences on the standard Adams–synthetic model, combined
with the tmf detection statements proved in Main. -/
noncomputable def literatureTheorems :
    KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems adamsComparison etaClass tmfLabels :=
  KIP126.Literature.AdamsSynthetic.SourceTheorems.toAdamsSyntheticTheorems adamsComparison etaClass tmfLabels
    sourceTheorems sourceApplicability tmfDetectionTheorems

end KIP126.Main.AdamsSynthetic
