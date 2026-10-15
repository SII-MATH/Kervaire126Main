module

public import KIP126.Main.AdamsSynthetic.Context
public import KIP126.Main.AdamsSynthetic.Toda
public import KIP126.Main.AdamsSynthetic.NuSource
public import KIP126.Main.SectionSeven.TmfDetection
public import KIP126.Computation.Tmf.Model.Data
public import KIP126.Computation.Tmf.CsvE2.Classes.Data
public import KIP126.Computation.Tmf.CsvE2.Data
public import KIP126.Computation.WellFormedness.Tmf.Classes
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Tactic.Ring
public import KIP126.Computation.Hypotheses.Joint
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
public import KIP126.Literature.Background.SphereConvergence
public import KIP126.Def.ClassicalAdams.Convergence.Tower.Separation
public import KIP126.Literature.Background.WeightShift
public import KIP126.Literature.Standard.Sphere.EInfty
public import KIP126.Main.Literature.SourceComparisons.Theorems

@[expose] public section

/-! Literature theorems and computation consequences on the fixed
Adams/synthetic comparison, including Toda relations and tmf detection. -/
namespace KIP126.Main.AdamsSynthetic

theorem sphereSeparated :
    KIP126.Classical.Adams.ClassicalSphereSeparated KIP126.Classical.Adams.standardFoundation.hf2 :=
  KIP126.Classical.Adams.classicalSphereSeparated_of_strongConvergence _
    KIP126.Def.standardSphereApplicability.strongly_convergent

/-- Apply the source results and the background naturality hypothesis to
the same canonical synthetic weight comparison. -/
noncomputable def sourceTheorems :
    KIP126.Literature.AdamsSynthetic.SourceTheorems adamsComparison etaClass tmfLabels
      literature.sources.sourceComparisons :=
  literature.theorems.sourceTheorems
    (KIP126.Synthetic.SpectralSequence.CanonicalWeightShift.natural
      KIP126.Classical.Adams.standardAdamsComparison.towerPresentation
      KIP126.Def.standardEInftyWeightShift
      (Classical.choose_spec
        (KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists
          KIP126.Classical.Adams.standardAdamsComparison.towerPresentation)))

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
  KIP126.Main.SectionSeven.tmf_inputs_of_computation adamsComparison
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
