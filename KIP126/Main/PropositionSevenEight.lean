module

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Main.AdamsSynthetic
public import KIP126.Main.Computation.Lambda
public import KIP126.Main.DifferentialReduction.Conclusion
public import KIP126.Main.TmfDetection
public import KIP126.Main.SectionSeven.AlphaOne
public import KIP126.Main.SectionSeven
import all KIP126.Main.SectionSeven.DifferentialCriterion.Dichotomy

@[expose] public section

/-! LWX Proposition 7.8 (`prop:possible_h_6_sq`): the exclusive
permanence/d₁₂ dichotomy and the criterion for a nonzero d₁₂ on h₆².

The classical-page, θ₅-square and detection arguments are proved in
`SectionSeven.DifferentialCriterion`. The statement retains the η-choice
premise and uses one common set of external hypotheses.
-/

namespace KIP126.Main.SectionSeven.DifferentialCriterion

open private h6_square_dichotomy from KIP126.Main.SectionSeven.DifferentialCriterion.Dichotomy
open KIP126.SpectralSequence.FinitePageCalculus
open KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Synthetic.Context
open KIP126.Main.AdamsSynthetic

/-- The d₃ differential in the ν-cofiber, on the fixed standard sphere model. -/
theorem cnu_d3 :
    KIP126.Computation.SphereAndCofiber.Derived.CnuDifferential computationTheorems.interpretation := by
  exact KIP126.Computation.SphereAndCofiber.cnu_d3 computationTheorems

/-- Multiplication by λ is injective in bidegree (125,130), using the
literature and computation statements on the same standard sphere. -/
theorem lambda_injective_125_130 :
    LambdaInjectiveAt 125 130 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) := by
  exact KIP126.Computation.SphereAndCofiber.lambda_injective_125_130 literatureTheorems computationTheorems

/-- Finite-page survival and permanence consequences for the sphere,
using the given Adams vanishing line. -/
theorem sphere_facts :
    KIP126.Computation.SphereAndCofiber.Derived.SphereFacts computationTheorems.interpretation := by
  exact KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing

/-- The precise F15 detector injectivity used at all three occurrences
of the tmf argument in Proposition 7.8. -/
theorem detector_injective : DetectorInjectiveAt adamsComparison 125 130 15 := by
  exact KIP126.Computation.SphereAndCofiber.detector_injective_125_130_filtration15
    literatureTheorems computationTheorems sphereVanishing sphereSeparated

/-- Proposition 7.9 in the implication form used by the final reduction:
vanishing of the stem-126 d₆ excludes the specified η-extension. -/
theorem eta_extension_excluded_of_d6_vanishes :
    KIP126.Main.Stem126.EtaExtensionObstruction.eta_extension_excluded_of_d6_vanishes
      standardMilnorCooperations adamsComparison sphereClasses etaClass := by
  intro _
  exact KIP126.Main.SectionSeven.proposition_7_9

/-- LWX Proposition 7.8 (`prop:possible_h_6_sq`), including the exclusive
dichotomy and the equivalence with conditions (3), (4) and (5).
All classes, comparisons and external facts refer to the same sphere. -/
theorem _root_.KIP126.Main.proposition_7_8 (input : KIP126.ExternalHypotheses) :
    KIP126.Main.Stem126.OnlyD12.d12_dichotomy_and_condition_equivalence
      standardMilnorCooperations standardAdamsComparison input.computation.interpretation.sphereClasses
      KIP126.Def.standardEta := by
  let lit := input.literature
  let B := lit.sources.sourceComparisons
  let st := lit.theorems.sourceTheorems
    KIP126.Def.standardEInftyWeightShift_natural
  let BHS : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems standardAdamsComparison := st.synthetic.toComparisonTheorems _ B.bhsCompletion
    B.completionApplicability B.completionComparison
    (KIP126.Main.Literature.SourceComparisons.realizationKernel_of_source _
      B.kernelSource st.realizationKernel B.kernelComparison)
  let RL : KIP126.Literature.AdamsSynthetic.RealizationDetectionData standardAdamsComparison := ⟨B.realization,
    KIP126.Main.Literature.SourceComparisons.realization_detection_of_completed_sources _
      B.realization B.bhsCompletion st.realization B.completionApplicability
      B.completionComparison B.realizationComparison⟩
  let CL := KIP126.Literature.AdamsSynthetic.classicalTheoremsOfSource standardAdamsComparison KIP126.Def.standardEta
    B.classicalSource st.classical B.hopfComparison B.synthetic_eta
  let TM := KIP126.Main.Computation.tmf_inputs_of_computation standardAdamsComparison
    input.computation.sphereAndCofiber lit.theorems.sphereVanishing KIP126.Def.standardSphereSeparated
    B.tmfSource st.tmf B.tmfComparison B.algebraDetectionCompatibility.classical_detection
  exact h6_square_dichotomy BHS RL CL B.algebraDetectionCompatibility.action_filtration TM st.bx input.computation.sphereAndCofiber
    (KIP126.Computation.SphereAndCofiber.sphere_facts input.computation lit.theorems.sphereVanishing)
    lit.theorems.sphereVanishing KIP126.Def.standardSphereSeparated

end KIP126.Main.SectionSeven.DifferentialCriterion
