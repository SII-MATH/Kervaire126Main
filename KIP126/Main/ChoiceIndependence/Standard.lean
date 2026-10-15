module

public import KIP126.Main.ChoiceIndependence.BJMInduction
public import KIP126.Main.ChoiceIndependence.DetectionEquivalence
public import KIP126.Main.AdamsSynthetic

@[expose] public section

/-! The choice-independent criteria on the fixed standard sphere.
These interfaces specialize the generic proofs using the same correlated
literature/computation witnesses as the rest of Main. The finite criterion
includes r = 0; no use of the final permanence theorem is made. -/
namespace KIP126.Main

open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.SyntheticTheta5 KIP126.Main.AdamsSynthetic

noncomputable section

/-- Remarks 7.4–7.5: the normalized criterion for every natural r and every
admissible theta choice, together with its untruncated counterpart. -/
theorem any_choice_criterion
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice standardMilnorCooperations adamsComparison.toAdamsComparisonData theta) :
    (∀ r : ℕ, SurvivesTo sphereAdamsData ((r : ℤ) + 3) (2, 128) standardH6Square ↔
      VanishesModLambda (r + 1) (lambdaEtaThetaSquare etaClass theta)) ∧
    (NonzeroSurvival sphereAdamsData (2, 128) standardH6Square ↔
      lambdaEtaThetaSquare etaClass theta = 0) := by
  exact Stem126.BJMInduction.any_choice_criterion_all_r literatureTheorems computationTheorems
    literature.sources.sourceComparisons.algebraDetectionCompatibility.action_filtration
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing)
    sphereVanishing sphereSeparated theta htheta

/-- The actual connecting-map formula at any admissible theta, transported
from the distinguished BX choice by the proved choice independence. -/
theorem delta_h6_square_eq_lambda_eta_theta_square
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice standardMilnorCooperations adamsComparison.toAdamsComparisonData theta) :
    deltaH6Square standardFoundation.hf2 standardMilnorCooperations adamsComparison.sphereFirstQuotient =
      lambdaEtaThetaSquare etaClass theta := by
  obtain ⟨source, hsource, hboundary, _⟩ := literatureTheorems.bx
  exact hboundary.trans
    (Stem126.BJMInduction.lambda_eta_theta_square_independent literatureTheorems computationTheorems
      literature.sources.sourceComparisons.algebraDetectionCompatibility.action_filtration
      (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing)
      sphereVanishing sphereSeparated theta source htheta hsource.2.1).symm

/-- Lemma 7.10: condition (4) is independent of the admissible theta representative. -/
theorem theta5_square_nonzero_detection_choice_equivalence :
    Theta5SquareNonzeroDetection standardMilnorCooperations adamsComparison.toAdamsComparisonData sphereClasses ↔
      ∀ theta, ThetaChoice standardMilnorCooperations adamsComparison.toAdamsComparisonData theta →
        Theta5SquareNonzeroDetectionAt standardMilnorCooperations adamsComparison.toAdamsComparisonData sphereClasses theta := by
  exact ChoiceIndependence.theta5_square_detection_choice_equivalence computationTheorems
    literatureTheorems.synthetic literatureTheorems.realization literatureTheorems.classical
    literature.sources.sourceComparisons.algebraDetectionCompatibility.action_filtration
    literatureTheorems.bx

/-- Lemma 7.11: condition (5) is independent of the detected U representative. -/
theorem eta_extension_detection_choice_equivalence :
    EtaExtensionDetection standardMilnorCooperations adamsComparison.toAdamsComparisonData sphereClasses etaClass ↔
      ∀ u, UChoice standardMilnorCooperations adamsComparison.toAdamsComparisonData sphereClasses u →
        EtaExtensionDetectionAt standardMilnorCooperations adamsComparison.toAdamsComparisonData sphereClasses etaClass u := by
  exact ChoiceIndependence.eta_extension_detection_choice_equivalence computationTheorems
    literatureTheorems.synthetic
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing)
    etaClass literatureTheorems.classical.hopf.1

end
end KIP126.Main
