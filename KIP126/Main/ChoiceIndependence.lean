module

public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Choice.Invariance
import all KIP126.Main.Internal.Choice.FinitePages
import all KIP126.Main.Internal.High125.Injectivity
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Selected.ProductDetection
import all KIP126.Main.Internal.Choice.Completion

/-! Paper-owned choice transport (Remarks 7.4–7.5 and Lemmas 7.10–7.11).
Sources: bbac1fc05843 Main/Solution/ChoiceIndependence and
Route/Selected/ChoiceInvariance (MIT; see the retained source LICENSE). The distinguished BX theorem
is already upstream; normalization and arbitrary-choice transport are not.
-/

@[expose] section
namespace KIP126.Main
open KIP126.Synthetic.Context KIP126.Core.SpectralSequence
open KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Remark 7.4: cancel one lambda using the actual source-page calculation
in degree (3,129), then apply the original fixed-choice BX criterion. -/
public theorem normalized_bx_finite (r : ℕ) (hr : 1 ≤ r) :
    SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
      model.standardClasses.standardH6Square ↔
    quotientClass (r+1)
      (KIP126.Literature.Standard.lambdaEtaThetaSquare
        KIP126.Literature.Standard.bxTheta5) = 0 := by
  exact (KIP126.Literature.Standard.bx_finite r hr).trans
    (Internal.Choice.Completion.normalized_quotient r
      (KIP126.Literature.Standard.etaThetaSquare KIP126.Literature.Standard.bxTheta5))

/-- The source-to-arbitrary-choice step belongs to the present paper.
The square difference has high filtration; the Section 7 eta-error and tmf
arguments annihilate it. Only the lambda-eta-square expression is asserted
independent, as in Remark 7.5. -/
public theorem lambda_eta_theta_square_independent
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Literature.Standard.lambdaEtaThetaSquare theta =
      KIP126.Literature.Standard.lambdaEtaThetaSquare
        KIP126.Literature.Standard.bxTheta5 := by
  classical
  let theta' := KIP126.Literature.Standard.bxTheta5
  have hgap := Internal.Choice.theta_choice_filtration_gap_of_pages
    Internal.Choice.theta_choice_finite_pages theta theta' htheta
    KIP126.Literature.Standard.bx_theta_label
  have hsquare : FiltrationAtLeast model.syntheticTower 12
      (sphereProduct theta theta - sphereProduct theta' theta') := by
    rw [Internal.Choice.theta_square_difference theta theta'
      (Internal.Choice.theta_degree_order_two theta')]
    exact KIP126.Literature.Standard.action_filtration .sphere 62 64 62 64 6 6
      (theta-theta') (theta-theta') hgap hgap
  have herror := Internal.Selected.eta_weight128_branches_filtration_fifteen _
    (Internal.Selected.stem124_weight128_filtration11_branches
      (Internal.Selected.theta_sphere_frame 13 137 9 (by decide) (by decide) _
        Internal.Selected.correction_infinity_generated) _
      (model.syntheticTower.filtrationSubmodule_antitone _ (124,128)
        (by decide : (11:ℤ) ≤ 12) hsquare))
  have hlinear : sphereProduct KIP126.Literature.Standard.eta
      (sphereProduct theta theta - sphereProduct theta' theta') =
      sphereProduct KIP126.Literature.Standard.eta (sphereProduct theta theta) -
        sphereProduct KIP126.Literature.Standard.eta (sphereProduct theta' theta') := by
    simp only [sphereProduct, Int.reduceAdd, CategoryTheory.Preadditive.comp_sub]
  rw [hlinear] at herror
  have heq := Internal.High125.detector_injective_filtration15 _ herror (by
    rw [CategoryTheory.Preadditive.sub_comp,
      Internal.High125.synthetic_eta_theta_square_detector_zero theta,
      Internal.High125.synthetic_eta_theta_square_detector_zero theta', sub_self])
  have h := congrArg (lambdaMultiply 1) (sub_eq_zero.mp heq)
  exact h

/-- The complete normalized criterion at any admissible theta choice. -/
public theorem any_choice_criterion
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    (∀ r : ℕ, 1 ≤ r →
      (SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
        model.standardClasses.standardH6Square ↔
        quotientClass (r+1) (KIP126.Literature.Standard.lambdaEtaThetaSquare theta) = 0)) ∧
    (H6SquarePermanent ↔ KIP126.Literature.Standard.lambdaEtaThetaSquare theta = 0) := by
  have he := lambda_eta_theta_square_independent theta htheta
  constructor
  · intro r hr
    rw [he]
    exact normalized_bx_finite r hr
  · rw [he]
    exact KIP126.Literature.Standard.bx_untruncated

/-- The original finite-page, filtration, and exponent-two proof of Theta5SquareNonzeroDetection
invariance, using the fixed upstream table and comparison declarations. -/
public theorem theta5_square_nonzero_detection_choice_invariant
    (theta theta' : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (htheta : ThetaChoice theta) (htheta' : ThetaChoice theta')
    (hc4 : Theta5SquareNonzeroDetectionAt theta') : Theta5SquareNonzeroDetectionAt theta := by
  exact Internal.Choice.theta5_square_nonzero_detection_invariance_of_pages Internal.Choice.theta_choice_finite_pages
    theta theta' htheta htheta' hc4

public theorem theta5_square_nonzero_detection_choice_equivalence :
    Theta5SquareNonzeroDetection ↔ ∀ theta, ThetaChoice theta → Theta5SquareNonzeroDetectionAt theta := by
  constructor
  · rintro ⟨theta', htheta', hc4⟩ theta htheta
    exact theta5_square_nonzero_detection_choice_invariant theta theta' htheta htheta' hc4
  · intro h
    obtain ⟨theta, htheta⟩ := KIP126.Literature.Standard.theta5_detected_exists
    exact ⟨theta, htheta, h theta htheta⟩

/-- Lemma 7.11 retains the quantification over all U representatives.
Multiplication by lambda-three eta sends their ambiguity to filtration 15,
which leaves the filtration-14 detection unchanged. -/
public theorem eta_extension_detection_choice_equivalence :
    EtaExtensionDetection ↔ ∀ u, UChoice u → EtaExtensionDetectionAt u := by
  constructor
  · rintro ⟨v,hv,hdet⟩ u hu
    exact Internal.Choice.detects_of_difference_in_next_filtration
      (model.convergence .sphere) (14,139,133) hdet
      (Internal.Choice.Completion.u_eta_difference_fifteen u v hu hv)
  · intro h
    obtain ⟨u,hu⟩ := Internal.Selected.u_choice_exists
    exact ⟨u,hu,h u hu⟩

public theorem square_and_eta_detection_choice_equivalence :
    (Theta5SquareNonzeroDetection ↔ ∀ theta, ThetaChoice theta → Theta5SquareNonzeroDetectionAt theta) ∧
    (EtaExtensionDetection ↔ ∀ u, UChoice u → EtaExtensionDetectionAt u) :=
  ⟨theta5_square_nonzero_detection_choice_equivalence, eta_extension_detection_choice_equivalence⟩

end
end KIP126.Main
