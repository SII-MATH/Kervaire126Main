module

public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Choice.Invariance
import all KIP126.Main.Internal.Choice.FinitePages

/-! Paper-owned choice transport (Remark 7.4 and Lemmas 7.10–7.11).
Sources: bbac1fc05843 Main/Solution/ChoiceIndependence and
Route/Selected/ChoiceInvariance (MIT; see the retained source LICENSE). The distinguished BX theorem
is already upstream; normalization and arbitrary-choice transport are not.
-/

@[expose] section
namespace KIP126.Main
open KIP126.Synthetic.Context KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section

/-- The paper's normalization at the already fixed BX source choice.
This was an unproved actual-model target in the pinned source. -/
public theorem normalized_bx_finite (r : ℕ) (hr : 1 ≤ r) :
    SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
      model.standardClasses.standardH6Square ↔
    quotientClass (r+1)
      (KIP126.Literature.Standard.lambdaEtaThetaSquare
        KIP126.Literature.Standard.bxTheta5) = 0 := by
  sorry

/-- The source-to-arbitrary-choice step belongs to the present paper.
Only the lambda-eta-square expression is asserted independent. -/
public theorem lambda_eta_theta_square_independent
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Literature.Standard.lambdaEtaThetaSquare theta =
      KIP126.Literature.Standard.lambdaEtaThetaSquare
        KIP126.Literature.Standard.bxTheta5 := by
  sorry

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

/-- The original finite-page, filtration, and exponent-two proof of C4
invariance, using the fixed upstream table and comparison declarations. -/
public theorem c4_choice_invariant
    (theta theta' : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (htheta : ThetaChoice theta) (htheta' : ThetaChoice theta')
    (hc4 : C4At theta') : C4At theta := by
  exact Internal.Choice.c4_invariance_of_pages Internal.Choice.theta_choice_finite_pages
    theta theta' htheta htheta' hc4

public theorem c4_choice_equivalence :
    C4 ↔ ∀ theta, ThetaChoice theta → C4At theta := by
  constructor
  · rintro ⟨theta', htheta', hc4⟩ theta htheta
    exact c4_choice_invariant theta theta' htheta htheta' hc4
  · intro h
    obtain ⟨theta, htheta⟩ := KIP126.Literature.Standard.theta5_detected_exists
    exact ⟨theta, htheta, h theta htheta⟩

/-- Lemma 7.11 retains the quantification over all U representatives.
Its actual-model theorem was only a target definition in the pinned source. -/
public theorem c5_choice_equivalence :
    C5 ↔ ∀ u, UChoice u → C5At u := by
  sorry

public theorem c4_c5_choice_equivalence :
    (C4 ↔ ∀ theta, ThetaChoice theta → C4At theta) ∧
    (C5 ↔ ∀ u, UChoice u → C5At u) :=
  ⟨c4_choice_equivalence, c5_choice_equivalence⟩

end
end KIP126.Main
