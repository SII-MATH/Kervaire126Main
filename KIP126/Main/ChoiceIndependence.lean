module

public import KIP126.Main.Conditions
import KIP126.Computation.Table.Values
import KIP126.AdamsSynthetic.Standard.ClassicalSupport
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
open CategoryTheory KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus KIP126.Computation.Table
open KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- Remark 7.4: cancel one lambda using the actual source-page calculation
in degree (3,129), then apply the original fixed-choice BX criterion. -/
private theorem normalized_bx_finite (r : ℕ) (hr : 1 ≤ r) :
    SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
      model.standardClasses.standardH6Square ↔
    quotientClass (r+1)
      (KIP126.Literature.Standard.lambdaEtaThetaSquare
        KIP126.Literature.Standard.bxTheta5) = 0 := by
  exact (KIP126.Literature.Standard.bx_finite r hr).trans
    (Internal.Choice.Completion.normalized_quotient r
      (KIP126.Literature.Standard.etaThetaSquare KIP126.Literature.Standard.bxTheta5))

private theorem h6_square_basis : basis .sphere 2 128 0 =
    model.standardClasses.standardH6Square := by
  have h := basis_value ⟨.mul (.named .h6) (.named .h6),0⟩ (by decide)
  change basis .sphere 2 128 0 = KIP126.Computation.Standard.product (r := (2,128))
    (KIP126.Computation.Standard.atom .h6) (KIP126.Computation.Standard.atom .h6) at h
  dsimp only [KIP126.Computation.Standard.product] at h
  simpa [KIP126.Computation.Standard.atom_h6,
    model.standardClasses.standardH6Square_eq_product] using h

/-- The fixed table records the actual square reaching E7, independently of
the paper's final permanence theorem or the positive-r BX criterion. -/
private theorem h6_square_reaches_seven : ReachesPage model.classical.sphere 7 (2,128)
    model.standardClasses.standardH6Square := by
  have hrow := result ⟨.sphere,.reaches,7,2,128,[0],2,128,[],"S0_AdamsE2_ss",2314⟩
    (List.mem_of_getElem? (i := 146) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 128 [0] = true := rfl
  simp only [decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at h
  rw [←h6_square_basis]
  exact h

/-- At the r=0 endpoint, the square is nonzero on E3: it reaches that page,
and the only possible incoming d2 has zero source E2^(0,127). -/
private theorem h6_square_survives_three : SurvivesTo model.classical.sphere 3 (2,128)
    model.standardClasses.standardH6Square := by
  obtain ⟨a,ha⟩ := reaches_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7)
    h6_square_reaches_seven
  refine ⟨a,ha,?_⟩
  apply represents_next_nonzero_of_incoming_zero
    (E := model.classical.sphere) (r := 2) (p := (2,128))
    (by simpa only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj,
      model.classical.firstPage] using (le_refl (2:ℤ))) (by decide) ?_ ha
    (RepresentsOnPage.self_two _) KIP126.Computation.Standard.square_nonzero
  have he : (2,128)-model.classical.sphere.diffDeg 2 = ((0,127) : ℤ×ℤ) := by
    simp only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj,
      model.classical.differentialDegree, Prod.mk_sub_mk, Int.reduceSub]
  rw [he]
  letI := KIP126.AdamsSynthetic.Standard.sphere_page_filtration_zero 2 127 (by decide)
  ext x
  rw [Subsingleton.elim x 0]
  simp

/-- Every lambda multiple vanishes in the first quotient; this endpoint
requires no detection or order-two condition on theta. -/
private theorem lambda_eta_theta_square_mod_lambda_zero
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    quotientClass 1 (KIP126.Literature.Standard.lambdaEtaThetaSquare theta) = 0 := by
  exact (Internal.Choice.Completion.quotient_zero_iff_multiple 1 129 _).mpr
    ⟨KIP126.Literature.Standard.etaThetaSquare theta, HEq.rfl⟩

/-- The source-to-arbitrary-choice step belongs to the present paper.
The square difference has high filtration; the Section 7 eta-error and tmf
arguments annihilate it. Only the lambda-eta-square expression is asserted
independent, as in Remark 7.5. -/
private theorem lambda_eta_theta_square_independent
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
      KIP126.Literature.Standard.bx_order_two]
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
  have heq := Internal.High125.detector_injective_filtration15 _ herror
    (Internal.High125.eta_product_difference_order_two 124 128
      (sphereProduct theta theta) (sphereProduct theta' theta')) (by
    rw [CategoryTheory.Preadditive.sub_comp,
      Internal.High125.synthetic_eta_theta_square_detector_zero theta,
      Internal.High125.synthetic_eta_theta_square_detector_zero theta', sub_self])
  have h := congrArg (lambdaMultiply 1) (sub_eq_zero.mp heq)
  exact h

/-- The complete normalized criterion at any admissible theta choice, for
every natural r. The r=0 case is the independent E3/first-quotient endpoint;
positive r uses the original fixed-choice BX criterion and choice transport. -/
public theorem any_choice_criterion
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    (∀ r : ℕ,
      (SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
        model.standardClasses.standardH6Square ↔
        quotientClass (r+1) (KIP126.Literature.Standard.lambdaEtaThetaSquare theta) = 0)) ∧
    (H6SquarePermanent ↔ KIP126.Literature.Standard.lambdaEtaThetaSquare theta = 0) := by
  have he := lambda_eta_theta_square_independent theta htheta
  constructor
  · intro r
    cases r with
    | zero =>
      exact ⟨fun _ => lambda_eta_theta_square_mod_lambda_zero theta,
        fun _ => h6_square_survives_three⟩
    | succ r =>
      rw [he]
      exact normalized_bx_finite (r+1) (by omega)
  · rw [he]
    exact KIP126.Literature.Standard.bx_untruncated

/-- The original finite-page, filtration, and exponent-two proof of Theta5SquareNonzeroDetection
invariance, using the fixed upstream table and comparison declarations. -/
private theorem theta5_square_nonzero_detection_choice_invariant
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

private theorem square_and_eta_detection_choice_equivalence :
    (Theta5SquareNonzeroDetection ↔ ∀ theta, ThetaChoice theta → Theta5SquareNonzeroDetectionAt theta) ∧
    (EtaExtensionDetection ↔ ∀ u, UChoice u → EtaExtensionDetectionAt u) :=
  ⟨theta5_square_nonzero_detection_choice_equivalence, eta_extension_detection_choice_equivalence⟩

end
end KIP126.Main
