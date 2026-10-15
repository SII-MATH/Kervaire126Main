module
public import KIP126.Main.ChoiceIndependence
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Selected.TargetFrame
import all KIP126.Main.Internal.Selected.ProductZero

/-! The dichotomy and both implications of Proposition 7.8, preserving
Selected/Assembly:247–304. The high-filtration detector argument is isolated
as a proved local dependency and is supplied by its separate paper proof. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Literature.Standard (eta bxTheta5)
open KIP126.Computation.Standard (T)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private abbrev bxEtaSquare : BiHom 125 130 (S_0_0 : SyntheticSpectrum) :=
  sphereProduct eta (sphereProduct bxTheta5 bxTheta5)

private theorem permanent_of_filtration_fifteen
    (hzero : FiltrationAtLeast model.syntheticTower 15 bxEtaSquare → bxEtaSquare=0)
    (hf : FiltrationAtLeast model.syntheticTower 15 bxEtaSquare) : H6SquarePermanent := by
  apply KIP126.Literature.Standard.bx_untruncated.mpr
  change lambdaMultiply 1 bxEtaSquare=0
  rw [hzero hf]
  simp only [lambdaMultiply,comp_zero]

private theorem selected_dichotomy
    (hzero : FiltrationAtLeast model.syntheticTower 15 bxEtaSquare → bxEtaSquare=0) :
    H6SquarePermanent ∨ D12 := by
  have hf14 : FiltrationAtLeast model.syntheticTower 14 bxEtaSquare := by
    rcases theta_three_cases bxTheta5 with h4|hbranch
    · exact c4_eta_filtration_fourteen h1_u_zero bxTheta5 h4
    · exact model.syntheticTower.filtrationSubmodule_antitone _ (125,130) (by decide : (14:ℤ)≤15)
        (eta_weight128_branches_filtration_fifteen (sphereProduct bxTheta5 bxTheta5) hbranch)
  by_cases hf15 : FiltrationAtLeast model.syntheticTower 15 bxEtaSquare
  · exact Or.inl (permanent_of_filtration_fifteen hzero hf15)
  · exact Or.inr (bx_lambda_nine_not_ten_d12 target_page_twelve_frame
      ((lambda_9_iff_filtration_14 bxEtaSquare).mpr hf14)
      (fun h => hf15 ((lambda_10_iff_filtration_15 bxEtaSquare).mp h)))

private theorem selected_forward
    (hzero : FiltrationAtLeast model.syntheticTower 15 bxEtaSquare → bxEtaSquare=0)
    (hd : D12) : C4∧C5 := by
  have impossible (hf : FiltrationAtLeast model.syntheticTower 15 bxEtaSquare) : False :=
    (d12_necessary hd).1 (permanent_of_filtration_fifteen hzero hf)
  have h4 : C4At bxTheta5 := by
    rcases theta_three_cases bxTheta5 with h4|hbranch
    · exact h4
    · exact False.elim (impossible
        (eta_weight128_branches_filtration_fifteen (sphereProduct bxTheta5 bxTheta5) hbranch))
  refine ⟨⟨bxTheta5,KIP126.Literature.Standard.bx_theta_label,h4⟩,?_⟩
  obtain ⟨u,hu⟩ := u_choice_exists
  let c : BiHom 125 133 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 3 (sphereProduct eta u)
  have hc14 : FiltrationAtLeast model.syntheticTower 14 c :=
    u_choice_eta_lambda_three_filtration_fourteen h1_u_zero u hu
  have hframe := target_infinity_frame KIP126.Main.SectionSeven.Internal.target_page_six_frame
  rcases theta_detection_step (14,139,133) (model.comparison.sphereE2 14 139 6 T)
      hframe c hc14 with hdet|hc15
  · exact ⟨u,hu,hdet.1⟩
  · exfalso
    apply impossible
    have hf13 := theta_sphere_frame 13 137 9 (by decide) (by decide) _ correction_infinity_generated
    have he := theta_u_eta_filtration_error hf13 bxTheta5 h4 u hu
    have hl := lambda_three_preserves_filtration_fifteen c hc15
    change bxEtaSquare-(show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 c)∈
      model.syntheticTower.filtrationSubmodule (S_0_0 : SyntheticSpectrum) 15 (125,130) at he
    have hh := (model.syntheticTower.filtrationSubmodule (S_0_0 : SyntheticSpectrum) 15 (125,130)).add_mem he hl
    simpa only [sub_add_cancel,FiltrationAtLeast,Int.reduceAdd] using hh

private theorem selected_reverse (hc3 : C3) (hc4 : C4) (hc5 : C5) : D12 := by
  obtain ⟨theta,htheta,h4⟩ := hc4
  obtain ⟨u,hu,h5⟩ := hc5
  have h4' := c4_choice_invariant bxTheta5 theta KIP126.Literature.Standard.bx_theta_label htheta h4
  have hf13 := theta_sphere_frame 13 137 9 (by decide) (by decide) _ correction_infinity_generated
  have hdetect := c4_c5_eta_target_detected hf13 bxTheta5 h4' u hu h5
  have hn := target_detected_not_filtration_fifteen T (c3_iff_target_survives_twelve.mp hc3) _ hdetect
  exact bx_lambda_nine_not_ten_d12 target_page_twelve_frame
    ((lambda_9_iff_filtration_14 bxEtaSquare).mpr (c4_eta_filtration_fourteen h1_u_zero bxTheta5 h4'))
    (fun h => hn ((lambda_10_iff_filtration_15 bxEtaSquare).mp h))

end
end KIP126.Main.Internal.Selected
