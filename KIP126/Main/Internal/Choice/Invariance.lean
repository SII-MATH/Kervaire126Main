module
public import KIP126.Main.Conditions
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.Choice.Gap
import all KIP126.Main.Internal.Choice.Filtration
import all KIP126.Main.Internal.Choice.OrderTwo

/-! Original Theta5SquareNonzeroDetection choice-transport proof in Selected/ChoiceInvariance:856–881,
bbac1fc05843 (MIT). All external facts are fixed upstream declarations. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem theta5_square_nonzero_detection_invariance_of_pages
    (hpages : Subsingleton (model.classical.sphere.Page 3 (3,65)) ∧
      Subsingleton (model.classical.sphere.Page 3 (4,66)) ∧
      Subsingleton (model.classical.sphere.Page 4 (5,67)))
    (θ θ' : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (hθ : ThetaChoice θ) (hθ' : ThetaChoice θ')
    (hc : Theta5SquareNonzeroDetectionAt θ') : Theta5SquareNonzeroDetectionAt θ := by
  classical
  have hd := theta_choice_filtration_gap_of_pages hpages θ θ' hθ hθ'
  have hsq : FiltrationAtLeast model.syntheticTower 12
      (sphereProduct θ θ-sphereProduct θ' θ') := by
    rw [theta_square_difference θ θ' (theta_degree_order_two θ')]
    exact KIP126.Literature.Standard.action_filtration .sphere 62 64 62 64 6 6
      (θ-θ') (θ-θ') hd hd
  refine ⟨?_,hc.2⟩
  apply detects_of_difference_in_next_filtration (model.convergence .sphere) (10,134,128) hc.1
  exact model.syntheticTower.filtrationSubmodule_antitone
    (S_0_0 : SyntheticSpectrum) (124,128) (by decide : (11:ℤ)≤12) hsq

end
end KIP126.Main.Internal.Choice
end
