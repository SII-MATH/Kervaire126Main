module

import KIP126.Main

/-! Ordinary public consumers of the mathematical replacements for the old
Main axioms. All objects belong to the same fixed sphere and comparison. -/

namespace Tests.Main
open KIP126.Main KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Literature.Standard (eta bxTheta5)

example : ∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u :=
  u_choice_exists

example (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    ∃ y : BiHom 125 139 (S_0_0 : SyntheticSpectrum),
      lambdaMultiply 3 (sphereProduct eta u) = lambdaMultiply 6 y :=
  lambda_three_eta_u_eq_lambda_six u hu

example (u v : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (hu : UChoice u) (hv : UChoice v) :
    FiltrationAtLeast model.syntheticTower 14
      (lambdaMultiply 3 (sphereProduct eta u) -
        lambdaMultiply 3 (sphereProduct eta v)) :=
  lambda_three_eta_u_difference_filtration_fourteen u v hu hv

example (hc3 : C3) (h : ∀ u, UChoice u → C5At u) : False := table1 hc3 h

-- Recover the former three-possibility shape with actual representatives.
example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (_htheta : ThetaChoice theta) :
    (∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u ∧
      sphereProduct theta theta = lambdaMultiply 6 u) ∨
    (∃ c : BiHom 124 137 (S_0_0 : SyntheticSpectrum),
      sphereProduct theta theta = lambdaMultiply 9 c) ∨
    (∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum),
      sphereProduct theta theta = lambdaMultiply 10 a) := by
  rcases theta_square_three_possibilities theta with h6 | h9 | h10
  · exact Or.inl h6
  · obtain ⟨c, _, hc⟩ := h9
    exact Or.inr (Or.inl ⟨c, hc⟩)
  · exact Or.inr (Or.inr h10)

example : KIP126.Literature.deltaH6Square model =
    KIP126.Literature.Standard.lambdaEtaThetaSquare bxTheta5 :=
  delta_h6_square_bx

example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Literature.deltaH6Square model =
      KIP126.Literature.Standard.lambdaEtaThetaSquare theta :=
  delta_h6_square_eq_lambda_eta_theta_square theta htheta

end Tests.Main
