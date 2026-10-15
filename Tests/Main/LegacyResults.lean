module

import KIP126.Main

/-! Selected paper results remain usable through the ordinary public entry.
Representative construction details are checked in Main.InternalAudit. -/
namespace Tests.Main
open KIP126.Main KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)

example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Literature.deltaH6Square model =
      KIP126.Literature.Standard.lambdaEtaThetaSquare theta :=
  delta_h6_square_eq_lambda_eta_theta_square theta htheta

example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    H6SquarePermanent ↔ KIP126.Literature.Standard.lambdaEtaThetaSquare theta = 0 :=
  (any_choice_criterion theta htheta).2

example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta)
    (r : ℕ) :
    KIP126.Core.SpectralSequence.SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
      model.standardClasses.standardH6Square ↔
    quotientClass (r+1) (KIP126.Literature.Standard.lambdaEtaThetaSquare theta) = 0 :=
  (any_choice_criterion theta htheta).1 r

-- The first quotient gives the newly covered r=0 endpoint through a normal import.
example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Core.SpectralSequence.SurvivesTo model.classical.sphere 3 (2,128)
      model.standardClasses.standardH6Square ↔
    quotientClass 1 (KIP126.Literature.Standard.lambdaEtaThetaSquare theta) = 0 :=
  (any_choice_criterion theta htheta).1 0

-- Positive r retains the original page/exponent indexing.
example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta) :
    KIP126.Core.SpectralSequence.SurvivesTo model.classical.sphere 4 (2,128)
      model.standardClasses.standardH6Square ↔
    quotientClass 2 (KIP126.Literature.Standard.lambdaEtaThetaSquare theta) = 0 :=
  (any_choice_criterion theta htheta).1 1

example : Theta5SquareNonzeroDetection ↔
    ∀ theta, ThetaChoice theta → Theta5SquareNonzeroDetectionAt theta :=
  theta5_square_nonzero_detection_choice_equivalence

example : EtaExtensionDetection ↔ ∀ u, UChoice u → EtaExtensionDetectionAt u :=
  eta_extension_detection_choice_equivalence

example (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
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

end Tests.Main
