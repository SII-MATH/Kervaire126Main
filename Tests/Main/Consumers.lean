module

import KIP126.Main

/-! Ordinary consumers call the fixed paper theorems directly. The endpoint
is the actual h₆ product on the same sphere, with nonzero E∞ semantics. -/
namespace Tests.Main
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Main

example :
    ((H6SquarePermanent ∧ ¬ H6SquareSupportsD12) ∨ (H6SquareSupportsD12 ∧ ¬ H6SquarePermanent)) ∧
      (H6SquareSupportsD12 ↔ Stem126D6Vanishes ∧ Theta5SquareNonzeroDetection ∧ EtaExtensionDetection) := h6_square_differential_dichotomy_and_criterion

example (hc3 : Stem126D6Vanishes) : ¬ EtaExtensionDetection := eta_extension_excluded_of_d6_vanishes hc3

example : NonzeroSurvival model.classical.sphere (2,128)
    model.standardClasses.standardH6Square := h6_sq_permanent

example : NonzeroSurvival model.classical.sphere (2,128)
    (model.sphereAlgebra.product (1,64) (1,64)
      model.standardClasses.standardH6 model.standardClasses.standardH6) := by
  change NonzeroSurvival model.classical.sphere (2,128)
    model.standardClasses.standardH6Square
  exact h6_sq_permanent

example (hd : H6SquareSupportsD12) : ¬ H6SquarePermanent ∧ Stem126D6Vanishes := by
  obtain ⟨cases, criterion⟩ := h6_square_differential_dichotomy_and_criterion
  refine ⟨?_, (criterion.mp hd).1⟩
  rcases cases with hp | hn
  · exact False.elim (hp.2 hd)
  · exact hn.2

/-- The paper's final reasoning consumes the two intermediate theorems
without requesting a construction or a delivery package from the caller. -/
theorem paperConclusion : H6SquarePermanent := by
  obtain ⟨cases, criterion⟩ := h6_square_differential_dichotomy_and_criterion
  rcases cases with hp | hd
  · exact hp.1
  · obtain ⟨h3, _, h5⟩ := criterion.mp hd.1
    exact False.elim (eta_extension_excluded_of_d6_vanishes h3 h5)

end Tests.Main
