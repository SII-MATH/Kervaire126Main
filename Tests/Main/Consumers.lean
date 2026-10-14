module

import KIP126.Main

/-! Ordinary consumers call the fixed paper theorems directly. The endpoint
is the actual h₆ product on the same sphere, with nonzero E∞ semantics. -/
namespace Tests.Main
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Main

example :
    ((H6SquarePermanent ∧ ¬ D12) ∨ (D12 ∧ ¬ H6SquarePermanent)) ∧
      (D12 ↔ C3 ∧ C4 ∧ C5) := proposition_7_8

example (hc3 : C3) : ¬ C5 := proposition_7_9 hc3

example : NonzeroSurvival model.classical.sphere (2,128)
    model.standardClasses.standardH6Square := h6_sq_permanent

example : NonzeroSurvival model.classical.sphere (2,128)
    (model.sphereAlgebra.product (1,64) (1,64)
      model.standardClasses.standardH6 model.standardClasses.standardH6) := by
  change NonzeroSurvival model.classical.sphere (2,128)
    model.standardClasses.standardH6Square
  exact h6_sq_permanent

example : C3 ↔ SurvivesTo model.classical.sphere 12 (14,139)
    KIP126.Computation.Standard.T := c3_iff_target_survives_twelve

example (hd : D12) : ¬ H6SquarePermanent ∧ C3 := d12_necessary hd

/-- The paper's final reasoning consumes the two intermediate theorems
without requesting a construction or a delivery package from the caller. -/
theorem paperConclusion : H6SquarePermanent := by
  obtain ⟨cases, criterion⟩ := proposition_7_8
  rcases cases with hp | hd
  · exact hp.1
  · obtain ⟨h3, _, h5⟩ := criterion.mp hd.1
    exact False.elim (proposition_7_9 h3 h5)

end Tests.Main
