module

import KIP126.SSComputation

/-! Later-page results remain callable through the new entry using the same
fixed E₂ classes, without a model or computation-result package argument. -/
namespace Tests.SSComputation
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard

theorem finiteAndPermanent :
    SurvivesTo model.classical.sphere 6 (8,134) W ∧
      IsPermanentCycle model.classical.sphere (14,139) T ∧
      NonzeroSurvival model.classical.sphere (10,134) U :=
  ⟨w_to_e6, t_permanent_cycle, u_permanent⟩

theorem literatureOneLine :
    HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65) h6 (product h0 h5Square) :=
  d2_h6

/- h₀h₄ reaches the candidate stage before its separate d₃ exclusion.
All square indices likewise remain candidates before the HHR input. -/
example : KIP126.SSComputation.TwoLineD2Candidate 0 4 := by
  unfold KIP126.SSComputation.TwoLineD2Candidate
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩)))))))

example (j : ℕ) : KIP126.SSComputation.TwoLineD2Candidate j j := by
  unfold KIP126.SSComputation.TwoLineD2Candidate
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

example : True := by
  fail_if_success have _ : NonzeroSurvival model.classical.sphere (8,134) W := w_to_e6
  fail_if_success have _ : NonzeroSurvival model.classical.sphere (14,139) T := t_permanent_cycle
  trivial

/-- The two source partitions recover certification of the original combined
claim list, using ordinary public imports and the original fixed objects. -/
theorem combinedClaimCertification (c : KIP126.Computation.Table.Raw.Claim)
    (hc : c ∈ KIP126.Computation.Table.Raw.claims ++
      KIP126.Computation.Table.Raw.directD2Claims) : KIP126.Computation.Table.Statement c := by
  rcases List.mem_append.mp hc with hs | hd
  · exact KIP126.Computation.Table.result c hs
  · exact KIP126.Computation.Table.direct_d2_result c hd

end Tests.SSComputation
