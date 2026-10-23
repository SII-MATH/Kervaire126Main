module

public import KIP126.AdamsComputation

/-! The d₂-stage analysis, adapted from the first step of the proof of
AimPaper Corollary 1.5 using Adams's one-line differentials, Lin's Ext⁴
calculation, and Leibniz. Squares have no upper index cutoff at this stage;
HHR is a separate later-page input. -/
@[expose] section
namespace KIP126.SSComputation
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

public def TwoLineD2Candidate (i j : ℕ) : Prop :=
  (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
  (i = 1 ∧ 3 ≤ j) ∨ i = j ∨
  (i = 2 ∧ j = 5) ∨ (i = 3 ∧ j = 5) ∨ (i = 3 ∧ j = 6) ∨
  (i = 0 ∧ j = 4)

/-- Only E₃ reachability is assumed, with E₂ nonzero and ordered indices.
This contains neither the later excluding differentials nor HHR's cutoff. -/
public theorem two_line_d2_candidates (i j : ℕ) (hij : i ≤ j)
    (hne : KIP126.Literature.Standard.hiProduct i j ≠ 0)
    (hreach : ReachesPage model.classical.sphere 3 (hiDegree i + hiDegree j)
      (KIP126.Literature.Standard.hiProduct i j)) : TwoLineD2Candidate i j := by
  sorry

end KIP126.SSComputation
