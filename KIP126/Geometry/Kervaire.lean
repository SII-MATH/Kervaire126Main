module

public import KIP126.Literature
import KIP126.Main

/-! AimPaper Theorem 1.1 and Corollary 1.2. The geometric objects, invariant
and Browder bridge belong to Literature. Both deductions below have complete
local proofs and no caller-supplied source package or extra hypotheses.
Their transitive upstream construction/proof obligations remain open.
-/

@[expose] section
namespace KIP126.Geometry
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Literature.Geometry

private theorem square_survives_iff (j : ℕ) :
    NonzeroSurvival model.classical.sphere (2, ((2 ^ (j + 1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) ↔ j ≤ 6 := by
  constructor
  · intro h
    by_contra hn
    exact KIP126.Literature.Standard.hhr_high_squares_not_permanent j (by omega) h
  · intro hj
    by_cases hlow : j ≤ 3
    · exact KIP126.Literature.Standard.may_low_squares_permanent j hlow
    · have cases : j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases cases with rfl | rfl | rfl
      · exact KIP126.Literature.Standard.mahowald_tangora_h4_square_permanent
      · exact KIP126.Literature.Standard.h5Square_permanent
      · exact KIP126.Main.h6_sq_permanent

private theorem admissible_dimensions (n : ℕ) :
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ 6 ∧ n = 2 ^ (j + 1) - 2) ↔
      n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  constructor
  · rintro ⟨j, hj, hj', rfl⟩
    interval_cases j <;> norm_num
  · intro hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by decide, by decide, by decide⟩
    · exact ⟨2, by decide, by decide, by decide⟩
    · exact ⟨3, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨5, by decide, by decide, by decide⟩
    · exact ⟨6, by decide, by decide, by decide⟩

/-- AimPaper Theorem 1.1: a closed smooth stably framed manifold of
Kervaire invariant one exists in dimension 126. -/
public theorem kervaire_invariant_one_126 : KervaireInvariantOneExists 126 := by
  exact (browder_iff 126).mpr ⟨6, by decide, by decide, KIP126.Main.h6_sq_permanent⟩

/-- AimPaper Corollary 1.2: precisely the six stated dimensions admit a
closed smooth stably framed manifold of Kervaire invariant one. -/
public theorem kervaire_invariant_one_iff (n : ℕ) :
    KervaireInvariantOneExists n ↔
      n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  rw [browder_iff, ← admissible_dimensions]
  constructor
  · rintro ⟨j, hj, hn, hs⟩
    exact ⟨j, hj, (square_survives_iff j).mp hs, hn⟩
  · rintro ⟨j, hj, hs, hn⟩
    exact ⟨j, hj, hn, (square_survives_iff j).mpr hs⟩

end KIP126.Geometry
