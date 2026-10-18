module

import KIP126.Geometry

/-! Ordinary consumption of the two geometric conclusions, retaining real
manifold witnesses, the exact dimension list, and the positive-index boundary.
-/
open KIP126.Literature.Geometry KIP126.Geometry

example : KervaireInvariantOneExists 126 := kervaire_invariant_one_126

example : ∃ M : ClosedStablyFramedManifold 126, kervaireInvariant 31 M = 1 := by
  obtain ⟨k, hk, M, hM⟩ := kervaire_invariant_one_126
  have hk' : k = 31 := by omega
  subst k
  exact ⟨M, hM⟩

example (n : ℕ) : KervaireInvariantOneExists n ↔
    n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 :=
  kervaire_invariant_one_iff n

example : KervaireInvariantOneExists 2 ∧ KervaireInvariantOneExists 6 ∧
    KervaireInvariantOneExists 14 ∧ KervaireInvariantOneExists 30 ∧
    KervaireInvariantOneExists 62 ∧ KervaireInvariantOneExists 126 := by
  simp only [kervaire_invariant_one_iff]
  decide

example : ¬ KervaireInvariantOneExists 0 := by
  rw [kervaire_invariant_one_iff]
  decide

example : ¬ KervaireInvariantOneExists 254 := by
  rw [kervaire_invariant_one_iff]
  decide

example (n : ℕ) (hn : 126 < n) : ¬ KervaireInvariantOneExists n := by
  rw [kervaire_invariant_one_iff]
  omega
