module

public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

namespace KIP126.Topology.Simplex

open Set
open scoped BigOperators

/-- The full-dimensional coordinate simplex obtained by omitting the
zeroth barycentric coordinate. -/
def coordinateSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The standard geometric simplex with one barycentric coordinate
eliminated; the omitted coordinate is recovered as one minus the sum. -/
def coordinateHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ coordinateSimplex n where
  toFun x := ⟨fun i => x.1 i.succ, fun i => x.2.1 _, by
    have hs := x.2.2
    rw [Fin.sum_univ_succ] at hs
    have h0 := x.2.1 0
    linarith⟩
  invFun x := ⟨Fin.cases (1 - ∑ i, x.1 i) x.1, by
    constructor
    · intro i
      induction i using Fin.cases with
      | zero => exact sub_nonneg.mpr x.2.2
      | succ i => exact x.2.1 i
    · rw [Fin.sum_univ_succ]
      simp⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    induction i using Fin.cases with
    | zero =>
      have hs := x.2.2
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cases_zero]
      linarith
    | succ i => rfl
  right_inv x := rfl
  continuous_toFun :=
    (continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    induction i using Fin.cases with
    | zero => exact continuous_const.sub (continuous_finsetSum _ fun i _ =>
        (continuous_apply i).comp continuous_subtype_val)
    | succ i => exact (continuous_apply i).comp continuous_subtype_val

end KIP126.Topology.Simplex
