module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Data
import Mathlib.Analysis.Normed.Module.Basic

@[expose] section

section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The affine cube identification with the unit ball for the maximum norm. -/
noncomputable def cubeClosedBallHomeomorph (n : ℕ) :
    (Fin n → I) ≃ₜ closedBall (0 : Fin n → ℝ) 1 where
  toFun z := ⟨fun i => 2*(z i : ℝ)-1, by
    rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [(z i).property.1,(z i).property.2]⟩
  invFun z i := ⟨(z.val i+1)/2, by
    have hz : ‖z.val‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using z.property
    have hi := (pi_norm_le_iff_of_nonneg zero_le_one).mp hz i
    rw [Real.norm_eq_abs,abs_le] at hi
    constructor <;> linarith⟩
  left_inv z := by
    ext i
    change (2*(z i : ℝ)-1+1)/2 = (z i : ℝ)
    ring
  right_inv z := by
    apply Subtype.ext
    funext i
    change 2*((z.val i+1)/2)-1 = z.val i
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_const.mul (continuous_apply i).subtype_val).sub continuous_const
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact ((continuous_apply i).comp continuous_subtype_val |>.add continuous_const).div_const 2


end KIP126.Topology.HomotopyLifting

end

section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem cubeClosedBallHomeomorph_boundary (n : ℕ) (z : Fin n → I) :
    z ∈ _root_.Cube.boundary (Fin n) ↔ ‖(cubeClosedBallHomeomorph n z).val‖ = 1 := by
  have hn : ‖(cubeClosedBallHomeomorph n z).val‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using (cubeClosedBallHomeomorph n z).property
  constructor
  · rintro ⟨i,hi⟩
    apply le_antisymm hn
    have he : ‖(cubeClosedBallHomeomorph n z).val i‖ = 1 := by
      rcases hi with hi | hi <;> norm_num [cubeClosedBallHomeomorph,hi]
    exact he.symm.trans_le (norm_le_pi_norm _ i)
  · intro h
    by_contra hc
    have hlt : ‖(cubeClosedBallHomeomorph n z).val‖ < 1 := by
      rw [pi_norm_lt_iff zero_lt_one]
      intro i
      have hi : z i ≠ 0 ∧ z i ≠ 1 := by
        constructor
        · intro hi; exact hc ⟨i,Or.inl hi⟩
        · intro hi; exact hc ⟨i,Or.inr hi⟩
      have hlo : 0 < (z i : ℝ) := by
        have : (z i : ℝ) ≠ 0 := fun h => hi.1 (Subtype.ext h)
        exact lt_of_le_of_ne (z i).property.1 (Ne.symm this)
      have hhi : (z i : ℝ) < 1 := by
        have : (z i : ℝ) ≠ 1 := fun h => hi.2 (Subtype.ext h)
        exact lt_of_le_of_ne (z i).property.2 this
      change ‖2*(z i : ℝ)-1‖ < 1
      rw [Real.norm_eq_abs,abs_lt]
      constructor <;> linarith
    linarith


end KIP126.Topology.HomotopyLifting

end
