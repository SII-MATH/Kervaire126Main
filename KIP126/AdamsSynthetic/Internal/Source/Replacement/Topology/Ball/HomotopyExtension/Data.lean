module

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

@[expose] section

namespace KIP126.Topology.Ball

open Metric
open scoped unitInterval

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial denominator for projecting a closed-ball cylinder away from
height two onto its bottom and boundary cylinder. -/
noncomputable def cylinderScale (z : closedBall (0 : E) 1 × I) : ℝ :=
  max ((2 - (z.2 : ℝ)) / 2) ‖z.1.1‖

/-- The explicit retraction of a closed-ball cylinder onto its bottom
and its boundary cylinder. The target remains bundled as the cylinder. -/
noncomputable def cylinderRetraction
    (z : closedBall (0 : E) 1 × I) : closedBall (0 : E) 1 × I := by
  have hx : ‖z.1.1‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using z.1.2
  have hpos : 0 < cylinderScale z :=
    lt_of_lt_of_le (by linarith [z.2.2.2] : 0 < (2 - (z.2 : ℝ)) / 2) (le_max_left _ _)
  have hlo : (2 - (z.2 : ℝ)) / 2 ≤ cylinderScale z := le_max_left _ _
  have hhi : cylinderScale z ≤ 1 := max_le (by linarith [z.2.2.1]) hx
  refine (⟨(cylinderScale z)⁻¹ • z.1.1, ?_⟩, ⟨2 - (2 - (z.2 : ℝ)) / cylinderScale z, ?_⟩)
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos)]
    have hn : ‖z.1.1‖ ≤ cylinderScale z := le_max_right _ _
    exact (inv_mul_le_iff₀ hpos).mpr (by simpa using hn)
  · constructor
    · have hr : (2 - (z.2 : ℝ)) / cylinderScale z ≤ 2 :=
        (div_le_iff₀ hpos).mpr (by linarith)
      linarith
    · have hr : 1 ≤ (2 - (z.2 : ℝ)) / cylinderScale z :=
        (le_div_iff₀ hpos).mpr (by linarith [z.2.2.2])
      linarith

end KIP126.Topology.Ball
