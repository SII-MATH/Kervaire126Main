module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Ball.HomotopyExtension.Data
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FunProp

@[expose] section

namespace KIP126.Topology.Ball

open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial denominator stays positive throughout the actual cylinder. -/
theorem cylinderScale_pos (z : closedBall (0 : E) 1 × I) : 0 < cylinderScale z :=
  lt_of_lt_of_le (by linarith [z.2.2.2] : 0 < (2 - (z.2 : ℝ)) / 2) (le_max_left _ _)

theorem cylinderScale_continuous : Continuous (cylinderScale (E := E)) := by
  unfold cylinderScale
  fun_prop

/-- No discontinuity occurs at the seam where the projection reaches the
bottom and side simultaneously. -/
theorem cylinderRetraction_continuous : Continuous (cylinderRetraction (E := E)) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (cylinderScale_continuous.inv₀ (fun z => (cylinderScale_pos z).ne')).smul
      continuous_fst.subtype_val
  · apply Continuous.subtype_mk
    exact continuous_const.sub ((continuous_const.sub continuous_snd.subtype_val).div
      cylinderScale_continuous (fun z => (cylinderScale_pos z).ne'))

/-- The entire bottom of the cylinder is fixed pointwise. -/
theorem cylinderRetraction_bottom (x : closedBall (0 : E) 1) :
    cylinderRetraction (x, 0) = (x, 0) := by
  have hx : ‖x.1‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using x.2
  have hm : cylinderScale (x, 0) = 1 := by simp [cylinderScale, max_eq_left hx]
  apply Prod.ext
  · apply Subtype.ext
    simp [cylinderRetraction, hm]
  · apply Subtype.ext
    simp [cylinderRetraction, hm]

/-- The entire boundary cylinder is also fixed pointwise. -/
theorem cylinderRetraction_side (x : closedBall (0 : E) 1)
    (hx : ‖x.1‖ = 1) (t : I) : cylinderRetraction (x, t) = (x, t) := by
  have hm : cylinderScale (x, t) = 1 := by
    change max ((2 - (t : ℝ)) / 2) ‖x.1‖ = 1
    rw [hx]
    apply max_eq_right
    linarith [t.2.1]
  apply Prod.ext
  · apply Subtype.ext
    simp [cylinderRetraction, hm]
  · apply Subtype.ext
    simp [cylinderRetraction, hm]

/-- The image lies exactly in the required bottom-or-side union. -/
theorem cylinderRetraction_range (z : closedBall (0 : E) 1 × I) :
    (cylinderRetraction z).2 = 0 ∨ ‖(cylinderRetraction z).1.1‖ = 1 := by
  by_cases h : ‖z.1.1‖ ≤ (2 - (z.2 : ℝ)) / 2
  · left
    apply Subtype.ext
    change 2 - (2 - (z.2 : ℝ)) / cylinderScale z = 0
    rw [cylinderScale, max_eq_left h]
    have ht : 2 - (z.2 : ℝ) ≠ 0 := by linarith [z.2.2.2]
    field_simp
    ring
  · right
    have hm : cylinderScale z = ‖z.1.1‖ := max_eq_right (le_of_not_ge h)
    change ‖(cylinderScale z)⁻¹ • z.1.1‖ = 1
    have hp : 0 < ‖z.1.1‖ := hm ▸ cylinderScale_pos z
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

/-- The boundary sphere inclusion into a closed ball has the full actual
homotopy extension property, witnessed using the displayed cylinder retraction. -/
theorem boundary_homotopy_extension {Y : Type v} [TopologicalSpace Y]
    (f : C(closedBall (0 : E) 1, Y)) (p : C(sphere (0 : E) 1 × I, Y))
    (hp : ∀ x : sphere (0 : E) 1,
      p (x, 0) = f ⟨x.1, Metric.sphere_subset_closedBall x.2⟩) :
    ∃ H : C(closedBall (0 : E) 1 × I, Y),
      (∀ x, H (x, 0) = f x) ∧
      (∀ (x : sphere (0 : E) 1) t,
        H (⟨x.1, Metric.sphere_subset_closedBall x.2⟩, t) = p (x, t)) := by
  classical
  let r : C(closedBall (0 : E) 1 × I, closedBall (0 : E) 1 × I) :=
    ⟨cylinderRetraction, cylinderRetraction_continuous⟩
  let U : Set (closedBall (0 : E) 1 × I) := {z | (r z).2 = 0}
  let V : Set (closedBall (0 : E) 1 × I) := {z | ‖(r z).1.1‖ = 1}
  have hU : IsClosed U := isClosed_eq r.continuous.snd continuous_const
  have hV : IsClosed V := isClosed_eq r.continuous.fst.subtype_val.norm continuous_const
  have hUV : U ∪ V = univ := Set.eq_univ_of_forall cylinderRetraction_range
  let F : closedBall (0 : E) 1 × I → Y := fun z =>
    if hz : ‖(r z).1.1‖ = 1 then
      p (⟨(r z).1.1, by simpa only [mem_sphere, dist_zero_right] using hz⟩, (r z).2)
    else f (r z).1
  have hu : ContinuousOn F U := (f.continuous.comp r.continuous.fst).continuousOn.congr (by
    intro z hz
    dsimp [F]
    split_ifs with hv
    · rw [show (r z).2 = 0 from hz]
      exact hp _
    · rfl)
  have hv : ContinuousOn F V := by
    apply continuousOn_iff_continuous_restrict.mpr
    let a : V → sphere (0 : E) 1 × I := fun z =>
      (⟨(r z.1).1.1, by simpa only [mem_sphere, dist_zero_right] using (show ‖(r z.1).1.1‖ = 1 from z.2)⟩, (r z.1).2)
    have ha : Continuous a :=
      ((r.continuous.comp continuous_subtype_val).fst.subtype_val.subtype_mk _).prodMk
        (r.continuous.comp continuous_subtype_val).snd
    apply (p.continuous.comp ha).congr
    intro z
    change p _ = F z.1
    dsimp only [F]
    rw [dif_pos (show ‖(r z.1).1.1‖ = 1 from z.2)]
  have hF : Continuous F := continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
  refine ⟨⟨F, hF⟩, ?_, ?_⟩
  · intro x
    have hb : r (x, 0) = (x, 0) := cylinderRetraction_bottom x
    change F (x, 0) = f x
    dsimp only [F]
    simp only [hb]
    split_ifs with hx
    · exact hp _
    · rfl
  · intro x t
    have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using x.2
    let xb : closedBall (0 : E) 1 := ⟨x.1, Metric.sphere_subset_closedBall x.2⟩
    have hb : r (xb, t) = (xb, t) := cylinderRetraction_side xb hx t
    change F (xb, t) = p (x, t)
    dsimp only [F]
    have hxb : ‖xb.1‖ = 1 := hx
    simp only [hb, dif_pos hxb]
    rfl

end KIP126.Topology.Ball
