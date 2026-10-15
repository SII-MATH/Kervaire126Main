module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Retraction.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem cubeFacesRetractionFunction_continuous {n : ℕ} (faces : Set (Fin n × Bool)) :
    Continuous (cubeFacesRetractionFunction faces) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact continuous_const.sub ((continuous_const.sub continuous_fst.subtype_val).div
      (cubeFacesScale_continuous faces) (fun z => (cubeFacesScale_pos faces z).ne'))
  · apply continuous_pi
    intro i
    apply continuous_projIcc.comp
    exact (((continuous_const.mul ((continuous_apply i).comp continuous_snd).subtype_val).sub
      continuous_const).div (cubeFacesScale_continuous faces)
        (fun z => (cubeFacesScale_pos faces z).ne') |>.add continuous_const).div_const 2


theorem cubeFacesRetractionFunction_restrict {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) (hz : z.1 = 0 ∨ z.2 ∈ cubeFacesBoundary n faces) :
    cubeFacesRetractionFunction faces z = z := by
  have hs := cubeFacesScale_eq_one_of_horn faces z hz
  apply Prod.ext
  · apply Subtype.ext
    change 2-(2-(z.1 : ℝ))/cubeFacesScale faces z = (z.1 : ℝ)
    rw [hs]
    ring
  · funext i
    change projIcc 0 1 zero_le_one (((2*(z.2 i : ℝ)-1)/cubeFacesScale faces z+1)/2) = z.2 i
    rw [hs]
    have he : ((2*(z.2 i : ℝ)-1)/1+1)/2 = (z.2 i : ℝ) := by ring
    rw [he,projIcc_of_mem zero_le_one (z.2 i).property]

theorem cubeFacesRetractionFunction_range {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) :
    (cubeFacesRetractionFunction faces z).1 = 0 ∨
      (cubeFacesRetractionFunction faces z).2 ∈ cubeFacesBoundary n faces := by
  classical
  obtain ⟨q,hq⟩ := (IsGreatest.pi_norm (cubeFacesGauge faces z)).1
  change ‖cubeFacesGauge faces z q‖ = ‖cubeFacesGauge faces z‖ at hq
  rw [Real.norm_eq_abs,abs_of_nonneg (cubeFacesGauge_nonneg faces z q)] at hq
  change cubeFacesGauge faces z q = cubeFacesScale faces z at hq
  have hp := cubeFacesScale_pos faces z
  cases q with
  | none =>
      left
      apply Subtype.ext
      change 2-(2-(z.1 : ℝ))/cubeFacesScale faces z = 0
      change (2-(z.1 : ℝ))/2 = cubeFacesScale faces z at hq
      field_simp
      nlinarith
  | some q =>
      obtain ⟨i,b⟩ := q
      right
      have hf : (i,b) ∈ faces := by
        by_contra hf
        simp [cubeFacesGauge,hf] at hq
        linarith
      refine ⟨i,b,hf,?_⟩
      dsimp only [cubeFacesGauge] at hq
      rw [if_pos hf] at hq
      have he : (if b then 2*(z.2 i : ℝ)-1 else 1-2*(z.2 i : ℝ)) =
          cubeFacesScale faces z := by
        have hh : 0 ≤ (if b then 2*(z.2 i : ℝ)-1 else 1-2*(z.2 i : ℝ)) := by
          by_contra hh
          rw [max_eq_left (le_of_not_ge hh)] at hq
          linarith
        rwa [max_eq_right hh] at hq
      change projIcc 0 1 zero_le_one
        (((2*(z.2 i : ℝ)-1)/cubeFacesScale faces z+1)/2) = if b then 1 else 0
      cases b with
      | false =>
          apply _root_.projIcc_eq_zero.mpr
          change 1-2*(z.2 i : ℝ) = cubeFacesScale faces z at he
          have he' : 2*(z.2 i : ℝ)-1 = -cubeFacesScale faces z := by linarith
          rw [he',neg_div,div_self hp.ne']
          norm_num
      | true =>
          apply _root_.projIcc_eq_one.mpr
          change 2*(z.2 i : ℝ)-1 = cubeFacesScale faces z at he
          rw [he,div_self hp.ne']
          norm_num


end KIP126.Topology.HomotopyLifting
