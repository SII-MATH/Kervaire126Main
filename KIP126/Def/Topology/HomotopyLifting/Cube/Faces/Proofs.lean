module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem cubeFacesGauge_nonneg {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) (q : Option (Fin n × Bool)) : 0 ≤ cubeFacesGauge faces z q := by
  classical
  cases q with
  | none => dsimp [cubeFacesGauge]; linarith [z.1.property.2]
  | some q =>
      dsimp [cubeFacesGauge]
      split_ifs <;> positivity

theorem cubeFacesGauge_le_one {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) (q : Option (Fin n × Bool)) : cubeFacesGauge faces z q ≤ 1 := by
  classical
  cases q with
  | none => dsimp [cubeFacesGauge]; linarith [z.1.property.1]
  | some q =>
      obtain ⟨i,b⟩ := q
      by_cases hf : (i,b) ∈ faces
      · simp only [cubeFacesGauge,if_pos hf]
        apply max_le zero_le_one
        cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
          linarith [(z.2 i).property.1,(z.2 i).property.2]
      · simp only [cubeFacesGauge,if_neg hf]
        exact zero_le_one

theorem cubeFacesGauge_le_scale {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) (q : Option (Fin n × Bool)) :
    cubeFacesGauge faces z q ≤ cubeFacesScale faces z := by
  have h := norm_le_pi_norm (cubeFacesGauge faces z) q
  rw [Real.norm_eq_abs,abs_of_nonneg (cubeFacesGauge_nonneg faces z q)] at h
  exact h

theorem cubeFacesScale_pos {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) : 0 < cubeFacesScale faces z := by
  have h := cubeFacesGauge_le_scale faces z none
  change (2-(z.1 : ℝ))/2 ≤ cubeFacesScale faces z at h
  linarith [z.1.property.2]

theorem cubeFacesScale_le_one {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) : cubeFacesScale faces z ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro q
  rw [Real.norm_eq_abs,abs_of_nonneg (cubeFacesGauge_nonneg faces z q)]
  exact cubeFacesGauge_le_one faces z q

theorem cubeFacesScale_continuous {n : ℕ} (faces : Set (Fin n × Bool)) :
    Continuous (cubeFacesScale faces) := by
  classical
  apply Continuous.norm
  apply continuous_pi
  intro q
  cases q with
  | none => dsimp [cubeFacesGauge]; fun_prop
  | some q =>
      dsimp [cubeFacesGauge]
      split_ifs <;> fun_prop

theorem cubeFacesScale_eq_one_of_horn {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) (hz : z.1 = 0 ∨ z.2 ∈ cubeFacesBoundary n faces) :
    cubeFacesScale faces z = 1 := by
  classical
  apply le_antisymm (cubeFacesScale_le_one faces z)
  rcases hz with ht | ⟨i,b,hface,hb⟩
  · have h := cubeFacesGauge_le_scale faces z none
    simpa [cubeFacesGauge,ht] using h
  · have h := cubeFacesGauge_le_scale faces z (some (i,b))
    cases b <;> norm_num [cubeFacesGauge,hface,hb] at h ⊢ <;> exact h

end KIP126.Topology.HomotopyLifting
