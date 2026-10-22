module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricDecomposition.Data
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] section

namespace KIP126.Topology.Simplex.BarycentricDecomposition

open scoped Classical

variable {V : Type*} [Fintype V]

@[simp] theorem mem_levels (y : stdSimplex ℝ V) (a : ℝ) :
    a ∈ levels y ↔ 0 < a ∧ ∃ j, y j = a := by
  classical
  simp [levels, and_comm]

theorem levels_nonempty (y : stdSimplex ℝ V) : (levels y).Nonempty := by
  classical
  by_contra h
  have hz (j : V) : y j = 0 := by
    have hn := y.property.1 j
    by_contra hj
    have hp : 0 < y j := lt_of_le_of_ne hn (Ne.symm hj)
    exact h ⟨y j, (mem_levels y _).mpr ⟨hp, j, rfl⟩⟩
  have hs : ∑ j, y j = 1 := stdSimplex.sum_eq_one y
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

theorem level_mem (y : stdSimplex ℝ V) (i : Fin (levels y).card) :
    level y i ∈ levels y := Finset.orderEmbOfFin_mem _ _ _

theorem level_pos (y : stdSimplex ℝ V) (i : Fin (levels y).card) :
    0 < level y i := ((mem_levels y _).mp (level_mem y i)).1

theorem level_exists_vertex (y : stdSimplex ℝ V) (i : Fin (levels y).card) :
    ∃ j, y j = level y i := ((mem_levels y _).mp (level_mem y i)).2

theorem level_strictAnti (y : stdSimplex ℝ V) : StrictAnti (level y) := by
  intro i k hik
  exact ((levels y).orderEmbOfFin rfl).strictMono (Fin.rev_lt_rev.mpr hik)

theorem exists_level_eq (y : stdSimplex ℝ V) (j : V) (hj : 0 < y j) :
    ∃ i, level y i = y j := by
  let a : levels y := ⟨y j, (mem_levels y _).mpr ⟨hj, j, rfl⟩⟩
  refine ⟨((levels y).orderIsoOfFin rfl).symm a |>.rev, ?_⟩
  simp only [level, Fin.rev_rev]
  exact congrArg Subtype.val (((levels y).orderIsoOfFin rfl).apply_symm_apply a)

@[simp] theorem levelAt_fin (y : stdSimplex ℝ V) (i : Fin (levels y).card) :
    levelAt y i.val = level y i := dif_pos i.isLt

@[simp] theorem levelAt_card (y : stdSimplex ℝ V) :
    levelAt y (levels y).card = 0 := dif_neg (lt_irrefl _)

@[simp] theorem mem_face (y : stdSimplex ℝ V) (i : Fin (levels y).card) (j : V) :
    j ∈ face y i ↔ level y i ≤ y j := by
  classical
  simp [face]

theorem face_nonempty (y : stdSimplex ℝ V) (i : Fin (levels y).card) :
    (face y i).Nonempty := by
  obtain ⟨j, hj⟩ := level_exists_vertex y i
  exact ⟨j, (mem_face y i j).mpr (le_of_eq hj.symm)⟩

theorem face_strictMono (y : stdSimplex ℝ V) : StrictMono (face y) := by
  intro i k hik
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact (mem_face y k j).mpr ((level_strictAnti y hik).le.trans ((mem_face y i j).mp hj))
  · intro heq
    obtain ⟨j, hj⟩ := level_exists_vertex y k
    have hmem : j ∈ face y i := heq.symm ▸ (mem_face y k j).mpr (le_of_eq hj.symm)
    have hle := (mem_face y i j).mp hmem
    rw [hj] at hle
    exact (not_le_of_gt (level_strictAnti y hik)) hle

theorem gap_pos (y : stdSimplex ℝ V) (i : Fin (levels y).card) :
    0 < levelAt y i.val - levelAt y (i.val + 1) := by
  rw [levelAt_fin]
  by_cases hi : i.val + 1 < (levels y).card
  · rw [levelAt, dif_pos hi]
    exact sub_pos.mpr (level_strictAnti y (show i < ⟨i.val + 1, hi⟩ from by change i.val < i.val + 1; omega))
  · rw [levelAt, dif_neg hi, sub_zero]
    exact level_pos y i

theorem weight_pos (y : stdSimplex ℝ V) (i : Fin (levels y).card) : 0 < weight y i :=
  mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr (face_nonempty y i))) (gap_pos y i)


/-- The tail of a finite successive-difference sum telescopes. -/
theorem sum_tail_differences (a : ℕ → ℝ) (n r : ℕ) :
    (∑ i ∈ Finset.range n, if r ≤ i then a i - a (i + 1) else 0) =
      if r < n then a r - a n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hr : r < n
    · rw [if_pos hr, if_pos (by omega : r ≤ n), if_pos (by omega : r < n + 1)]
      ring
    · by_cases he : r = n
      · subst r
        simp
      · rw [if_neg hr, if_neg (by omega : ¬ r ≤ n), if_neg (by omega : ¬ r < n + 1)]
        simp

/-- The upper-level faces containing a coordinate form exactly the
corresponding terminal interval of the sorted level indices. -/
theorem mem_face_iff_index (y : stdSimplex ℝ V) (j : V)
    (r i : Fin (levels y).card) (hr : level y r = y j) :
    j ∈ face y i ↔ r ≤ i := by
  rw [mem_face, ← hr]
  exact (level_strictAnti y).le_iff_ge

/-- On its face a weighted uniform barycenter contributes precisely the
successive coordinate gap. -/
theorem weight_barycenter (y : stdSimplex ℝ V) (i : Fin (levels y).card) (j : V) :
    weight y i * (if j ∈ face y i then ((face y i).card : ℝ)⁻¹ else 0) =
      if j ∈ face y i then levelAt y i.val - levelAt y (i.val + 1) else 0 := by
  classical
  by_cases hj : j ∈ face y i
  · rw [if_pos hj, if_pos hj, weight]
    have hc : ((face y i).card : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (face_nonempty y i)))
    field_simp
  · simp only [if_neg hj, mul_zero]

/-- The positive upper-level flag reconstructs the original simplex point exactly. -/
theorem reconstruction (y : stdSimplex ℝ V) (j : V) :
    y j = ∑ i, weight y i * (if j ∈ face y i then ((face y i).card : ℝ)⁻¹ else 0) := by
  classical
  simp only [weight_barycenter]
  by_cases hj : 0 < y j
  · obtain ⟨r, hr⟩ := exists_level_eq y j hj
    simp only [mem_face_iff_index y j r _ hr]
    change y j = ∑ i : Fin (levels y).card,
      if r.val ≤ i.val then levelAt y i.val - levelAt y (i.val + 1) else 0
    rw [Fin.sum_univ_eq_sum_range (fun i => if r.val ≤ i then
        levelAt y i - levelAt y (i + 1) else 0), sum_tail_differences, if_pos r.isLt, levelAt_card,
      sub_zero, levelAt_fin, hr]
  · have hz : y j = 0 := le_antisymm (le_of_not_gt hj) (y.property.1 j)
    rw [hz]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    have hi := (mem_face y i j).mp h
    rw [hz] at hi
    exact (not_le_of_gt (level_pos y i)) hi

/-- Every nonempty uniform face barycenter has total coordinate mass one. -/
theorem sum_face_barycenter (s : Finset V) (hs : s.Nonempty) :
    (∑ j : V, if j ∈ s then (s.card : ℝ)⁻¹ else 0) = 1 := by
  classical
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ (ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)))

/-- The strictly positive coefficients of the canonical flag sum to one. -/
theorem weight_sum (y : stdSimplex ℝ V) : ∑ i, weight y i = 1 := by
  classical
  calc
    ∑ i, weight y i = ∑ i, weight y i *
        ∑ j : V, (if j ∈ face y i then ((face y i).card : ℝ)⁻¹ else 0) := by
      simp only [sum_face_barycenter _ (face_nonempty y _), mul_one]
    _ = ∑ j : V, ∑ i, weight y i *
        (if j ∈ face y i then ((face y i).card : ℝ)⁻¹ else 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ j : V, y j := by simp only [← reconstruction]
    _ = 1 := stdSimplex.sum_eq_one y

/-- Every standard simplex point has an actual strict nonempty face flag
and strictly positive barycentric weights on that flag. -/
theorem exists_strict_flag (y : stdSimplex ℝ V) :
    ∃ (m : ℕ) (_ : 0 < m) (c : Fin m → Finset V) (t : stdSimplex ℝ (Fin m)),
      (∀ i, (c i).Nonempty) ∧ StrictMono c ∧ (∀ i, 0 < t i) ∧
        ∀ j, y j = ∑ i, t i * (if j ∈ c i then ((c i).card : ℝ)⁻¹ else 0) := by
  refine ⟨(levels y).card, Finset.card_pos.mpr (levels_nonempty y), face y,
    ⟨weight y, fun i => (weight_pos y i).le, weight_sum y⟩,
    face_nonempty y, face_strictMono y, weight_pos y, reconstruction y⟩

end KIP126.Topology.Simplex.BarycentricDecomposition
