module

public import KIP126.Def.Topology.Simplex.BarycentricDecomposition.Uniqueness.Data
public import KIP126.Def.Topology.Simplex.BarycentricDecomposition.Proofs
public import Mathlib.Order.Hom.Set

@[expose] public section

namespace KIP126.Topology.Simplex.BarycentricDecomposition

open scoped Classical

variable {V : Type*} {m : ℕ}

@[simp] theorem tailMass_card (a : Fin m → ℝ) : tailMass a m = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  exact if_neg (by omega)

/-- Consecutive tail masses recover exactly one per-vertex mass. -/
theorem tailMass_sub_succ (a : Fin m → ℝ) (i : Fin m) :
    tailMass a i.val - tailMass a (i.val + 1) = a i := by
  unfold tailMass
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ k : Fin m, ((if i.val ≤ k.val then a k else 0) -
      (if i.val + 1 ≤ k.val then a k else 0))) = ∑ k, if k = i then a i else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i
      · subst k
        simp
      · have hne : k.val ≠ i.val := fun h => hk (Fin.ext h)
        by_cases hle : i.val ≤ k.val
        · rw [if_pos hle, if_pos (by omega : i.val + 1 ≤ k.val), if_neg hk, sub_self]
        · rw [if_neg hle, if_neg (by omega : ¬ i.val + 1 ≤ k.val), if_neg hk, sub_self]
    _ = a i := by simp

theorem tailMass_pos (a : Fin m → ℝ) (ha : ∀ k, 0 < a k) (i : Fin m) :
    0 < tailMass a i.val := by
  apply lt_of_lt_of_le (ha i)
  have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
    show 0 ≤ if i.val ≤ k.val then a k else 0 from by
      split_ifs
      · exact (ha k).le
      · exact le_rfl)
    (Finset.mem_univ i)
  simpa only [le_refl, if_true, tailMass] using h

theorem tailMass_strictAnti (a : Fin m → ℝ) (ha : ∀ k, 0 < a k) :
    StrictAnti (fun i : Fin m => tailMass a i.val) := by
  intro i j hij
  apply Finset.sum_lt_sum
  · intro k _
    by_cases hjk : j.val ≤ k.val
    · rw [if_pos hjk, if_pos (by exact le_trans (Fin.le_iff_val_le_val.mp hij.le) hjk)]
    · rw [if_neg hjk]
      split_ifs
      · exact (ha k).le
      · exact le_rfl
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [if_neg (by exact not_le_of_gt hij), if_pos (le_refl _)]
    exact ha i

/-- Each face in a strictly increasing nonempty flag contains a vertex
which first appears exactly at that face. -/
theorem strict_flag_new_vertex (c : Fin m → Finset V)
    (hc : StrictMono c) (hne : ∀ i, (c i).Nonempty) (i : Fin m) :
    ∃ j, ∀ k, j ∈ c k ↔ i ≤ k := by
  by_cases hi : i.val = 0
  · obtain ⟨j, hj⟩ := hne i
    refine ⟨j, fun k => ?_⟩
    have hik : i ≤ k := by change i.val ≤ k.val; omega
    exact iff_of_true (hc.monotone hik hj) hik
  · let p : Fin m := ⟨i.val - 1, by omega⟩
    have hpi : p < i := by change i.val - 1 < i.val; omega
    obtain ⟨j, hji, hjp⟩ := Finset.exists_of_ssubset (hc hpi)
    refine ⟨j, fun k => ⟨fun hj => ?_, fun hik => hc.monotone hik hji⟩⟩
    by_contra hki
    have hkp : k ≤ p := by change k.val ≤ i.val - 1; exact Nat.le_sub_one_of_lt (not_le.mp hki)
    exact hjp (hc.monotone hkp hj)

/-- A vertex with positive flag mass has a unique first face; all its
containing faces are the resulting terminal interval. -/
theorem positive_flagSum_first (c : Fin m → Finset V) (hc : Monotone c)
    (a : Fin m → ℝ) (j : V) (hj : 0 < flagSum c a j) :
    ∃ i, ∀ k, j ∈ c k ↔ i ≤ k := by
  have hex : ∃ k, j ∈ c k := by
    by_contra h
    push Not at h
    have hz : flagSum c a j = 0 := by simp [flagSum, h]
    linarith
  let s : Finset (Fin m) := Finset.univ.filter (fun k => j ∈ c k)
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  let i := s.min' hs
  have hi : j ∈ c i := (Finset.mem_filter.mp (s.min'_mem hs)).2
  refine ⟨i, fun k => ⟨fun hk => ?_, fun hik => hc hik hi⟩⟩
  exact s.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)

theorem flagSum_eq_tailMass (c : Fin m → Finset V) (a : Fin m → ℝ)
    (i : Fin m) (j : V) (hj : ∀ k, j ∈ c k ↔ i ≤ k) :
    flagSum c a j = tailMass a i.val := by
  unfold flagSum tailMass
  apply Finset.sum_congr rfl
  intro k _
  simp only [hj, Fin.le_iff_val_le_val]

/-- Each strict flag face is the upper level set of its associated tail mass. -/
theorem mem_flag_iff_tailMass_le (c : Fin m → Finset V) (hc : Monotone c)
    (a : Fin m → ℝ) (ha : ∀ k, 0 < a k) (i : Fin m) (j : V) :
    j ∈ c i ↔ tailMass a i.val ≤ flagSum c a j := by
  constructor
  · intro hji
    apply Finset.sum_le_sum
    intro k _
    by_cases hik : i.val ≤ k.val
    · rw [if_pos hik, if_pos (hc hik hji)]
    · rw [if_neg hik]
      split_ifs
      · exact (ha k).le
      · exact le_rfl
  · intro hle
    by_contra hji
    have hlt : flagSum c a j < tailMass a i.val := by
      apply Finset.sum_lt_sum
      · intro k _
        by_cases hjk : j ∈ c k
        · have hik : i.val ≤ k.val := by
            by_contra h
            exact hji (hc (le_of_lt (not_le.mp h)) hjk)
          rw [if_pos hjk, if_pos hik]
        · rw [if_neg hjk]
          split_ifs
          · exact (ha k).le
          · exact le_rfl
      · refine ⟨i, Finset.mem_univ _, ?_⟩
        rw [if_neg hji, if_pos (le_refl _)]
        exact ha i
    exact (not_lt_of_ge hle) hlt

end KIP126.Topology.Simplex.BarycentricDecomposition
