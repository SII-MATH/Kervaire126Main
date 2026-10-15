module

public import KIP126.Def.Topology.Cube.Grid.Incidence.Data

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Among two different grid indices, the one of no larger total degree
has a strictly smaller coordinate. -/
theorem grid_index_lower_of_degree_le {n m : ℕ} (k l : Fin n → Fin (m+1))
    (hdegree : gridDegree l ≤ gridDegree k) (hne : l ≠ k) : ∃ i, l i < k i := by
  by_contra! h
  have hs : (∑ i, (k i).val) = ∑ i, (l i).val :=
    le_antisymm (Finset.sum_le_sum fun i _ => h i) hdegree
  have hle (i : Fin n) : (k i).val ≤ (l i).val := h i
  have he := (Finset.sum_eq_sum_iff_of_le fun i (_ : i ∈ Finset.univ) => hle i).mp hs
  apply hne
  funext i
  exact (Fin.ext (he i (Finset.mem_univ i))).symm

/-- Meeting a cell with a smaller coordinate forces a point onto the
corresponding lower face of its own affine cell coordinates. -/
theorem gridCell_overlap_coordinate {n m : ℕ} (k l : Fin n → Fin (m+1))
    (x : Fin n → I) (hx : (gridCellMap n m k x).val ∈ gridCell n m l)
    (i : Fin n) (hi : l i < k i) : x i = 0 := by
  apply (gridCoordinate_eq_lower_iff m (k i) (x i)).mp
  have hupper := (hx i).2
  have hcut : (l i).succ ≤ (k i).castSucc := by
    change (l i).val+1 ≤ (k i).val
    exact Nat.succ_le_of_lt hi
  exact le_antisymm (hupper.trans (gridVertex_monotone m hcut)) (gridCoordinate_mem m (k i) (x i)).1

/-- Distinct cells in the same or an earlier layer meet a new cell only
along its already incoming lower faces. -/
theorem gridCell_overlap_lower_face {n m : ℕ} (k l : Fin n → Fin (m+1))
    (x : Fin n → I) (hx : (gridCellMap n m k x).val ∈ gridCell n m l)
    (hdegree : gridDegree l ≤ gridDegree k) (hne : l ≠ k) :
    ∃ i, 0 < (k i).val ∧ x i = 0 := by
  obtain ⟨i,hi⟩ := grid_index_lower_of_degree_le k l hdegree hne
  exact ⟨i,lt_of_le_of_lt (Nat.zero_le _) hi,gridCell_overlap_coordinate k l x hx i hi⟩

/-- Every lower face not on the global lower boundary already belongs to
a strictly earlier cell. -/
theorem gridCell_lower_face_previous {n m : ℕ} (k : Fin n → Fin (m+1))
    (x : Fin n → I) (i : Fin n) (hi : 0 < (k i).val) (hx : x i = 0) :
    ∃ l : Fin n → Fin (m+1), gridDegree l < gridDegree k ∧
      (gridCellMap n m k x).val ∈ gridCell n m l := by
  let j : Fin (m+1) := ⟨(k i).val-1,lt_of_le_of_lt (Nat.sub_le _ _) (k i).is_lt⟩
  let l := Function.update k i j
  have hji : j.val+1 = (k i).val := by dsimp [j]; omega
  have hjlt : j < k i := by change (k i).val-1 < (k i).val; omega
  refine ⟨l,?_,?_⟩
  · apply Finset.sum_lt_sum
    · intro a _
      by_cases ha : a = i
      · subst a
        simpa [l] using hjlt.le
      · simp [l,ha]
    · exact ⟨i,Finset.mem_univ i,by simpa [l] using hjlt⟩
  · intro a
    by_cases ha : a = i
    · subst a
      change gridCoordinate m (k i) (x i) ∈ Set.Icc (gridVertex m (l i).castSucc) (gridVertex m (l i).succ)
      have he : j.succ = (k i).castSucc := Fin.ext hji
      simp only [l,Function.update_self,hx,gridCoordinate_zero]
      rw [← he]
      exact ⟨gridVertex_monotone m (by change j.val ≤ j.val+1; omega),le_rfl⟩
    · change gridCoordinate m (k a) (x a) ∈
        Set.Icc (gridVertex m (l a).castSucc) (gridVertex m (l a).succ)
      simpa only [l,Function.update_of_ne ha] using gridCoordinate_mem m (k a) (x a)

end KIP126.Topology.Cube
