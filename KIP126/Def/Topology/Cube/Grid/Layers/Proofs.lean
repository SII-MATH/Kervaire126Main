module

public import KIP126.Def.Topology.Cube.Grid.Layers.Data
public import KIP126.Def.Topology.Cube.Grid.Incidence.Proofs

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem gridGlobalHorn_isClosed (n : ℕ) : IsClosed (gridGlobalHorn n) := by
  have h (i : Fin n) : IsClosed {x : Fin (n+1) → I | x i.succ = 0 ∨ x i.succ = 1} :=
    (isClosed_eq (continuous_apply _) continuous_const).union
      (isClosed_eq (continuous_apply _) continuous_const)
  simpa only [gridGlobalHorn,Set.setOf_or,Set.setOf_exists] using
    (isClosed_eq (continuous_apply (0 : Fin (n+1))) continuous_const).union
      (isClosed_iUnion_of_finite h)

theorem gridPast_isClosed (n m r : ℕ) : IsClosed (gridPast n m r) := by
  classical
  have h (k : Fin (n+1) → Fin (m+1)) :
      IsClosed {x | gridDegree k < r ∧ x ∈ gridCell (n+1) m k} := by
    by_cases hk : gridDegree k < r
    · simpa [hk] using gridCell_isClosed (n+1) m k
    · simp [hk]
  simpa only [gridPast,Set.setOf_exists] using
    (gridGlobalHorn_isClosed n).union (isClosed_iUnion_of_finite h)

theorem gridPast_zero (n m : ℕ) : gridPast n m 0 = gridGlobalHorn n := by
  ext x
  simp [gridPast]

theorem gridPast_mono (n m : ℕ) {r s : ℕ} (hrs : r ≤ s) :
    gridPast n m r ⊆ gridPast n m s := by
  rintro x (hx | ⟨k,hk,hx⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨k,lt_of_lt_of_le hk hrs,hx⟩

theorem gridPast_succ (n m r : ℕ) :
    gridPast n m (r+1) = gridPast n m r ∪
      {x | ∃ k : Fin (n+1) → Fin (m+1), gridDegree k = r ∧ x ∈ gridCell (n+1) m k} := by
  ext x
  constructor
  · rintro (hx | ⟨k,hk,hx⟩)
    · exact Or.inl (Or.inl hx)
    · by_cases he : gridDegree k = r
      · exact Or.inr ⟨k,he,hx⟩
      · exact Or.inl (Or.inr ⟨k,by omega,hx⟩)
  · rintro ((hx | ⟨k,hk,hx⟩) | ⟨k,hk,hx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨k,by omega,hx⟩
    · exact Or.inr ⟨k,by omega,hx⟩

theorem gridDegree_le {n m : ℕ} (k : Fin n → Fin (m+1)) : gridDegree k ≤ n*m := by
  calc
    gridDegree k ≤ ∑ _i : Fin n, m :=
      Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (k i).is_lt)
    _ = n*m := by simp

theorem gridPast_eq_univ (n m : ℕ) : gridPast n m ((n+1)*m+1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨k,hk⟩ := exists_gridCell (n+1) m x
  exact Or.inr ⟨k,Nat.lt_succ_of_le (gridDegree_le k),hk⟩

theorem gridIncoming_of_lower_face {n m : ℕ} (k : Fin (n+1) → Fin (m+1))
    (x : Fin (n+1) → I) (i : Fin (n+1)) (hx : x i = 0) : x ∈ gridIncoming k := by
  induction i using Fin.cases with
  | zero => exact Or.inl hx
  | succ i => exact Or.inr ⟨i,Or.inl hx⟩

theorem gridCell_globalHorn_incoming {n m : ℕ} (k : Fin (n+1) → Fin (m+1))
    (x : Fin (n+1) → I) (hx : (gridCellMap (n+1) m k x).val ∈ gridGlobalHorn n) :
    x ∈ gridIncoming k := by
  rcases hx with ht | ⟨i,hi | hi⟩
  · exact Or.inl ((gridCoordinate_eq_zero_iff m (k 0) (x 0)).mp ht).2
  · exact Or.inr ⟨i,Or.inl ((gridCoordinate_eq_zero_iff m (k i.succ) (x i.succ)).mp hi).2⟩
  · exact Or.inr ⟨i,Or.inr ((gridCoordinate_eq_one_iff m (k i.succ) (x i.succ)).mp hi)⟩

theorem gridCell_lower_face_mem_past {n m : ℕ} (k : Fin (n+1) → Fin (m+1))
    (x : Fin (n+1) → I) (i : Fin (n+1)) (hx : x i = 0) :
    (gridCellMap (n+1) m k x).val ∈ gridPast n m (gridDegree k) := by
  by_cases hk : (k i).val = 0
  · have hzero : (gridCellMap (n+1) m k x).val i = 0 :=
      (gridCoordinate_eq_zero_iff m (k i) (x i)).mpr ⟨hk,hx⟩
    apply Or.inl
    induction i using Fin.cases with
    | zero => exact Or.inl hzero
    | succ i => exact Or.inr ⟨i,Or.inl hzero⟩
  · obtain ⟨l,hl,hy⟩ := gridCell_lower_face_previous k x i (Nat.pos_of_ne_zero hk) hx
    exact Or.inr ⟨l,hl,hy⟩

/-- Precisely the incoming local faces are already prescribed when a
cell is attached in increasing total degree. -/
theorem gridCell_mem_past_iff {n m : ℕ} (k : Fin (n+1) → Fin (m+1))
    (x : Fin (n+1) → I) :
    (gridCellMap (n+1) m k x).val ∈ gridPast n m (gridDegree k) ↔ x ∈ gridIncoming k := by
  constructor
  · rintro (hx | ⟨l,hl,hx⟩)
    · exact gridCell_globalHorn_incoming k x hx
    · obtain ⟨i,_,hi⟩ := gridCell_overlap_lower_face k l x hx hl.le (by rintro rfl; omega)
      exact gridIncoming_of_lower_face k x i hi
  · rintro (hx | ⟨i,hx | ⟨hk,hx⟩⟩)
    · exact gridCell_lower_face_mem_past k x 0 hx
    · exact gridCell_lower_face_mem_past k x i.succ hx
    · exact Or.inl (Or.inr ⟨i,Or.inr ((gridCoordinate_eq_one_iff m (k i.succ) (x i.succ)).mpr ⟨hk,hx⟩)⟩)

/-- Different cells in one layer can only overlap in the previously
constructed domain. -/
theorem gridCell_same_layer_inter_subset_past {n m r : ℕ}
    (k l : Fin (n+1) → Fin (m+1)) (hk : gridDegree k = r) (hl : gridDegree l = r)
    (hne : k ≠ l) : gridCell (n+1) m k ∩ gridCell (n+1) m l ⊆ gridPast n m r := by
  rintro y ⟨hyk,hyl⟩
  obtain ⟨x,hx⟩ := (gridCellMap_bijective (n+1) m k).surjective ⟨y,hyk⟩
  have he : (gridCellMap (n+1) m k x).val = y := congrArg Subtype.val hx
  obtain ⟨i,_,hi⟩ := gridCell_overlap_lower_face k l x (he.symm ▸ hyl)
    (by omega) (Ne.symm hne)
  have hp := gridCell_lower_face_mem_past k x i hi
  simpa only [he,hk] using hp

theorem gridIncoming_cylinder_iff {n m : ℕ} (k : Fin (n+1) → Fin (m+1))
    (z : I × (Fin n → I)) :
    HomotopyLifting.cubeCylinderHomeomorph n z ∈ gridIncoming k ↔
      z.1 = 0 ∨ z.2 ∈ HomotopyLifting.cubeFacesBoundary n (gridIncomingFaces k) := by
  constructor
  · rintro (ht | ⟨i,hi | ⟨hk,hi⟩⟩)
    · exact Or.inl ht
    · exact Or.inr ⟨i,false,Or.inl rfl,hi⟩
    · exact Or.inr ⟨i,true,Or.inr hk,hi⟩
  · rintro (ht | ⟨i,b,hb,hi⟩)
    · exact Or.inl ht
    · cases b
      · exact Or.inr ⟨i,Or.inl hi⟩
      · exact Or.inr ⟨i,Or.inr ⟨hb.resolve_left (by simp),hi⟩⟩

end KIP126.Topology.Cube
