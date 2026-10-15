module

public import KIP126.Def.Topology.Cube.Grid.Data
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

theorem gridVertex_monotone (m : ℕ) : Monotone (gridVertex m) := by
  intro i j hij
  change (i.val : ℝ) / (m+1) ≤ (j.val : ℝ) / (m+1)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem gridCellOrigin_mem (n m : ℕ) (k : Fin n → Fin (m+1)) :
    gridCellOrigin n m k ∈ gridCell n m k := by
  intro i
  exact ⟨le_rfl,gridVertex_monotone m (by change (k i).val ≤ (k i).val+1; omega)⟩

/-- Every interval point belongs to one of the finitely many closed pieces,
including the right endpoint. -/
theorem exists_grid_interval (m : ℕ) (t : I) :
    ∃ k : Fin (m+1), t ∈ Set.Icc (gridVertex m k.castSucc) (gridVertex m k.succ) := by
  let a : ℝ := (m+1) * (t : ℝ)
  have ha : 0 ≤ a := mul_nonneg (by positivity) t.property.1
  let k : Fin (m+1) := ⟨min ⌊a⌋₊ m,Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hkle : (k.val : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
    exact_mod_cast (min_le_left ⌊a⌋₊ m)
  have hklo : (k.val : ℝ) ≤ a := hkle.trans (Nat.floor_le ha)
  have hkhi : a ≤ (k.val : ℝ) + 1 := by
    change a ≤ ((min ⌊a⌋₊ m : ℕ) : ℝ) + 1
    by_cases h : ⌊a⌋₊ ≤ m
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one a).le
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
      dsimp [a]
      nlinarith [t.property.2]
  refine ⟨k,?_,?_⟩
  · change (k.val : ℝ) / (m+1) ≤ (t : ℝ)
    exact (div_le_iff₀ (by positivity)).mpr (by simpa [a,mul_comm] using hklo)
  · change (t : ℝ) ≤ ((k.val+1 : ℕ) : ℝ) / (m+1)
    rw [Nat.cast_add,Nat.cast_one]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa [a,mul_comm] using hkhi)

/-- The finite uniform grid covers the entire actual cube. -/
theorem exists_gridCell (n m : ℕ) (x : Fin n → I) :
    ∃ k : Fin n → Fin (m+1), x ∈ gridCell n m k := by
  choose k hk using fun i => exists_grid_interval m (x i)
  exact ⟨k,hk⟩

theorem gridCell_isClosed (n m : ℕ) (k : Fin n → Fin (m+1)) : IsClosed (gridCell n m k) := by
  have h (i : Fin n) : IsClosed {x : Fin n → I |
      x i ∈ Set.Icc (gridVertex m (k i).castSucc) (gridVertex m (k i).succ)} :=
    isClosed_Icc.preimage (continuous_apply i)
  simpa only [gridCell,Set.setOf_forall] using isClosed_iInter h

/-- The supremum metric diameter from the lower vertex is at most the mesh. -/
theorem gridCell_dist_origin_le (n m : ℕ) (k : Fin n → Fin (m+1))
    {x : Fin n → I} (hx : x ∈ gridCell n m k) :
    dist x (gridCellOrigin n m k) ≤ 1 / (m+1 : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hxi := hx i
  change (k i).val / (m+1 : ℝ) ≤ (x i : ℝ) ∧
    (x i : ℝ) ≤ (((k i).val+1 : ℕ) : ℝ) / (m+1) at hxi
  change |(x i : ℝ) - (k i).val / (m+1 : ℝ)| ≤ 1 / (m+1 : ℝ)
  rw [abs_of_nonneg (sub_nonneg.mpr hxi.1)]
  have hhi := hxi.2
  rw [Nat.cast_add,Nat.cast_one,add_div] at hhi
  linarith

/-- A sufficiently fine finite uniform cube subdivision is subordinate to
any open cover, including in dimension zero. -/
theorem exists_grid_subordinate_open_cover (n : ℕ) {ι : Type*}
    (U : ι → Set (Fin n → I)) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.univ ⊆ ⋃ i, U i) :
    ∃ m : ℕ, ∀ k : Fin n → Fin (m+1), ∃ i, gridCell n m k ⊆ U i := by
  obtain ⟨δ,hδ,hballs⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m,fun k => ?_⟩
  obtain ⟨i,hi⟩ := hballs (gridCellOrigin n m k) (Set.mem_univ _)
  refine ⟨i,fun x hx => hi ?_⟩
  exact (gridCell_dist_origin_le n m k hx).trans_lt hm

/-- A continuous cube map admits a grid whose every closed cell lies
over one member of an open cover of its image. -/
theorem exists_grid_image_subordinate {B : Type*} [TopologicalSpace B]
    (n : ℕ) (H : C((Fin n → I),B)) {ι : Type*} (U : ι → Set B)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.range H ⊆ ⋃ i, U i) :
    ∃ m : ℕ, ∀ k : Fin n → Fin (m+1), ∃ i, H '' gridCell n m k ⊆ U i := by
  obtain ⟨m,hm⟩ := exists_grid_subordinate_open_cover n (fun i => H ⁻¹' U i)
    (fun i => (hU i).preimage H.continuous) (by
      intro x _
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover ⟨x,rfl⟩)
      exact Set.mem_iUnion.mpr ⟨i,hi⟩)
  exact ⟨m,fun k => (hm k).imp fun i hi => Set.image_subset_iff.mpr hi⟩

@[continuity, fun_prop] theorem continuous_gridCoordinate (m : ℕ) (k : Fin (m+1)) :
    Continuous (gridCoordinate m k) := by
  apply Continuous.subtype_mk
  exact (continuous_const.add continuous_subtype_val).div_const _

theorem gridCoordinate_mem (m : ℕ) (k : Fin (m+1)) (t : I) :
    gridCoordinate m k t ∈ Set.Icc (gridVertex m k.castSucc) (gridVertex m k.succ) := by
  constructor
  · change (k.val : ℝ) / (m+1) ≤ ((k.val : ℝ) + (t : ℝ)) / (m+1)
    exact div_le_div_of_nonneg_right (by linarith [t.property.1]) (by positivity)
  · change ((k.val : ℝ) + (t : ℝ)) / (m+1) ≤ ((k.val+1 : ℕ) : ℝ) / (m+1)
    rw [Nat.cast_add,Nat.cast_one]
    exact div_le_div_of_nonneg_right (by linarith [t.property.2]) (by positivity)

theorem gridCoordinate_injective (m : ℕ) (k : Fin (m+1)) :
    Function.Injective (gridCoordinate m k) := by
  intro s t h
  have hval := congrArg Subtype.val h
  change ((k.val : ℝ) + (s : ℝ)) / (m+1) = ((k.val : ℝ) + (t : ℝ)) / (m+1) at hval
  apply Subtype.ext
  exact add_left_cancel ((div_left_inj' (by positivity : (m+1 : ℝ) ≠ 0)).mp hval)

theorem gridCoordinate_surjective_interval (m : ℕ) (k : Fin (m+1)) (x : I)
    (hx : x ∈ Set.Icc (gridVertex m k.castSucc) (gridVertex m k.succ)) :
    ∃ t : I, gridCoordinate m k t = x := by
  have hm : (0 : ℝ) < m+1 := by positivity
  change (k.val : ℝ) / (m+1) ≤ (x : ℝ) ∧ (x : ℝ) ≤ ((k.val+1 : ℕ) : ℝ) / (m+1) at hx
  have h₀ := (div_le_iff₀ hm).mp hx.1
  have h₁ := (le_div_iff₀ hm).mp hx.2
  rw [Nat.cast_add,Nat.cast_one] at h₁
  let t : I := ⟨(x : ℝ) * (m+1) - k.val,by constructor <;> linarith⟩
  refine ⟨t,Subtype.ext ?_⟩
  change ((k.val : ℝ) + ((x : ℝ) * (m+1) - k.val)) / (m+1) = (x : ℝ)
  field_simp
  ring

end KIP126.Topology.Cube
