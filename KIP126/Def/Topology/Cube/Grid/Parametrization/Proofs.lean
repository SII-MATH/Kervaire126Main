module

public import KIP126.Def.Topology.Cube.Grid.Parametrization.Data

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

theorem gridCellMap_bijective (n m : ℕ) (k : Fin n → Fin (m+1)) :
    Function.Bijective (gridCellMap n m k) := by
  constructor
  · intro x y h
    funext i
    apply gridCoordinate_injective m (k i)
    exact congrArg (fun z : gridCell n m k => z.val i) h
  · intro x
    choose t ht using fun i => gridCoordinate_surjective_interval m (k i) (x.val i) (x.property i)
    refine ⟨t,Subtype.ext (funext ht)⟩

@[simp] theorem gridCoordinate_zero (m : ℕ) (k : Fin (m+1)) :
    gridCoordinate m k 0 = gridVertex m k.castSucc := by
  apply Subtype.ext
  change ((k.val : ℝ) + 0) / (m+1) = (k.val : ℝ) / (m+1)
  simp

@[simp] theorem gridCoordinate_one (m : ℕ) (k : Fin (m+1)) :
    gridCoordinate m k 1 = gridVertex m k.succ := by
  apply Subtype.ext
  change ((k.val : ℝ) + 1) / (m+1) = ((k.val+1 : ℕ) : ℝ) / (m+1)
  simp

theorem gridCoordinate_eq_lower_iff (m : ℕ) (k : Fin (m+1)) (t : I) :
    gridCoordinate m k t = gridVertex m k.castSucc ↔ t = 0 := by
  rw [← gridCoordinate_zero m k]
  exact (gridCoordinate_injective m k).eq_iff

theorem gridCoordinate_eq_upper_iff (m : ℕ) (k : Fin (m+1)) (t : I) :
    gridCoordinate m k t = gridVertex m k.succ ↔ t = 1 := by
  rw [← gridCoordinate_one m k]
  exact (gridCoordinate_injective m k).eq_iff

/-- A coordinate reaches the global lower face exactly in the first cell
and on its local lower face. -/
theorem gridCoordinate_eq_zero_iff (m : ℕ) (k : Fin (m+1)) (t : I) :
    gridCoordinate m k t = 0 ↔ k.val = 0 ∧ t = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change ((k.val : ℝ) + (t : ℝ)) / (m+1) = 0 at hv
    have hn : (m+1 : ℝ) ≠ 0 := by positivity
    have he := (div_eq_zero_iff).mp hv
    have hsum := he.resolve_right hn
    have hk : (k.val : ℝ) = 0 := by linarith [t.property.1,Nat.cast_nonneg (α := ℝ) k.val]
    refine ⟨by exact_mod_cast hk,Subtype.ext ?_⟩
    change (t : ℝ) = 0
    linarith
  · rintro ⟨hk,rfl⟩
    apply Subtype.ext
    change ((k.val : ℝ) + 0) / (m+1) = 0
    simp [hk]

/-- A coordinate reaches the global upper face exactly in the last cell
and on its local upper face. -/
theorem gridCoordinate_eq_one_iff (m : ℕ) (k : Fin (m+1)) (t : I) :
    gridCoordinate m k t = 1 ↔ k.val = m ∧ t = 1 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change ((k.val : ℝ) + (t : ℝ)) / (m+1) = 1 at hv
    have hsum := (div_eq_one_iff_eq (by positivity : (m+1 : ℝ) ≠ 0)).mp hv
    have hk : (k.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ k.is_lt
    have hke : (k.val : ℝ) = m := by linarith [t.property.2]
    refine ⟨by exact_mod_cast hke,Subtype.ext ?_⟩
    change (t : ℝ) = 1
    linarith
  · rintro ⟨hk,rfl⟩
    apply Subtype.ext
    change ((k.val : ℝ) + 1) / (m+1) = 1
    rw [hk]
    exact div_self (by positivity)

end KIP126.Topology.Cube
