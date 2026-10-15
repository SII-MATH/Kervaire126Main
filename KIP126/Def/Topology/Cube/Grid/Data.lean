module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- The uniform subdivision of an interval into `m+1` pieces. -/
noncomputable def gridVertex (m : ℕ) (k : Fin (m+2)) : I :=
  ⟨(k.val : ℝ) / (m+1),by
    have hm : (0 : ℝ) < m+1 := by positivity
    constructor
    · positivity
    · apply (div_le_one hm).mpr
      exact_mod_cast Nat.le_of_lt_succ k.is_lt⟩

/-- One actual closed box of the uniform finite cube subdivision. -/
def gridCell (n m : ℕ) (k : Fin n → Fin (m+1)) : Set (Fin n → I) :=
  {x | ∀ i, x i ∈ Set.Icc (gridVertex m (k i).castSucc) (gridVertex m (k i).succ)}

/-- The lower vertex of a closed grid cell. -/
noncomputable def gridCellOrigin (n m : ℕ) (k : Fin n → Fin (m+1)) : Fin n → I :=
  fun i => gridVertex m (k i).castSucc

/-- The affine coordinate in one closed subdivision interval. -/
noncomputable def gridCoordinate (m : ℕ) (k : Fin (m+1)) (t : I) : I :=
  ⟨((k.val : ℝ) + (t : ℝ)) / (m+1),by
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1) (by positivity)
    · apply (div_le_one (by positivity)).mpr
      have hk : (k.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ k.is_lt
      linarith [t.property.2]⟩

end KIP126.Topology.Cube
