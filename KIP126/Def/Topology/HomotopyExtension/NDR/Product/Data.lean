module

public import KIP126.Def.Topology.HomotopyExtension.NDR.Predicates

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open scoped unitInterval

/-- Relative deformation time for two neighborhood coordinates. Its value
at the common zero is literal zero; continuity of the deformation output
there follows from the fixed-subspace condition. -/
noncomputable def ndrRelativeTime (r s t : I) : I :=
  ⟨(t : ℝ) * ((s : ℝ) / max (r : ℝ) (s : ℝ)), by
    have hd : 0 ≤ max (r : ℝ) (s : ℝ) := le_trans s.property.1 (le_max_right _ _)
    have hq : 0 ≤ (s : ℝ) / max (r : ℝ) (s : ℝ) := div_nonneg s.property.1 hd
    have hq1 : (s : ℝ) / max (r : ℝ) (s : ℝ) ≤ 1 := by
      by_cases hz : max (r : ℝ) (s : ℝ) = 0
      · rw [hz,div_zero]; norm_num
      · exact (div_le_one (lt_of_le_of_ne hd (Ne.symm hz))).mpr (le_max_right _ _)
    exact ⟨mul_nonneg t.property.1 hq, by nlinarith [t.property.1,t.property.2]⟩⟩

end KIP126.Topology.HomotopyExtension
