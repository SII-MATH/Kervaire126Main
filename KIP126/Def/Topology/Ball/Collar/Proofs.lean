module

public import KIP126.Def.Topology.Ball.Collar.Data
public import KIP126.Def.Topology.Pushout.Neighborhood.Proofs

@[expose] public section

namespace KIP126.Topology.Ball

open Metric Set CategoryTheory CategoryTheory.Limits _root_.Topology

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false

omit [NormedSpace ℝ E] in
/-- The radial collar is open in the actual closed ball. -/
theorem unitDiskCollar_isOpen : IsOpen (unitDiskCollar E) :=
  isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)

omit [NormedSpace ℝ E] in
/-- Every boundary point lies in the radial collar. -/
theorem unitDiskBoundary_mem_collar (s : sphere (0 : E) 1) :
    unitDiskBoundary E s ∈ unitDiskCollar E := by
  have hs : ‖s.1‖ = 1 := mem_sphere_zero_iff_norm.mp s.2
  change (1:ℝ)/2 < ‖s.1‖
  rw [hs]
  norm_num

/-- The collar projection fixes each actual boundary point. -/
theorem unitDiskCollarProjection_boundary (s : sphere (0 : E) 1) :
    unitDiskCollarProjection E ⟨unitDiskBoundary E s,unitDiskBoundary_mem_collar s⟩ = s := by
  apply Subtype.ext
  have hs : ‖s.1‖ = 1 := mem_sphere_zero_iff_norm.mp s.2
  simp [unitDiskCollarProjection,unitDiskBoundary,hs]

end KIP126.Topology.Ball
