module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

noncomputable def cubeFacesRetractionFunction {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) : I × (Fin n → I) := by
  have hp := cubeFacesScale_pos faces z
  have hlo := cubeFacesGauge_le_scale faces z none
  change (2-(z.1 : ℝ))/2 ≤ cubeFacesScale faces z at hlo
  have hhi := cubeFacesScale_le_one faces z
  refine (⟨2-(2-(z.1 : ℝ))/cubeFacesScale faces z,?_,?_⟩,
    fun i => projIcc 0 1 zero_le_one (((2*(z.2 i : ℝ)-1)/cubeFacesScale faces z+1)/2))
  · have hd : (2-(z.1 : ℝ))/cubeFacesScale faces z ≤ 2 :=
      (div_le_iff₀ hp).mpr (by linarith)
    linarith
  · have hd : 1 ≤ (2-(z.1 : ℝ))/cubeFacesScale faces z :=
      (le_div_iff₀ hp).mpr (by linarith [z.1.property.2])
    linarith

end KIP126.Topology.HomotopyLifting
