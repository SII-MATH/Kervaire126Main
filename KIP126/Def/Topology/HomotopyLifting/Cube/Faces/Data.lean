module

public import KIP126.Def.Topology.HomotopyLifting.Data
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- A selected union of cube faces: `false` denotes the zero face and
`true` the one face. -/
def cubeFacesBoundary (n : ℕ) (faces : Set (Fin n × Bool)) : Set (Fin n → I) :=
  {z | ∃ i b, (i,b) ∈ faces ∧ z i = if b then 1 else 0}

noncomputable def cubeFacesGauge {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) : Option (Fin n × Bool) → ℝ := by
  classical
  exact fun q => match q with
    | none => (2-(z.1 : ℝ))/2
    | some (i,b) => if (i,b) ∈ faces then max 0 (if b then 2*(z.2 i : ℝ)-1 else 1-2*(z.2 i : ℝ)) else 0

noncomputable def cubeFacesScale {n : ℕ} (faces : Set (Fin n × Bool))
    (z : I × (Fin n → I)) : ℝ := ‖cubeFacesGauge faces z‖

end KIP126.Topology.HomotopyLifting
