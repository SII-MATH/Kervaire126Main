module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace KIP126.Topology.Ball

open Metric Set CategoryTheory

universe u
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard sphere inclusion into its closed unit ball. -/
noncomputable def unitDiskBoundary :
    TopCat.of (sphere (0 : E) 1) ⟶ TopCat.of (closedBall (0 : E) 1) :=
  TopCat.ofHom ⟨Set.inclusion sphere_subset_closedBall,continuous_inclusion _⟩

/-- The outer half of the unit disk, a genuine open neighborhood of its boundary. -/
def unitDiskCollar : Set (closedBall (0 : E) 1) := {x | (1:ℝ)/2 < ‖x.1‖}

/-- Radial projection of the open disk collar onto its actual boundary. -/
noncomputable def unitDiskCollarProjection : C(unitDiskCollar E,sphere (0 : E) 1) := by
  let g : unitDiskCollar E → ({0}ᶜ : Set E) := fun x => ⟨x.1.1,by
      have hx : (1:ℝ)/2 < ‖x.1.1‖ := x.2
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
      exact norm_ne_zero_iff.mp (by linarith)⟩
  have hg : Continuous g :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact ⟨fun x => ((homeomorphUnitSphereProd E) (g x)).1,
    continuous_fst.comp ((homeomorphUnitSphereProd E).continuous.comp hg)⟩

end KIP126.Topology.Ball
