module

import Mathlib.AlgebraicTopology.TopologicalSimplex

@[expose] section

namespace KIP126.Topology.Simplex

/-- Barycentric combination of a finite family of simplex points,
written in coordinates. -/
noncomputable def combinationCoordinates {A B : Type*} [Fintype A] [Fintype B]
    (v : A → stdSimplex ℝ B) (t : stdSimplex ℝ A) (b : B) : ℝ :=
  ∑ a, t a * v a b

end KIP126.Topology.Simplex
