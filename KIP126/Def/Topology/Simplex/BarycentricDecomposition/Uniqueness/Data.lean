module

public import KIP126.Def.Topology.Simplex.BarycentricDecomposition.Data
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace KIP126.Topology.Simplex.BarycentricDecomposition

open scoped Classical

/-- Tail sums of the positive per-vertex masses along a flag. -/
noncomputable def tailMass {m : ℕ} (a : Fin m → ℝ) (r : ℕ) : ℝ :=
  ∑ k, if r ≤ k.val then a k else 0

/-- Coordinates obtained by assigning constant mass on each face of a flag. -/
noncomputable def flagSum {V : Type*} {m : ℕ} (c : Fin m → Finset V)
    (a : Fin m → ℝ) (j : V) : ℝ := ∑ k, if j ∈ c k then a k else 0

end KIP126.Topology.Simplex.BarycentricDecomposition
