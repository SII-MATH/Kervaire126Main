module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace KIP126.Topology.Simplex

/-- The cumulative barycentric mass before the given vertex cut. -/
noncomputable def cumulative {n : ℕ} (x : stdSimplex ℝ (Fin (n+1))) (k : ℕ) : ℝ :=
  ∑ i : Fin (n+1), if i.1 < k then x i else 0

/-- The common mass of two consecutive intervals in the ordered barycentric
partitions. This is the canonical monotone coupling used to triangulate
products of simplices. -/
noncomputable def couplingMass {p q : ℕ}
    (x : stdSimplex ℝ (Fin (p+1))) (y : stdSimplex ℝ (Fin (q+1)))
    (i : Fin (p+1)) (j : Fin (q+1)) : ℝ :=
  min (cumulative x (i.1+1)) (cumulative y (j.1+1)) -
    min (cumulative x i.1) (cumulative y (j.1+1)) -
    min (cumulative x (i.1+1)) (cumulative y j.1) +
    min (cumulative x i.1) (cumulative y j.1)

end KIP126.Topology.Simplex
