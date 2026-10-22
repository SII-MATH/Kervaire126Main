module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Combination.Data
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Rev

@[expose] section

namespace KIP126.Topology.Simplex.BarycentricDecomposition

variable {V : Type*} [Fintype V]

/-- The distinct positive coordinate values of a point of the simplex. -/
noncomputable def levels (y : stdSimplex ℝ V) : Finset ℝ :=
  (Finset.univ.image y).filter (0 < ·)

/-- Distinct positive coordinate values, enumerated in decreasing order. -/
noncomputable def level (y : stdSimplex ℝ V) (i : Fin (levels y).card) : ℝ :=
  (levels y).orderEmbOfFin rfl i.rev

/-- Extend the decreasing coordinate levels by zero after their last index. -/
noncomputable def levelAt (y : stdSimplex ℝ V) (i : ℕ) : ℝ :=
  if h : i < (levels y).card then level y ⟨i,h⟩ else 0

/-- The upper level face corresponding to a positive coordinate value. -/
noncomputable def face (y : stdSimplex ℝ V) (i : Fin (levels y).card) : Finset V :=
  Finset.univ.filter (fun j => level y i ≤ y j)

/-- Successive level gaps, scaled by face cardinality, are the barycentric weights. -/
noncomputable def weight (y : stdSimplex ℝ V) (i : Fin (levels y).card) : ℝ :=
  (face y i).card * (levelAt y i.val - levelAt y (i.val + 1))

end KIP126.Topology.Simplex.BarycentricDecomposition
