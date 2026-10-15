module

public import KIP126.Def.Topology.SimplicialRealization.Classical.Proofs
public import Mathlib.Topology.CWComplex.Classical.Basic

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open Simplicial Set

universe u

/-- The actual nondegenerate simplex characteristic map, with its proved
interior inverse, as a classical CW cell chart. -/
noncomputable def simplexCellChart (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n) :
    PartialEquiv (Fin n → ℝ) |X| :=
  (simplexCharacteristicExtension_injOn X n s).toPartialEquiv
    (simplexCharacteristicExtension X n s) (Metric.ball 0 1)

end KIP126.Topology.SimplicialRealization
