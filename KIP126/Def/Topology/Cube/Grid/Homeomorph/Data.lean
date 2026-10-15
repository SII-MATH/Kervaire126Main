module

public import KIP126.Def.Topology.Cube.Grid.Parametrization.Proofs
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- Each closed uniform grid cell is homeomorphic to the entire cube, by
the specified affine coordinate map. -/
noncomputable def gridCellHomeomorph (n m : ℕ) (k : Fin n → Fin (m+1)) :
    (Fin n → I) ≃ₜ gridCell n m k :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (gridCellMap n m k) (gridCellMap_bijective n m k))
    (gridCellMap n m k).continuous

end KIP126.Topology.Cube
