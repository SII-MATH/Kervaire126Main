module

public import KIP126.Def.Topology.Cube.Grid.Homeomorph.Data

@[expose] public section

namespace KIP126.Topology.Cube

/-- The finite layer of a grid cell, increasing strictly along each grid direction. -/
def gridDegree {n m : ℕ} (k : Fin n → Fin (m+1)) : ℕ := ∑ i, (k i).val

end KIP126.Topology.Cube
