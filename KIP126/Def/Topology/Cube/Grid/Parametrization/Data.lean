module

public import KIP126.Def.Topology.Cube.Grid.Proofs

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- The affine parametrization of an actual closed grid cell. -/
noncomputable def gridCellMap (n m : ℕ) (k : Fin n → Fin (m+1)) :
    C((Fin n → I),gridCell n m k) where
  toFun x := ⟨fun i => gridCoordinate m (k i) (x i),fun i => gridCoordinate_mem m (k i) (x i)⟩
  continuous_toFun := (continuous_pi fun i =>
    (continuous_gridCoordinate m (k i)).comp (continuous_apply i)).subtype_mk _

end KIP126.Topology.Cube
