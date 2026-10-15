module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory Simplicial KIP126.Topology.HomotopyLifting
universe u

/-- The chosen cube homeomorphism agrees exactly with the chosen
boundary homeomorphism on every original point of the cone base. -/
theorem orderBoundaryConeCubeHomeomorph_base (n : ℕ)
    (x : |nerve (orderProperChains (ULift.{u} (Fin (n+1))))|) :
    orderBoundaryConeCubeHomeomorph n
        (SSet.toTop.map (orderMappingConeSourceTopInclusion
          (orderProperChains (ULift.{u} (Fin (n+1))))) x) =
      cubeBoundaryInclusion n (orderBoundaryCubeHomeomorph n x) :=
  (exists_orderBoundaryCone_cube_homeomorph n).choose_spec.choose_spec x

end KIP126.Topology.SimplicialRealization
