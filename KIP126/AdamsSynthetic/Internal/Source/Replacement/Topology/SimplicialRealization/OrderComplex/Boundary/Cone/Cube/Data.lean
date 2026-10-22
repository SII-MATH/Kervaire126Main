module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Existence.Proofs
import Mathlib.CategoryTheory.Comma.Arrow

@[expose] section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory Simplicial KIP126.Topology.HomotopyLifting
universe u

/-- The finite proper-chain realization identifies the whole original
cube boundary, in the same universe as the original cube. -/
noncomputable def orderBoundaryCubeHomeomorph (n : ℕ) :
    |nerve (orderProperChains (ULift.{u} (Fin (n+1))))| ≃ₜ cubeBoundaryObject.{u} n :=
  (exists_orderBoundaryCone_cube_homeomorph n).choose

/-- The coherent finite order cone identifies the whole original cube. -/
noncomputable def orderBoundaryConeCubeHomeomorph (n : ℕ) :
    |nerve (WithTop (orderProperChains (ULift.{u} (Fin (n+1)))))| ≃ₜ cubeObject.{u} n :=
  (exists_orderBoundaryCone_cube_homeomorph n).choose_spec.choose

/-- The actual finite-order cone base inclusion and the original cube
boundary inclusion are isomorphic as topological arrows, also in dimension zero. -/
noncomputable def orderBoundaryCubeArrowIso (n : ℕ) :
    Arrow.mk (SSet.toTop.map (orderMappingConeSourceTopInclusion
      (orderProperChains (ULift.{u} (Fin (n+1)))))) ≅
        Arrow.mk (cubeBoundaryInclusion.{u} n) :=
  Arrow.isoMk (TopCat.isoOfHomeo (orderBoundaryCubeHomeomorph n))
    (TopCat.isoOfHomeo (orderBoundaryConeCubeHomeomorph n)) (by
      apply ConcreteCategory.hom_ext
      intro x
      exact ((exists_orderBoundaryCone_cube_homeomorph n).choose_spec.choose_spec x).symm)

end KIP126.Topology.SimplicialRealization
