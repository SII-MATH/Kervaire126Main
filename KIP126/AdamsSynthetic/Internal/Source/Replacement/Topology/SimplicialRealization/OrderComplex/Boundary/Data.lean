module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

/-- The actual suborder of chains omitting at least one ambient vertex. -/
def orderProperChains (P : Type u) [PartialOrder P] [Fintype P] :
    Set (PartialOrder.NonemptyFiniteChains P) := {c | c.finset ≠ Finset.univ}

/-- The actual simplicial inclusion of the proper-chain suborder. -/
def orderBoundaryInclusion (P : Type u) [PartialOrder P] [Fintype P] :
    nerve (orderProperChains P) ⟶ nerve (PartialOrder.NonemptyFiniteChains P) :=
  orderSuborderInclusion (PartialOrder.NonemptyFiniteChains P) (orderProperChains P)

/-- The coordinate boundary in the original actual order-complex realization. -/
def orderCoordinateBoundary (P : Type u) [PartialOrder P] [Fintype P] :
    Set |nerve P| := {x | ∃ p, orderComplexCoordinates P x p = 0}

end KIP126.Topology.SimplicialRealization
