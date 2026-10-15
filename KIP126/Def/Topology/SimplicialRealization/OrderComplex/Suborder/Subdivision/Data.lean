module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Suborder.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The actual subdivision inclusion takes each chain of suborder
vertices to the same finite set of ambient vertices. -/
noncomputable def orderSuborderSubdivisionInclusion (P : Type u) [PartialOrder P]
    (S : Set P) :
    nerve (PartialOrder.NonemptyFiniteChains S) ⟶
      nerve (PartialOrder.NonemptyFiniteChains P) :=
  nerveMap (PartialOrder.NonemptyFiniteChains.orderHomMap
    (OrderHom.Subtype.val (· ∈ S))).monotone.functor

end KIP126.Topology.SimplicialRealization
