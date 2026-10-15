module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.LastVertex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The actual simplicial last-vertex comparison for order-complex
subdivision, defined for every partial order. -/
noncomputable def orderSubdivisionLastVertex (P : Type u) [PartialOrder P] :
    nerve (PartialOrder.NonemptyFiniteChains P) ⟶ nerve P :=
  nerveMap orderChainMaximum_monotone.functor

end KIP126.Topology.SimplicialRealization
