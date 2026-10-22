module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.LastVertex
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The actual simplicial last-vertex comparison for order-complex
subdivision, defined for every partial order. -/
noncomputable def orderSubdivisionLastVertex (P : Type u) [PartialOrder P] :
    nerve (PartialOrder.NonemptyFiniteChains P) ⟶ nerve P :=
  nerveMap orderChainMaximum_monotone.functor

end KIP126.Topology.SimplicialRealization
