module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The actual nerve inclusion of a suborder on a specified vertex set. -/
def orderSuborderInclusion (P : Type u) [PartialOrder P] (S : Set P) :
    nerve S ⟶ nerve P :=
  nerveMap (OrderHom.Subtype.val (· ∈ S)).monotone.functor

end KIP126.Topology.SimplicialRealization
