module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The actual nerve inclusion of a suborder on a specified vertex set. -/
def orderSuborderInclusion (P : Type u) [PartialOrder P] (S : Set P) :
    nerve S ⟶ nerve P :=
  nerveMap (OrderHom.Subtype.val (· ∈ S)).monotone.functor

end KIP126.Topology.SimplicialRealization
