module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Mesh.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every actual nonempty finite chain has vertex diameter at most the stated bound. -/
def OrderMeshBound (P : Type*) [PartialOrder P] (v : P → E) (D : ℝ) : Prop :=
  ∀ c : PartialOrder.NonemptyFiniteChains P,
    ∀ p ∈ c.finset, ∀ q ∈ c.finset, dist (v p) (v q) ≤ D

end KIP126.Topology.SimplicialRealization
