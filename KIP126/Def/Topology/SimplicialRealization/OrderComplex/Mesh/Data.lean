module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Predicates
public import KIP126.Def.Topology.Simplex.BarycentricSubdivisionMesh.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual vertex assignment after barycentric subdivision of an order. -/
noncomputable def orderSubdivisionVertices {P : Type u} [PartialOrder P] (v : P → E) :
    PartialOrder.NonemptyFiniteChains P → E :=
  fun c => Simplex.BarycentricSubdivisionMesh.avg v c.finset

/-- The actual recursively iterated order of nonempty finite chains. -/
def iteratedOrderSubdivision (P : Type u) [PartialOrder P] : ℕ → PartOrd.{u}
  | 0 => PartOrd.of P
  | n + 1 => PartOrd.of (PartialOrder.NonemptyFiniteChains (iteratedOrderSubdivision P n))

/-- Vertex vectors obtained by taking actual finite face means at every step. -/
noncomputable def iteratedOrderSubdivisionVertices {P : Type u} [PartialOrder P]
    (v : P → E) : (n : ℕ) → iteratedOrderSubdivision P n → E
  | 0 => v
  | n + 1 => orderSubdivisionVertices (iteratedOrderSubdivisionVertices v n)

end KIP126.Topology.SimplicialRealization
