module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

/-- A simplex point has chain support when its positive coordinates
are supported on mutually comparable vertices. -/
def HasChainSupport {P : Type*} [PartialOrder P] [Fintype P]
    (y : stdSimplex ℝ P) : Prop :=
  ∀ p q, 0 < y p → 0 < y q → p ≤ q ∨ q ≤ p

/-- A bound on the number of vertices in each nonempty order simplex. -/
def OrderChainSizeLE (P : Type*) [PartialOrder P] (N : ℕ) : Prop :=
  ∀ c : PartialOrder.NonemptyFiniteChains P, c.finset.card ≤ N

end KIP126.Topology.SimplicialRealization
