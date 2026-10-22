module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Stars.Data

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

/-- A vertex assignment carries every actual nonempty chain to a chain,
without requiring the assignment itself to preserve order. -/
def PreservesOrderChains {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (v : P → Q) : Prop :=
  ∀ c : PartialOrder.NonemptyFiniteChains P, ∀ p ∈ c.finset, ∀ q ∈ c.finset,
    v p ≤ v q ∨ v q ≤ v p

/-- The image under an actual continuous map of every source vertex star
lies in the star of its assigned target vertex. -/
def IsOrderStarAssignment {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    [Fintype P] [Fintype Q] (f : C(|nerve P|,|nerve Q|)) (v : P → Q) : Prop :=
  ∀ p, Set.MapsTo f (orderOpenStar P p) (orderOpenStar Q (v p))

end KIP126.Topology.SimplicialRealization
