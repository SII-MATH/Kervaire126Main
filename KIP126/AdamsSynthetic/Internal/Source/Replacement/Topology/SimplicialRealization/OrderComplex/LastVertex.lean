module

import Mathlib.Order.NonemptyFiniteChains
import Mathlib.Order.Preorder.Finite

@[expose] section

section

namespace KIP126.Topology.SimplicialRealization

/-- The greatest vertex of a nonempty finite chain in a partial order. -/
noncomputable def orderChainMaximum {P : Type*} [PartialOrder P]
    (c : PartialOrder.NonemptyFiniteChains P) : P :=
  Classical.choose (c.finset.exists_maximal c.nonempty)

end KIP126.Topology.SimplicialRealization

end

section

namespace KIP126.Topology.SimplicialRealization

variable {P Q : Type*} [PartialOrder P] [PartialOrder Q]

/-- The greatest chain vertex belongs to that chain. -/
theorem orderChainMaximum_mem (c : PartialOrder.NonemptyFiniteChains P) :
    orderChainMaximum c ∈ c.finset :=
  (Classical.choose_spec (c.finset.exists_maximal c.nonempty)).1

/-- Every chain vertex is at most its greatest vertex. -/
theorem le_orderChainMaximum (c : PartialOrder.NonemptyFiniteChains P)
    (p : P) (hp : p ∈ c.finset) : p ≤ orderChainMaximum c := by
  obtain h | h := c.comparable ⟨p,hp⟩ ⟨orderChainMaximum c,orderChainMaximum_mem c⟩
  · exact h
  · exact (Classical.choose_spec (c.finset.exists_maximal c.nonempty)).2 hp h

/-- Inclusion of chains is monotone on their greatest vertices. -/
theorem orderChainMaximum_monotone :
    Monotone (orderChainMaximum : PartialOrder.NonemptyFiniteChains P → P) := by
  intro a b hab
  exact le_orderChainMaximum b _ (hab (orderChainMaximum_mem a))

/-- Greatest vertices commute with arbitrary monotone maps, including
ones that identify vertices. -/
theorem orderChainMaximum_map (c : PartialOrder.NonemptyFiniteChains P) (f : P →o Q) :
    orderChainMaximum (c.map f) = f (orderChainMaximum c) := by
  apply le_antisymm
  · obtain ⟨p,hp,hf⟩ := (PartialOrder.NonemptyFiniteChains.mem_map_iff c f _).mp
      (orderChainMaximum_mem (c.map f))
    rw [← hf]
    exact f.monotone (le_orderChainMaximum c p hp)
  · exact le_orderChainMaximum (c.map f) _
      ((PartialOrder.NonemptyFiniteChains.mem_map_iff c f _).mpr
        ⟨orderChainMaximum c,orderChainMaximum_mem c,rfl⟩)

end KIP126.Topology.SimplicialRealization

end
