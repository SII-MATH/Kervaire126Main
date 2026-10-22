module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Proofs

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

/-- The actual topological colimit of a sequence of closed embeddings
between T1 spaces is T1. -/
theorem t1Space_nat_colimit
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) :
    T1Space c.pt := by
  constructor
  intro x
  apply (TopCat.isClosed_iff_of_isColimit c hc _).mpr
  intro n
  exact (Set.Finite.preimage
    (isClosedEmbedding_nat_colimit F c hc hF n).injective.injOn
    (Set.finite_singleton x)).isClosed

end KIP126.Topology
