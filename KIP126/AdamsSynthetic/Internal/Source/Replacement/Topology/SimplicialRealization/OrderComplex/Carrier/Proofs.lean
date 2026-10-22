module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Carrier.Image.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Stars.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A genuine star assignment preserves chains, as witnessed by the
image of the actual common barycenter of each source chain. -/
theorem IsOrderStarAssignment.preservesOrderChains [Fintype P] [Fintype Q]
    {f : C(|nerve P|,|nerve Q|)} {v : P → Q} (h : IsOrderStarAssignment f v) :
    PreservesOrderChains v := by
  intro c p hp q hq
  obtain ⟨b,_⟩ := exists_orderOpenStarIntersection_barycenter P c
  exact orderComplexCoordinates_hasChainSupport Q (f b.val) (v p) (v q)
    (h p (b.property p hp)) (h q (b.property q hq))

/-- The constructed image chain has exactly the finite image of the
original vertices, with no larger carrier chosen. -/
theorem orderCarrierChainMap_finset (v : P → Q) (hv : PreservesOrderChains v)
    (c : PartialOrder.NonemptyFiniteChains P) :
    (orderCarrierChainMap v hv c).finset = c.finset.image v := rfl

/-- Every chosen greatest image vertex is the assigned image of some
actual vertex in the source chain. -/
theorem orderCarrierMaximum_mem (v : P → Q) (hv : PreservesOrderChains v)
    (c : PartialOrder.NonemptyFiniteChains P) :
    ∃ p ∈ c.finset, v p = orderCarrierMaximum v hv c := by
  have hm := orderChainMaximum_mem (orderCarrierChainMap v hv c)
  exact Finset.mem_image.mp hm

/-- On every actual source flag, the constructed simplicial map pushes
the simplex weights to the selected greatest image vertices. -/
theorem orderCarrierSimplicialMap_coordinates [Fintype Q]
    (v : P → Q) (hv : PreservesOrderChains v) {d : SimplexCategoryᵒᵖ}
    (s : (nerve (PartialOrder.NonemptyFiniteChains P)).obj d)
    (t : stdSimplex ℝ (Fin (d.unop.len+1))) :
    orderComplexCoordinates Q
      (SSet.toTop.map (orderCarrierSimplicialMap v hv) (simplexPoint _ s t)) =
      stdSimplex.map (fun k => orderCarrierMaximum v hv (s.obj k)) t := by
  rw [simplexPoint_map,orderComplexCoordinates_simplex]
  rfl

end KIP126.Topology.SimplicialRealization
