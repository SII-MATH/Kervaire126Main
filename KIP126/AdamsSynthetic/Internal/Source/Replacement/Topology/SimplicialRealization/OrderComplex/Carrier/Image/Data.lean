module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Carrier.Predicates
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.LastVertex

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Taking actual finite images of chains is monotone under inclusion,
even when the original vertex assignment is not monotone. -/
noncomputable def orderCarrierChainMap (v : P → Q) (hv : PreservesOrderChains v) :
    PartialOrder.NonemptyFiniteChains P →o PartialOrder.NonemptyFiniteChains Q := by
  classical
  exact {
    toFun := fun c => {
      finset := c.finset.image v
      nonempty := c.nonempty.image v
      comparable := by
        intro a b
        obtain ⟨p,hp,he⟩ := Finset.mem_image.mp a.property
        obtain ⟨q,hq,hf⟩ := Finset.mem_image.mp b.property
        change a.val ≤ b.val ∨ b.val ≤ a.val
        rw [← he,← hf]
        exact hv c p hp q hq }
    monotone' := fun _ _ h => Finset.image_subset_image h }

/-- Choosing the largest vertex of each actual image chain gives an
order map on one further subdivision. -/
noncomputable def orderCarrierMaximum (v : P → Q) (hv : PreservesOrderChains v) :
    PartialOrder.NonemptyFiniteChains P →o Q :=
  (⟨orderChainMaximum,orderChainMaximum_monotone⟩ :
    PartialOrder.NonemptyFiniteChains Q →o Q).comp (orderCarrierChainMap v hv)

/-- The actual simplicial map on the subdivided source defined by the
greatest vertices of its finite image chains. -/
noncomputable def orderCarrierSimplicialMap (v : P → Q) (hv : PreservesOrderChains v) :
    nerve (PartialOrder.NonemptyFiniteChains P) ⟶ nerve Q :=
  nerveMap (orderCarrierMaximum v hv).monotone.functor

end KIP126.Topology.SimplicialRealization
