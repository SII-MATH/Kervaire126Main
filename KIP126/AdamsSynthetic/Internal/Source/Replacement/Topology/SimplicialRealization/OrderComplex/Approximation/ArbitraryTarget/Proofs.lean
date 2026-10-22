module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Compact.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Approximation.Order.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- A continuous map from a finite order complex into an arbitrary
order complex is homotopic to an actual order map after finitely many
subdivisions. No finiteness assumption on the target is needed: its
finite induced suborder is obtained from the actual compact image. -/
theorem exists_iteratedOrderSubdivision_order_approximation_arbitrary_target
    (P Q : Type u) [PartialOrder P] [PartialOrder Q] [Fintype P]
    (f : C(|nerve P|,|nerve Q|)) :
    ∃ (n : ℕ) (a : iteratedOrderSubdivision P (n+1) →o Q),
      (f.comp ⟨iteratedOrderSubdivisionHomeomorph P (n+1),
        (iteratedOrderSubdivisionHomeomorph P (n+1)).continuous⟩).Homotopic
          (SSet.toTop.map (nerveMap a.monotone.functor)).hom := by
  classical
  letI := finite_nerve_of_finite_order P
  letI := compactSpace_of_finite (nerve P)
  obtain ⟨S,hS,g,hg⟩ := continuousMap_factor_finite_suborder Q f
  letI : Fintype S := hS.fintype
  obtain ⟨n,a,H,_,_⟩ := exists_iteratedOrderSubdivision_order_approximation P S g
  let b : iteratedOrderSubdivision P (n+1) →o Q :=
    (OrderHom.Subtype.val (· ∈ S)).comp a
  let j := SSet.toTop.map (orderSuborderInclusion Q S)
  have hs : j.hom.comp (g.comp
      ⟨iteratedOrderSubdivisionHomeomorph P (n+1),
        (iteratedOrderSubdivisionHomeomorph P (n+1)).continuous⟩) =
      f.comp ⟨iteratedOrderSubdivisionHomeomorph P (n+1),
        (iteratedOrderSubdivisionHomeomorph P (n+1)).continuous⟩ := by
    ext x
    exact hg _
  have ht : j.hom.comp (SSet.toTop.map (nerveMap a.monotone.functor)).hom =
      (SSet.toTop.map (nerveMap b.monotone.functor)).hom := by
    change (SSet.toTop.map (nerveMap a.monotone.functor) ≫
      SSet.toTop.map (orderSuborderInclusion Q S)).hom = _
    rw [← Functor.map_comp]
    rfl
  exact ⟨n,b,⟨((ContinuousMap.Homotopy.refl j.hom).comp H).cast hs ht⟩⟩

end KIP126.Topology.SimplicialRealization
