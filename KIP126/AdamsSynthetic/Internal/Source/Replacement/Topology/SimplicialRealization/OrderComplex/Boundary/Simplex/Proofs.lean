module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

/-- For a finite linear order, every simplex support is a chain, so
the actual order-complex coordinates give the whole standard simplex. -/
theorem exists_linearOrderCoordinates_homeomorph (P : Type u) [LinearOrder P] [Fintype P] :
    ∃ h : |nerve P| ≃ₜ stdSimplex ℝ P, ∀ x, h x = orderComplexCoordinates P x := by
  obtain ⟨e,he⟩ := exists_orderComplexCoordinates_homeomorph P
  have hs : (setOf HasChainSupport : Set (stdSimplex ℝ P)) = Set.univ := by
    ext y
    simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
    intro p q _ _
    exact le_total p q
  exact ⟨e.trans ((Homeomorph.setCongr hs).trans (Homeomorph.Set.univ _)),he⟩

/-- The actual proper-chain simplicial boundary of a finite linear
order is homeomorphic to the entire standard-simplex coordinate boundary.
Its forward map is the original barycentric projection. -/
theorem exists_orderBoundary_stdSimplex_homeomorph (P : Type u)
    [LinearOrder P] [Fintype P] :
    ∃ h : |nerve (orderProperChains P)| ≃ₜ
        {y : stdSimplex ℝ P // ∃ p, y p = 0},
      ∀ x, (h x).val =
        orderSubdivisionCoordinates P (SSet.toTop.map (orderBoundaryInclusion P) x) := by
  obtain ⟨b,hb⟩ := exists_orderBoundary_homeomorph P
  obtain ⟨e,he⟩ := exists_linearOrderCoordinates_homeomorph P
  have hi (x : |nerve P|) : x ∈ orderCoordinateBoundary P ↔ ∃ p, e x p = 0 := by
    rw [he]
    rfl
  refine ⟨b.trans (e.subtype hi),?_⟩
  intro x
  change e (b x).val = _
  rw [he,hb,orderSubdivisionHomeomorph_coordinates]

end KIP126.Topology.SimplicialRealization
