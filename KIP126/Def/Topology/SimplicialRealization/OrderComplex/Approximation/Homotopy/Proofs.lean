module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Approximation.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Carrier.Homotopy.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- An arbitrary continuous map between actual finite order-complex
realizations is homotopic to a genuine simplicial map after a finite
number of actual subdivisions. The homotopy retains every zero
coordinate and fixes every original vertex fiber. -/
theorem exists_iteratedOrderSubdivision_simplicial_approximation (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : C(|nerve P|,|nerve Q|)) :
    ∃ (n : ℕ) (φ : nerve (iteratedOrderSubdivision P (n+1)) ⟶ nerve Q),
      ∃ H : (f.comp ⟨iteratedOrderSubdivisionHomeomorph P (n+1),
          (iteratedOrderSubdivisionHomeomorph P (n+1)).continuous⟩).Homotopy
        (SSet.toTop.map φ).hom,
        (∀ (t : I) (x : |nerve (iteratedOrderSubdivision P (n+1))|) (q : Q),
          orderComplexCoordinates Q (f (iteratedOrderSubdivisionHomeomorph P (n+1) x)) q = 0 →
            orderComplexCoordinates Q (H (t,x)) q = 0) ∧
        ∀ (t : I) (x : |nerve (iteratedOrderSubdivision P (n+1))|) (q : Q),
          f (iteratedOrderSubdivisionHomeomorph P (n+1) x) = orderVertex Q q →
            H (t,x) = orderVertex Q q := by
  obtain ⟨n,v,hv⟩ := exists_iteratedOrderSubdivision_star_assignment P Q f
  letI := iteratedOrderSubdivisionFintype P n
  obtain ⟨H,hzero,hvertex⟩ := hv.exists_carrier_homotopy_fixing_vertices
  exact ⟨n,orderCarrierSimplicialMap v hv.preservesOrderChains,H,hzero,hvertex⟩

/-- The actual simplicial approximation is relative to any region on
which the original map takes a single specified vertex value. -/
theorem exists_iteratedOrderSubdivision_simplicial_approximation_rel (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : C(|nerve P|,|nerve Q|)) (B : Set |nerve P|) (q : Q)
    (hB : ∀ x ∈ B, f x = orderVertex Q q) :
    ∃ (n : ℕ) (φ : nerve (iteratedOrderSubdivision P (n+1)) ⟶ nerve Q),
      ContinuousMap.HomotopicRel
        (f.comp ⟨iteratedOrderSubdivisionHomeomorph P (n+1),
          (iteratedOrderSubdivisionHomeomorph P (n+1)).continuous⟩)
        (SSet.toTop.map φ).hom
        ((iteratedOrderSubdivisionHomeomorph P (n+1)) ⁻¹' B) := by
  obtain ⟨n,φ,H,_,hfix⟩ := exists_iteratedOrderSubdivision_simplicial_approximation P Q f
  refine ⟨n,φ,⟨⟨H,?_⟩⟩⟩
  intro t x hx
  exact (hfix t x q (hB _ hx)).trans (hB _ hx).symm

end KIP126.Topology.SimplicialRealization
