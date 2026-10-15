module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Approximation.Homotopy.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual finite-order approximation is induced by an order map,
so it can be used directly as the attaching map of an order mapping
cylinder or mapping cone. Its homotopy retains coordinate supports
and fixes every fiber of an original target vertex. -/
theorem exists_iteratedOrderSubdivision_order_approximation (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : C(|nerve P|,|nerve Q|)) :
    ∃ (n : ℕ) (a : iteratedOrderSubdivision P (n+1) →o Q),
      ∃ H : (f.comp ⟨iteratedOrderSubdivisionHomeomorph P (n+1),
          (iteratedOrderSubdivisionHomeomorph P (n+1)).continuous⟩).Homotopy
        (SSet.toTop.map (nerveMap a.monotone.functor)).hom,
        (∀ (t : I) (x : |nerve (iteratedOrderSubdivision P (n+1))|) (q : Q),
          orderComplexCoordinates Q (f (iteratedOrderSubdivisionHomeomorph P (n+1) x)) q = 0 →
            orderComplexCoordinates Q (H (t,x)) q = 0) ∧
        ∀ (t : I) (x : |nerve (iteratedOrderSubdivision P (n+1))|) (q : Q),
          f (iteratedOrderSubdivisionHomeomorph P (n+1) x) = orderVertex Q q →
            H (t,x) = orderVertex Q q := by
  obtain ⟨n,v,hv⟩ := exists_iteratedOrderSubdivision_star_assignment P Q f
  letI := iteratedOrderSubdivisionFintype P n
  obtain ⟨H,hzero,hvertex⟩ := hv.exists_carrier_homotopy_fixing_vertices
  exact ⟨n,orderCarrierMaximum v hv.preservesOrderChains,H,hzero,hvertex⟩

end KIP126.Topology.SimplicialRealization
