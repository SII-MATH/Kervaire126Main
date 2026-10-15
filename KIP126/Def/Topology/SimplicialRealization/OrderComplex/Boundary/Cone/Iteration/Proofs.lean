module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Cone.Extension.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- A finite order has finitely many proper nonempty chains. -/
instance orderProperChains_finite (P : Type u) [PartialOrder P] [Fintype P] :
    Finite (orderProperChains P) := by
  letI := finite_nonemptyFiniteChains P
  infer_instance

/-- A nontrivial order has an actual vertex in its proper-chain boundary. -/
instance orderProperChains_nonempty (P : Type u) [PartialOrder P] [Fintype P] [Nontrivial P] :
    Nonempty (orderProperChains P) := by
  obtain ⟨p,q,hpq⟩ := exists_pair_ne P
  refine ⟨⟨orderSingletonChain p,?_⟩⟩
  intro h
  have hq : q ∈ (orderSingletonChain p).finset := by rw [h]; exact Finset.mem_univ q
  exact hpq (Finset.mem_singleton.mp hq).symm

/-- Repeated subdivision of a nonempty order remains nonempty, with a
vertex supplied by the actual iterated singleton construction. -/
instance iteratedOrderSubdivision_nonempty (P : Type u) [PartialOrder P] [Nonempty P] (n : ℕ) :
    Nonempty (iteratedOrderSubdivision P n) :=
  ⟨iteratedOrderSubdivisionVertex P n (Classical.arbitrary P)⟩

/-- Coning any finite subdivision of the entire proper-chain boundary
produces an actual standard simplex. The boundary is identified by the
actual iterated subdivision homeomorphism, and the cone apex remains
the standard barycenter. -/
theorem exists_iteratedOrderBoundaryCone_stdSimplex_homeomorph (P : Type u)
    [LinearOrder P] [Fintype P] [Nontrivial P] [Fintype (orderProperChains P)] (n : ℕ) :
    ∃ h : |nerve (WithTop (iteratedOrderSubdivision (orderProperChains P) n))| ≃ₜ
        stdSimplex ℝ P,
      (∀ x : |nerve (iteratedOrderSubdivision (orderProperChains P) n)|,
        h (SSet.toTop.map (orderMappingConeSourceTopInclusion
          (iteratedOrderSubdivision (orderProperChains P) n)) x) =
          orderSubdivisionCoordinates P (SSet.toTop.map (orderBoundaryInclusion P)
            (iteratedOrderSubdivisionHomeomorph (orderProperChains P) n x))) ∧
      h (orderVertex _ (⊤ : WithTop (iteratedOrderSubdivision (orderProperChains P) n))) =
        stdSimplex.barycenter := by
  letI := iteratedOrderSubdivisionFintype (orderProperChains P) n
  obtain ⟨e,_,he,heTop⟩ := exists_orderBoundaryCone_stdSimplex_homeomorph P
  obtain ⟨c,_,hc,hcTop⟩ := exists_orderCone_homeomorph
    (iteratedOrderSubdivisionHomeomorph (orderProperChains P) n)
  refine ⟨c.trans e,?_,?_⟩
  · intro x
    change e (c _) = _
    rw [hc]
    exact he _
  · change e (c _) = _
    rw [hcTop,heTop]

end KIP126.Topology.SimplicialRealization
