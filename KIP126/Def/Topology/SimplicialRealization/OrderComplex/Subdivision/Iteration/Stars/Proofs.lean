module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Mesh.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Stars.Proofs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every point in an actual open star lies in a characteristic simplex
that contains its distinguished vertex. -/
theorem exists_orderOpenStar_simplex_vertex (P : Type u) [PartialOrder P] [Fintype P]
    (p : P) (x : |nerve P|) (hx : x ∈ orderOpenStar P p) :
    ∃ (d : ℕ) (s : (nerve P).obj (op ⦋d⦌)) (w : stdSimplex ℝ (Fin (d+1)))
      (i : Fin (d+1)), simplexPoint _ s w = x ∧
        simplexPoint _ s (stdSimplex.vertex i) = orderVertex P p := by
  obtain ⟨d,s,w,_,_,hs⟩ := exists_orderComplex_positive_simplex P x
  have hp : 0 < stdSimplex.map s.obj w p := by
    change 0 < orderComplexCoordinates P x p at hx
    simpa only [← hs,orderComplexCoordinates_simplex] using hx
  have hm : p ∈ Set.range s.obj := by
    by_contra h
    exact (ne_of_gt hp) (simplex_map_apply_not_range s.obj w p h)
  obtain ⟨i,hi⟩ := hm
  refine ⟨d,s,w,i,hs,orderComplexCoordinates_injective P ?_⟩
  rw [orderComplexCoordinates_simplex,stdSimplex.map_vertex,hi,
    orderComplexCoordinates_vertex]

/-- After enough actual subdivisions, every open star stays within the
given coordinate distance of the image of its vertex. -/
theorem exists_iteratedOrderSubdivision_star_small (P : Type u)
    [PartialOrder P] [Fintype P] (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, letI := iteratedOrderSubdivisionFintype P n
      ∀ (p : iteratedOrderSubdivision P n) (x : |nerve (iteratedOrderSubdivision P n)|),
        x ∈ orderOpenStar _ p →
        dist (orderComplexCoordinates P (iteratedOrderSubdivisionHomeomorph P n x))
          (orderComplexCoordinates P (iteratedOrderSubdivisionHomeomorph P n
            (orderVertex _ p))) < ε := by
  obtain ⟨n,hn⟩ := exists_iteratedOrderSubdivision_coordinates_small P ε hε
  refine ⟨n,?_⟩
  letI := iteratedOrderSubdivisionFintype P n
  intro p x hx
  obtain ⟨d,s,w,i,hs,hi⟩ := exists_orderOpenStar_simplex_vertex _ p x hx
  simpa only [hs,hi] using hn d s w (stdSimplex.vertex i)

/-- Actual iterated subdivision stars refine every open cover of a
finite order-complex realization. -/
theorem exists_iteratedOrderSubdivision_star_refinement (P : Type u)
    [PartialOrder P] [Fintype P] {ι : Sort*} (U : ι → Set |nerve P|)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) :
    ∃ n : ℕ, letI := iteratedOrderSubdivisionFintype P n
      ∀ p : iteratedOrderSubdivision P n, ∃ i,
        ∀ x ∈ orderOpenStar _ p, iteratedOrderSubdivisionHomeomorph P n x ∈ U i := by
  obtain ⟨b,hb⟩ := exists_orderComplexCoordinates_homeomorph P
  letI := finite_nerve_of_finite_order P
  letI := compactSpace_of_finite (nerve P)
  letI := b.compactSpace
  let V (i : ι) : Set {y : stdSimplex ℝ P // HasChainSupport y} := b.symm ⁻¹' U i
  have hV (i : ι) : IsOpen (V i) := (hU i).preimage b.symm.continuous
  have hVc : Set.univ ⊆ ⋃ i, V i := by
    intro y _
    have hy : b.symm y ∈ ⋃ i, U i := by rw [hcover]; trivial
    simpa only [Set.mem_iUnion,V,Set.mem_preimage] using hy
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hVc
  obtain ⟨n,hn⟩ := exists_iteratedOrderSubdivision_star_small P δ hδ
  refine ⟨n,?_⟩
  letI := iteratedOrderSubdivisionFintype P n
  intro p
  obtain ⟨i,hi⟩ := hball (b (iteratedOrderSubdivisionHomeomorph P n (orderVertex _ p)))
    (Set.mem_univ _)
  refine ⟨i,?_⟩
  intro x hx
  have hd : b (iteratedOrderSubdivisionHomeomorph P n x) ∈
      Metric.ball (b (iteratedOrderSubdivisionHomeomorph P n (orderVertex _ p))) δ := by
    change dist _ _ < δ
    simpa only [Subtype.dist_eq,hb] using hn p x hx
  have hm := hi hd
  simpa only [V,Set.mem_preimage,Homeomorph.symm_apply_apply] using hm

end KIP126.Topology.SimplicialRealization
