module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Carrier.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]

/-- A realized carrier map has support contained in the image under
the original map of the actual geometric subdivision point. -/
theorem IsOrderStarAssignment.carrier_zero
    {f : C(|nerve P|,|nerve Q|)} {v : P → Q} (h : IsOrderStarAssignment f v)
    (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (q : Q)
    (hx : orderComplexCoordinates Q (f (orderSubdivisionHomeomorph P x)) q = 0) :
    orderComplexCoordinates Q
      (SSet.toTop.map (orderCarrierSimplicialMap v h.preservesOrderChains) x) q = 0 := by
  obtain ⟨d,s,w,_,hw,hs⟩ := exists_orderComplex_positive_simplex
    (PartialOrder.NonemptyFiniteChains P) x
  have hn (k : Fin (d+1)) : orderCarrierMaximum v h.preservesOrderChains (s.obj k) ≠ q := by
    obtain ⟨p,hp,he⟩ := orderCarrierMaximum_mem v h.preservesOrderChains (s.obj k)
    have hpos : 0 < orderComplexCoordinates P (orderSubdivisionHomeomorph P x) p := by
      rw [orderSubdivisionHomeomorph_coordinates,← hs,orderSubdivisionCoordinates_simplex]
      change 0 < ∑ i, w i * orderChainBarycenter P (s.obj i) p
      have hk : 0 < w k * orderChainBarycenter P (s.obj k) p := by
        rw [orderChainBarycenter_apply,if_pos hp]
        exact mul_pos (hw k) (inv_pos.mpr (Nat.cast_pos.mpr
          (Finset.card_pos.mpr (s.obj k).nonempty)))
      exact hk.trans_le (Finset.single_le_sum (fun i _ =>
        mul_nonneg (w.property.1 i) ((orderChainBarycenter P (s.obj i)).property.1 p))
          (Finset.mem_univ k))
    have himage : 0 < orderComplexCoordinates Q (f (orderSubdivisionHomeomorph P x)) (v p) :=
      h p hpos
    intro heq
    rw [he,heq,hx] at himage
    exact (lt_irrefl 0) himage
  rw [← hs,orderCarrierSimplicialMap_coordinates]
  exact simplex_map_apply_not_range _ w q (by rintro ⟨k,hk⟩; exact hn k hk)

/-- The actual carrier realization is homotopic to the given map after
the actual barycentric homeomorphism. Every zero coordinate of the
given map is retained throughout the homotopy. -/
theorem IsOrderStarAssignment.exists_carrier_homotopy
    {f : C(|nerve P|,|nerve Q|)} {v : P → Q} (h : IsOrderStarAssignment f v) :
    ∃ H : (f.comp ⟨orderSubdivisionHomeomorph P,
        (orderSubdivisionHomeomorph P).continuous⟩).Homotopy
      (SSet.toTop.map (orderCarrierSimplicialMap v h.preservesOrderChains)).hom,
      ∀ (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (q : Q),
        orderComplexCoordinates Q (f (orderSubdivisionHomeomorph P x)) q = 0 →
          orderComplexCoordinates Q (H (t,x)) q = 0 := by
  let a : C(|nerve (PartialOrder.NonemptyFiniteChains P)|,|nerve Q|) :=
    f.comp ⟨orderSubdivisionHomeomorph P,(orderSubdivisionHomeomorph P).continuous⟩
  let b := (SSet.toTop.map (orderCarrierSimplicialMap v h.preservesOrderChains)).hom
  obtain ⟨G,hG⟩ := Simplex.exists_affine_homotopy
    ((orderComplexCoordinates Q).comp a) ((orderComplexCoordinates Q).comp b)
  have hzero (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (q : Q)
      (hx : orderComplexCoordinates Q (a x) q = 0) : G (t,x) q = 0 := by
    rw [hG]
    change (1 - (t : ℝ)) * orderComplexCoordinates Q (a x) q +
      (t : ℝ) * orderComplexCoordinates Q (b x) q = 0
    rw [hx,h.carrier_zero x q hx]
    simp
  have hchain (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
      HasChainSupport (G (t,x)) := by
    intro p q hp hq
    apply orderComplexCoordinates_hasChainSupport Q (a x) p q
    · exact lt_of_le_of_ne ((orderComplexCoordinates Q (a x)).property.1 p)
        (fun he => (ne_of_gt hp) (hzero t x p he.symm))
    · exact lt_of_le_of_ne ((orderComplexCoordinates Q (a x)).property.1 q)
        (fun he => (ne_of_gt hq) (hzero t x q he.symm))
  obtain ⟨e,he⟩ := exists_orderComplexCoordinates_homeomorph Q
  have hei (y : {y : stdSimplex ℝ Q // HasChainSupport y}) :
      orderComplexCoordinates Q (e.symm y) = y.val := by
    have hh := he (e.symm y)
    rw [e.apply_symm_apply] at hh
    exact hh.symm
  let H : a.Homotopy b := {
    toFun := fun z => e.symm ⟨G z,hchain z.1 z.2⟩
    continuous_toFun := e.symm.continuous.comp (G.continuous.subtype_mk _)
    map_zero_left := by
      intro x
      apply orderComplexCoordinates_injective Q
      rw [hei]
      exact G.apply_zero x
    map_one_left := by
      intro x
      apply orderComplexCoordinates_injective Q
      rw [hei]
      exact G.apply_one x }
  refine ⟨H,?_⟩
  intro t x q hx
  change orderComplexCoordinates Q (e.symm ⟨G (t,x),hchain t x⟩) q = 0
  rw [hei]
  exact hzero t x q hx

/-- An actual order-complex point supported at one vertex is that
actual vertex, since its remaining coordinate has total mass one. -/
theorem eq_orderVertex_of_zero_coordinates (Q : Type u) [PartialOrder Q] [Fintype Q]
    (x : |nerve Q|) (q : Q)
    (h : ∀ r, r ≠ q → orderComplexCoordinates Q x r = 0) : x = orderVertex Q q := by
  apply orderComplexCoordinates_injective Q
  rw [orderComplexCoordinates_vertex]
  apply stdSimplex.ext
  funext r
  by_cases hr : r = q
  · subst r
    have hsum : (∑ r, orderComplexCoordinates Q x r) = orderComplexCoordinates Q x q := by
      apply Finset.sum_eq_single q
      · intro r _ hr
        exact h r hr
      · simp
    have hq : orderComplexCoordinates Q x q = 1 :=
      hsum.symm.trans (stdSimplex.sum_eq_one (orderComplexCoordinates Q x))
    simpa [stdSimplex.vertex] using hq
  · simpa [stdSimplex.vertex,hr] using h r hr

/-- The actual carrier homotopy fixes every point where the original
map takes a vertex value; the same homotopy works simultaneously for
all such vertex fibers and retains all original zero coordinates. -/
theorem IsOrderStarAssignment.exists_carrier_homotopy_fixing_vertices
    {f : C(|nerve P|,|nerve Q|)} {v : P → Q} (h : IsOrderStarAssignment f v) :
    ∃ H : (f.comp ⟨orderSubdivisionHomeomorph P,
        (orderSubdivisionHomeomorph P).continuous⟩).Homotopy
      (SSet.toTop.map (orderCarrierSimplicialMap v h.preservesOrderChains)).hom,
      (∀ (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (q : Q),
        orderComplexCoordinates Q (f (orderSubdivisionHomeomorph P x)) q = 0 →
          orderComplexCoordinates Q (H (t,x)) q = 0) ∧
      ∀ (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (q : Q),
        f (orderSubdivisionHomeomorph P x) = orderVertex Q q → H (t,x) = orderVertex Q q := by
  obtain ⟨H,hzero⟩ := h.exists_carrier_homotopy
  refine ⟨H,hzero,?_⟩
  intro t x q hx
  apply eq_orderVertex_of_zero_coordinates Q (H (t,x)) q
  intro r hr
  apply hzero t x r
  rw [hx,orderComplexCoordinates_vertex]
  simp [stdSimplex.vertex,hr,Ne.symm hr]

/-- The actual carrier comparison is relative to any region on which
the original map takes vertex values, with no extra homotopy assumption. -/
theorem IsOrderStarAssignment.carrier_homotopicRel
    {f : C(|nerve P|,|nerve Q|)} {v : P → Q} (h : IsOrderStarAssignment f v)
    (B : Set |nerve (PartialOrder.NonemptyFiniteChains P)|)
    (hB : ∀ x ∈ B, ∃ q, f (orderSubdivisionHomeomorph P x) = orderVertex Q q) :
    (f.comp ⟨orderSubdivisionHomeomorph P,
        (orderSubdivisionHomeomorph P).continuous⟩).HomotopicRel
      (SSet.toTop.map (orderCarrierSimplicialMap v h.preservesOrderChains)).hom B := by
  obtain ⟨H,_,hfix⟩ := h.exists_carrier_homotopy_fixing_vertices
  refine ⟨{ toHomotopy := H, prop' := ?_ }⟩
  intro t x hx
  obtain ⟨q,hq⟩ := hB x hx
  exact (hfix t x q hq).trans hq.symm

end KIP126.Topology.SimplicialRealization
