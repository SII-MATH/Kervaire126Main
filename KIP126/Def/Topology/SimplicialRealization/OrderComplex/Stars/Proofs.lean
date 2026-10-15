module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Stars.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Proofs
public import KIP126.Def.Topology.Simplex.Homotopy.Proofs
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every actual vertex star is open. -/
theorem isOpen_orderOpenStar (P : Type u) [PartialOrder P] [Fintype P] (p : P) :
    IsOpen (orderOpenStar P p) :=
  isOpen_lt continuous_const
    ((continuous_apply p).comp (orderComplexCoordinates P).continuous.subtype_val)

/-- The actual vertex stars cover the realization. -/
theorem exists_mem_orderOpenStar (P : Type u) [PartialOrder P] [Fintype P]
    (x : |nerve P|) : ∃ p, x ∈ orderOpenStar P p := by
  by_contra h
  have hz (p : P) : orderComplexCoordinates P x p = 0 := by
    apply le_antisymm _ ((orderComplexCoordinates P x).property.1 p)
    exact le_of_not_gt (fun hp => h ⟨p,hp⟩)
  have hsum := stdSimplex.sum_eq_one (orderComplexCoordinates P x)
  simp only [hz, Finset.sum_const_zero] at hsum
  norm_num at hsum

/-- The union of all actual vertex stars is the whole realization. -/
theorem iUnion_orderOpenStar (P : Type u) [PartialOrder P] [Fintype P] :
    (⋃ p, orderOpenStar P p) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_orderOpenStar P x

/-- Finitely many actual vertex stars have open intersection. -/
theorem isOpen_orderOpenStarIntersection (P : Type u) [PartialOrder P] [Fintype P]
    (s : Finset P) : IsOpen (orderOpenStarIntersection P s) := by
  convert isOpen_biInter_finset (fun p (_ : p ∈ s) => isOpen_orderOpenStar P p) using 1
  ext x
  simp [orderOpenStarIntersection]

/-- Any vertices whose actual stars meet are comparable in the original order. -/
theorem orderOpenStarIntersection_nonempty_comparable (P : Type u)
    [PartialOrder P] [Fintype P] (s : Finset P)
    (h : (orderOpenStarIntersection P s).Nonempty) :
    ∀ p ∈ s, ∀ q ∈ s, p ≤ q ∨ q ≤ p := by
  obtain ⟨x,hx⟩ := h
  intro p hp q hq
  exact orderComplexCoordinates_hasChainSupport P x p q (hx p hp) (hx q hq)

/-- Coordinates of an actual vertex are the corresponding simplex vertex. -/
theorem orderComplexCoordinates_vertex (P : Type u) [PartialOrder P] [Fintype P]
    (p : P) : orderComplexCoordinates P (orderVertex P p) = stdSimplex.vertex p := by
  classical
  rw [orderVertex, orderComplexCoordinates_simplex, stdSimplex.map_vertex]
  rfl

/-- Each actual vertex belongs to its own open star. -/
theorem orderVertex_mem_orderOpenStar (P : Type u) [PartialOrder P] [Fintype P]
    (p : P) : orderVertex P p ∈ orderOpenStar P p := by
  classical
  change 0 < orderComplexCoordinates P (orderVertex P p) p
  rw [orderComplexCoordinates_vertex]
  simp [stdSimplex.vertex]

/-- The barycenter of a genuine chain has support in that same chain. -/
theorem orderChainBarycenter_hasChainSupport (P : Type u) [PartialOrder P] [Fintype P]
    (c : PartialOrder.NonemptyFiniteChains P) : HasChainSupport (orderChainBarycenter P c) := by
  classical
  intro p q hp hq
  have hm (r : P) (hr : 0 < orderChainBarycenter P c r) : r ∈ c.finset := by
    by_contra hn
    rw [orderChainBarycenter_apply, if_neg hn] at hr
    exact (lt_irrefl 0) hr
  exact c.comparable ⟨p,hm p hp⟩ ⟨q,hm q hq⟩

/-- A nonempty chain's uniform barycenter is an actual point of its
common open star. -/
theorem exists_orderOpenStarIntersection_barycenter (P : Type u)
    [PartialOrder P] [Fintype P] (c : PartialOrder.NonemptyFiniteChains P) :
    ∃ b : orderOpenStarIntersection P c.finset,
      orderComplexCoordinates P b.val = orderChainBarycenter P c := by
  classical
  obtain ⟨b,hb⟩ := orderComplexCoordinates_preimage P (orderChainBarycenter P c)
    (orderChainBarycenter_hasChainSupport P c)
  refine ⟨⟨b,?_⟩,hb⟩
  intro p hp
  change 0 < orderComplexCoordinates P b p
  rw [hb,orderChainBarycenter_apply,if_pos hp]
  exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr c.nonempty))

end KIP126.Topology.SimplicialRealization
