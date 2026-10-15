module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.LastVertex.Map.Data
public import KIP126.Def.Topology.Simplex.Homotopy.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual last-vertex map sends each flag's weights to its chain maxima. -/
theorem orderSubdivisionLastVertex_simplex (P : Type u) [PartialOrder P] [Fintype P]
    {d : ℕ} (s : (nerve (PartialOrder.NonemptyFiniteChains P)).obj (op ⦋d⦌))
    (w : stdSimplex ℝ (Fin (d+1))) :
    orderComplexCoordinates P
      (SSet.toTop.map (orderSubdivisionLastVertex P) (simplexPoint _ s w)) =
      stdSimplex.map (fun k => orderChainMaximum (s.obj k)) w := by
  rw [simplexPoint_map,orderComplexCoordinates_simplex]
  rfl

/-- Last-vertex realization has support contained in the geometric
barycentric support, with no extra face-preservation assumption. -/
theorem orderSubdivisionCoordinates_zero_lastVertex (P : Type u)
    [PartialOrder P] [Fintype P] (x : |nerve (PartialOrder.NonemptyFiniteChains P)|)
    (p : P) (hx : orderSubdivisionCoordinates P x p = 0) :
    orderComplexCoordinates P (SSet.toTop.map (orderSubdivisionLastVertex P) x) p = 0 := by
  classical
  obtain ⟨d,s,w,_,hw,hs⟩ := exists_orderComplex_positive_simplex
    (PartialOrder.NonemptyFiniteChains P) x
  rw [← hs,orderSubdivisionCoordinates_simplex] at hx
  change Simplex.combinationCoordinates (fun k => orderChainBarycenter P (s.obj k)) w p = 0 at hx
  have hz := (Simplex.combinationCoordinates_eq_zero_iff _ w p).mp hx
  have hn (k : Fin (d+1)) : p ∉ (s.obj k).finset := by
    have hzk := (hz k).resolve_left (ne_of_gt (hw k))
    rw [orderChainBarycenter_apply] at hzk
    intro hp
    rw [if_pos hp] at hzk
    exact (ne_of_gt (inv_pos.mpr (Nat.cast_pos.mpr
      (Finset.card_pos.mpr (s.obj k).nonempty)))) hzk
  rw [← hs,orderSubdivisionLastVertex_simplex]
  apply simplex_map_apply_not_range
  rintro ⟨k,hk⟩
  exact hn k (hk ▸ orderChainMaximum_mem (s.obj k))

/-- Geometric subdivision and actual last-vertex coordinates have a
continuous homotopy within the geometric order complex, preserving
every zero coordinate of the geometric subdivision throughout. -/
theorem exists_orderSubdivisionCoordinates_homotopy (P : Type u)
    [PartialOrder P] [Fintype P] :
    ∃ H : (orderSubdivisionCoordinates P).Homotopy
      ((orderComplexCoordinates P).comp (SSet.toTop.map (orderSubdivisionLastVertex P)).hom),
      (∀ (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|), HasChainSupport (H (t,x))) ∧
      (∀ (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (p : P),
        orderSubdivisionCoordinates P x p = 0 → H (t,x) p = 0) := by
  obtain ⟨H,hH⟩ := Simplex.exists_affine_homotopy
    (orderSubdivisionCoordinates P)
    ((orderComplexCoordinates P).comp (SSet.toTop.map (orderSubdivisionLastVertex P)).hom)
  have hz (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (p : P)
      (hx : orderSubdivisionCoordinates P x p = 0) : H (t,x) p = 0 := by
    rw [hH,hx]
    change (1 - (t : ℝ)) * 0 + (t : ℝ) *
      orderComplexCoordinates P (SSet.toTop.map (orderSubdivisionLastVertex P) x) p = 0
    rw [orderSubdivisionCoordinates_zero_lastVertex P x p hx]
    simp
  refine ⟨H,?_,hz⟩
  intro t x p q hp hq
  apply orderSubdivisionCoordinates_hasChainSupport P x p q
  · exact lt_of_le_of_ne ((orderSubdivisionCoordinates P x).property.1 p)
      (fun h => (ne_of_gt hp) (hz t x p h.symm))
  · exact lt_of_le_of_ne ((orderSubdivisionCoordinates P x).property.1 q)
      (fun h => (ne_of_gt hq) (hz t x q h.symm))

end KIP126.Topology.SimplicialRealization
