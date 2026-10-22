module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Subdivision.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Uniform chain barycenters commute with injective order maps, whose
actual finite images retain the original chain cardinalities. -/
theorem orderChainBarycenter_map_injective {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    [Fintype P] [Fintype Q] (f : P →o Q) (hf : Function.Injective f)
    (c : PartialOrder.NonemptyFiniteChains P) :
    stdSimplex.map f (orderChainBarycenter P c) = orderChainBarycenter Q (c.map f) := by
  apply stdSimplex.ext
  funext q
  have hcard : (c.map f).finset.card = c.finset.card := Finset.card_image_of_injective _ hf
  by_cases hq : q ∈ Set.range f
  · obtain ⟨p,rfl⟩ := hq
    rw [simplex_map_apply_injective _ hf,orderChainBarycenter_apply,
      orderChainBarycenter_apply,hcard]
    have hm : f p ∈ (c.map f).finset ↔ p ∈ c.finset := by
      rw [PartialOrder.NonemptyFiniteChains.mem_map_iff]
      constructor
      · rintro ⟨r,hr,he⟩
        simpa only [hf he] using hr
      · exact fun hp => ⟨p,hp,rfl⟩
    simp only [hm]
  · rw [simplex_map_apply_not_range _ _ q hq,orderChainBarycenter_apply,if_neg]
    intro hmem
    obtain ⟨p,_,he⟩ := (PartialOrder.NonemptyFiniteChains.mem_map_iff c f q).mp hmem
    exact hq ⟨p,he⟩

/-- Actual barycentric subdivision coordinates commute with injective
order maps on the realized nerves of their chains. -/
theorem orderSubdivisionCoordinates_natural_injective {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (hf : Function.Injective f)
    (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
    orderSubdivisionCoordinates Q
      (SSet.toTop.map (nerveMap
        (PartialOrder.NonemptyFiniteChains.orderHomMap f).monotone.functor) x) =
      stdSimplex.map f (orderSubdivisionCoordinates P x) := by
  obtain ⟨d,s,w,_,_,hs⟩ := exists_orderComplex_positive_simplex
    (PartialOrder.NonemptyFiniteChains P) x
  rw [← hs,simplexPoint_map,orderSubdivisionCoordinates_simplex,
    orderSubdivisionCoordinates_simplex]
  apply stdSimplex.ext
  change Simplex.combinationCoordinates
      (fun k => orderChainBarycenter Q ((s.obj k).map f)) w =
    FunOnFinite.linearMap ℝ ℝ f
      (Simplex.combinationCoordinates (fun k => orderChainBarycenter P (s.obj k)) w)
  rw [Simplex.combinationCoordinates_map_target]
  simp only [orderChainBarycenter_map_injective f hf]

/-- The actual one-step barycentric homeomorphisms commute with an
injective order map and its actual map on nonempty finite chains. -/
theorem orderSubdivisionHomeomorph_natural_injective {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (hf : Function.Injective f)
    (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
    orderSubdivisionHomeomorph Q
      (SSet.toTop.map (nerveMap
        (PartialOrder.NonemptyFiniteChains.orderHomMap f).monotone.functor) x) =
      SSet.toTop.map (nerveMap f.monotone.functor) (orderSubdivisionHomeomorph P x) := by
  apply orderComplexCoordinates_injective Q
  rw [orderSubdivisionHomeomorph_coordinates,orderComplexCoordinates_natural,
    orderSubdivisionHomeomorph_coordinates,orderSubdivisionCoordinates_natural_injective f hf]

/-- The actual barycentric homeomorphism carries the realized
subdivided suborder precisely onto the original suborder realization. -/
theorem orderSuborderSubdivisionInclusion_range_iff (P : Type u)
    [PartialOrder P] [Fintype P] (S : Set P)
    (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
    x ∈ Set.range (SSet.toTop.map (orderSuborderSubdivisionInclusion P S)) ↔
      orderSubdivisionHomeomorph P x ∈
        Set.range (SSet.toTop.map (orderSuborderInclusion P S)) := by
  letI : Fintype S := Fintype.ofFinite S
  have hn (y : |nerve (PartialOrder.NonemptyFiniteChains S)|) :
      orderSubdivisionHomeomorph P
        (SSet.toTop.map (orderSuborderSubdivisionInclusion P S) y) =
      SSet.toTop.map (orderSuborderInclusion P S) (orderSubdivisionHomeomorph S y) :=
    orderSubdivisionHomeomorph_natural_injective
      (OrderHom.Subtype.val (· ∈ S)) Subtype.val_injective y
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨orderSubdivisionHomeomorph S y,(hn y).symm⟩
  · rintro ⟨y,hy⟩
    refine ⟨(orderSubdivisionHomeomorph S).symm y,?_⟩
    apply (orderSubdivisionHomeomorph P).injective
    rw [hn,Homeomorph.apply_symm_apply,hy]

end KIP126.Topology.SimplicialRealization
