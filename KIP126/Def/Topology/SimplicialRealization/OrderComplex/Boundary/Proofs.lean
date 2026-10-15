module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Suborder.Subdivision.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Proper chains form an actual simplicial subobject of the subdivision. -/
instance orderBoundaryInclusion_mono (P : Type u) [PartialOrder P] [Fintype P] :
    Mono (orderBoundaryInclusion P) :=
  inferInstanceAs (Mono (orderSuborderInclusion
    (PartialOrder.NonemptyFiniteChains P) (orderProperChains P)))

/-- A subdivided point belongs to the actual proper-chain suborder
exactly when its geometric barycentric projection has a zero coordinate. -/
theorem orderBoundaryInclusion_range_iff (P : Type u) [PartialOrder P] [Fintype P]
    (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) :
    x ∈ Set.range (SSet.toTop.map (orderBoundaryInclusion P)) ↔
      ∃ p, orderSubdivisionCoordinates P x p = 0 := by
  letI := finite_nonemptyFiniteChains P
  letI : Fintype (PartialOrder.NonemptyFiniteChains P) := Fintype.ofFinite _
  change x ∈ Set.range (SSet.toTop.map (orderSuborderInclusion
    (PartialOrder.NonemptyFiniteChains P) (orderProperChains P))) ↔ _
  rw [orderSuborderInclusion_range_iff]
  obtain ⟨d,s,w,hsm,hw,hs⟩ := exists_orderComplex_positive_simplex
    (PartialOrder.NonemptyFiniteChains P) x
  constructor
  · intro hx
    have hproper : (s.obj (Fin.last d)).finset ≠ Finset.univ := by
      intro he
      have hz := hx (s.obj (Fin.last d)) (by
        change ¬ (s.obj (Fin.last d)).finset ≠ Finset.univ
        exact not_ne_iff.mpr he)
      rw [← hs,orderComplexCoordinates_simplex,
        simplex_map_apply_injective _ hsm.injective] at hz
      exact (ne_of_gt (hw (Fin.last d))) hz
    have hex : ∃ p, p ∉ (s.obj (Fin.last d)).finset := by
      by_contra! hn
      exact hproper (Finset.eq_univ_iff_forall.mpr hn)
    obtain ⟨p,hp⟩ := hex
    refine ⟨p,?_⟩
    rw [← hs,orderSubdivisionCoordinates_simplex]
    change Simplex.combinationCoordinates (fun k => orderChainBarycenter P (s.obj k)) w p = 0
    apply Simplex.combinationCoordinates_zero
    intro k
    rw [orderChainBarycenter_apply,if_neg]
    exact fun hk => hp (s.monotone (Fin.le_last k) hk)
  · rintro ⟨p,hp⟩ c hc
    have hfull : c.finset = Finset.univ := by
      change ¬ c.finset ≠ Finset.univ at hc
      exact not_ne_iff.mp hc
    rw [← hs,orderSubdivisionCoordinates_simplex] at hp
    have hz := (Simplex.combinationCoordinates_eq_zero_iff
      (fun k => orderChainBarycenter P (s.obj k)) w p).mp hp
    rw [← hs,orderComplexCoordinates_simplex]
    apply simplex_map_apply_not_range s.obj w c
    rintro ⟨k,hk⟩
    have hzk := (hz k).resolve_left (ne_of_gt (hw k))
    rw [hk,orderChainBarycenter_apply,hfull,if_pos (Finset.mem_univ p)] at hzk
    have hn : 0 < (Finset.univ : Finset P).card :=
      Finset.card_pos.mpr (hfull ▸ c.nonempty)
    exact (ne_of_gt (inv_pos.mpr (Nat.cast_pos.mpr hn))) hzk

/-- The composed actual boundary inclusion has exactly the original
coordinate boundary as its image under the barycentric homeomorphism. -/
theorem orderBoundaryInclusion_geometric_range_iff (P : Type u)
    [PartialOrder P] [Fintype P] (y : |nerve P|) :
    y ∈ Set.range (fun x : |nerve (orderProperChains P)| =>
      orderSubdivisionHomeomorph P (SSet.toTop.map (orderBoundaryInclusion P) x)) ↔
      y ∈ orderCoordinateBoundary P := by
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨p,hp⟩ := (orderBoundaryInclusion_range_iff P
      (SSet.toTop.map (orderBoundaryInclusion P) x)).mp ⟨x,rfl⟩
    refine ⟨p,?_⟩
    rw [orderSubdivisionHomeomorph_coordinates]
    exact hp
  · intro hy
    have hx : (orderSubdivisionHomeomorph P).symm y ∈
        Set.range (SSet.toTop.map (orderBoundaryInclusion P)) := by
      apply (orderBoundaryInclusion_range_iff P _).mpr
      obtain ⟨p,hp⟩ := hy
      refine ⟨p,?_⟩
      rw [← orderSubdivisionHomeomorph_coordinates,Homeomorph.apply_symm_apply]
      exact hp
    obtain ⟨x,hx⟩ := hx
    refine ⟨x,?_⟩
    change orderSubdivisionHomeomorph P (SSet.toTop.map (orderBoundaryInclusion P) x) = y
    rw [hx,Homeomorph.apply_symm_apply]

/-- The actual realization of the proper-chain simplicial subobject
is homeomorphic to the original coordinate boundary, with its
specified geometric inclusion retained. -/
theorem exists_orderBoundary_homeomorph (P : Type u) [PartialOrder P] [Fintype P] :
    ∃ h : |nerve (orderProperChains P)| ≃ₜ orderCoordinateBoundary P,
      ∀ x, (h x).val =
        orderSubdivisionHomeomorph P (SSet.toTop.map (orderBoundaryInclusion P) x) := by
  let g := fun x : |nerve (orderProperChains P)| =>
    orderSubdivisionHomeomorph P (SSet.toTop.map (orderBoundaryInclusion P) x)
  have hg : _root_.Topology.IsEmbedding g :=
    (orderSubdivisionHomeomorph P).isEmbedding.comp
      (realization_mono_isClosedEmbedding (orderBoundaryInclusion P)).toIsEmbedding
  have hr : Set.range g = orderCoordinateBoundary P :=
    Set.ext (orderBoundaryInclusion_geometric_range_iff P)
  exact ⟨hg.toHomeomorph.trans (Homeomorph.setCongr hr),fun _ => rfl⟩

end KIP126.Topology.SimplicialRealization
