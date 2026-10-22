module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Extension.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homeomorphisms of finite order realizations extend over their cones,
including empty bases, and agree exactly on the realized base inclusion. -/
theorem exists_orderCone_homeomorph_of_homeomorph
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (h : |nerve P| ≃ₜ |nerve Q|) :
    ∃ e : |nerve (WithTop P)| ≃ₜ |nerve (WithTop Q)|,
      ∀ x : |nerve P|,
        e (SSet.toTop.map (orderMappingConeSourceTopInclusion P) x) =
          SSet.toTop.map (orderMappingConeSourceTopInclusion Q) (h x) := by
  classical
  have hempty (R : Type u) [PartialOrder R] [Fintype R] [IsEmpty R] :
      IsEmpty |nerve R| := by
    refine ⟨fun x => ?_⟩
    have hx := (orderComplexCoordinates R x).property.2
    simp at hx
  cases isEmpty_or_nonempty P with
  | inl hP =>
    letI := hP
    letI := hempty P
    letI : IsEmpty Q := ⟨fun q => isEmptyElim (h.symm (orderVertex Q q))⟩
    let o := (OrderIso.ofIsEmpty P Q).withTopCongr
    let e : nerve (WithTop P) ≅ nerve (WithTop Q) := PartOrd.nerveFunctor.mapIso {
      hom := PartOrd.ofHom ⟨o,o.monotone⟩
      inv := PartOrd.ofHom ⟨o.symm,o.symm.monotone⟩
      hom_inv_id := by apply PartOrd.ext; intro p; exact o.symm_apply_apply p
      inv_hom_id := by apply PartOrd.ext; intro q; exact o.apply_symm_apply q }
    exact ⟨TopCat.homeoOfIso (SSet.toTop.mapIso e),fun x => isEmptyElim x⟩
  | inr hP =>
    letI := hP
    have hQ : Nonempty Q := by
      by_contra hn
      letI : IsEmpty Q := not_nonempty_iff.mp hn
      letI := hempty Q
      exact isEmptyElim (h (orderVertex P (Classical.arbitrary P)))
    letI := hQ
    obtain ⟨e,_,he,_⟩ := exists_orderCone_homeomorph h
    exact ⟨e,he⟩

end KIP126.Topology.SimplicialRealization
