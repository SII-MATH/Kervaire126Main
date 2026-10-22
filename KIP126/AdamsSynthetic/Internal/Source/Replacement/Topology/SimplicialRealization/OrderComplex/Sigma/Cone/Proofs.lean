module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Cone.Extension.Empty.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual disjoint cone-base map restricts to each cone's base map. -/
theorem orderSigmaConeEmbedding_inclusion
    {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)] (j : ι) :
    orderSigmaInclusion P j ≫ nerveMap (orderSigmaConeEmbedding P).monotone.functor =
      orderMappingConeSourceTopInclusion (P j) ≫
        orderSigmaInclusion (fun k => WithTop (P k)) j := rfl

/-- Any assembled family of finite-order base homeomorphisms extends to
an actual homeomorphism of the disjoint cones, with a strictly commuting
base square. Empty bases and arbitrary index sets are permitted. -/
theorem exists_orderSigmaCone_homeomorph
    {ι : Type u} (P Q : ι → Type u)
    [∀ j, PartialOrder (P j)] [∀ j, PartialOrder (Q j)]
    [∀ j, Fintype (P j)] [∀ j, Fintype (Q j)]
    (e : ∀ j, |nerve (P j)| ≃ₜ |nerve (Q j)|)
    (E : |nerve (Σ j, P j)| ≃ₜ |nerve (Σ j, Q j)|)
    (hE : ∀ j (x : |nerve (P j)|), E (SSet.toTop.map (orderSigmaInclusion P j) x) =
      SSet.toTop.map (orderSigmaInclusion Q j) (e j x)) :
    ∃ C : |nerve (Σ j, WithTop (P j))| ≃ₜ |nerve (Σ j, WithTop (Q j))|,
      (TopCat.isoOfHomeo E).hom ≫
        SSet.toTop.map (nerveMap (orderSigmaConeEmbedding Q).monotone.functor) =
      SSet.toTop.map (nerveMap (orderSigmaConeEmbedding P).monotone.functor) ≫
        (TopCat.isoOfHomeo C).hom := by
  classical
  have h (j : ι) := exists_orderCone_homeomorph_of_homeomorph (e j)
  choose c hc using h
  obtain ⟨C,hC⟩ := exists_orderSigmaRealization_homeomorph_of_family
    (fun j => WithTop (P j)) (fun j => WithTop (Q j)) c
  refine ⟨C,?_⟩
  apply (orderSigmaRealizationCofan_isColimit P).hom_ext
  rintro ⟨j⟩
  ext x
  change SSet.toTop.map (nerveMap (orderSigmaConeEmbedding Q).monotone.functor)
    (E (SSet.toTop.map (orderSigmaInclusion P j) x)) =
    C (SSet.toTop.map (nerveMap (orderSigmaConeEmbedding P).monotone.functor)
      (SSet.toTop.map (orderSigmaInclusion P j) x))
  rw [hE]
  have hb (R : ι → Type u) [∀ j, PartialOrder (R j)] (x : |nerve (R j)|) :
      SSet.toTop.map (nerveMap (orderSigmaConeEmbedding R).monotone.functor)
        (SSet.toTop.map (orderSigmaInclusion R j) x) =
      SSet.toTop.map (orderSigmaInclusion (fun k => WithTop (R k)) j)
        (SSet.toTop.map (orderMappingConeSourceTopInclusion (R j)) x) := by
    simpa only [CategoryTheory.Functor.map_comp,TopCat.comp_app] using
      ConcreteCategory.congr_hom
        (congrArg SSet.toTop.map (orderSigmaConeEmbedding_inclusion R j)) x
  rw [hb Q,hb P,hC,hc]

end KIP126.Topology.SimplicialRealization
