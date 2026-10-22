module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Attachment.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.HomotopySquare.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Equivalence.OrderMappingCylinder.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual continuous attachment along a lower induced suborder has
the homotopy type of the explicit attachment order whenever its boundary
map is homotopic to an actual order map. Both directions retain the old
target realization exactly. Arbitrary index sets and target orders are
allowed. -/
theorem exists_orderAttachment_homotopyEquiv
    {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q)
    (a : SSet.toTop.obj (nerve P) ⟶ SSet.toTop.obj (nerve Q))
    {T : TopCat.{u}} (u : SSet.toTop.obj (nerve Q) ⟶ T)
    (v : SSet.toTop.obj (nerve R) ⟶ T)
    (hp : IsPushout a (SSet.toTop.map (nerveMap i.monotone.functor)) u v)
    (Ha : a.hom.Homotopic (SSet.toTop.map (nerveMap f.monotone.functor)).hom) :
    ∃ E : ContinuousMap.HomotopyEquiv |nerve (OrderAttachment i hi f)| T,
      (∀ y : |nerve Q|, E (SSet.toTop.map
        (orderMappingCylinderTargetInclusion f ≫ orderAttachmentCylinderInclusion i hi f) y) = u y) ∧
      ∀ y : |nerve Q|, E.invFun (u y) = SSet.toTop.map
        (orderMappingCylinderTargetInclusion f ≫ orderAttachmentCylinderInclusion i hi f) y := by
  let c := SSet.toTop.map (orderAttachmentCylinderInclusion i hi f)
  let q := SSet.toTop.map (orderMappingCylinderProjection f)
  let r := SSet.toTop.map (orderMappingCylinderTargetInclusion f)
  let b := SSet.toTop.map (orderMappingCylinderSourceInclusion f)
  obtain ⟨H,_⟩ := exists_orderMappingCylinder_fiber_deformation f
  have hr : r ≫ q = 𝟙 _ := by
    dsimp only [r,q]
    rw [← CategoryTheory.Functor.map_comp,orderMappingCylinder_target_projection,
      CategoryTheory.Functor.map_id]
  let e : ContinuousMap.HomotopyEquiv |nerve (OrderMappingCylinder f)| |nerve Q| := {
    toFun := q.hom
    invFun := r.hom
    left_inv := ⟨H.symm⟩
    right_inv := by
      have he : q.hom.comp r.hom = ContinuousMap.id _ := congrArg TopCat.Hom.hom hr
      rw [he] }
  have hb : e.toFun.comp b.hom = (SSet.toTop.map (nerveMap f.monotone.functor)).hom := by
    change (b ≫ q).hom = _
    dsimp only [b,q]
    rw [← Functor.map_comp,orderMappingCylinder_source_projection]
  obtain ⟨Ha⟩ := Ha.symm
  letI : Mono (nerveMap i.monotone.functor) := nerveMap_mono_of_injective_orderHom i.toOrderHom i.injective
  obtain ⟨E,hE,hEinv⟩ := exists_homotopyEquiv_of_cofibration_pushout_homotopy_square
    (orderAttachment_realization_isPushout i hi f) hp
    (realization_mono_hasHomotopyExtension (nerveMap i.monotone.functor))
    e (Ha.cast hb.symm rfl)
  refine ⟨E,?_,?_⟩
  · intro y
    rw [Functor.map_comp,TopCat.comp_app]
    change E (c (r y)) = u y
    exact (hE (r y)).trans (congrArg u (ConcreteCategory.congr_hom hr y))
  · intro y
    rw [Functor.map_comp,TopCat.comp_app]
    exact hEinv y

end KIP126.Topology.SimplicialRealization
