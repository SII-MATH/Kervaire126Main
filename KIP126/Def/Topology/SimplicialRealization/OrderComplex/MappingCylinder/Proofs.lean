module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Homotopy.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Retraction on the source end is exactly the original order map. -/
theorem orderMappingCylinder_retraction_inl (f : P →o Q) :
    (orderMappingCylinderRetraction f).comp (orderMappingCylinderInl f) = f := rfl

/-- Retraction on the target end is exactly the identity. -/
theorem orderMappingCylinder_retraction_inr (f : P →o Q) :
    (orderMappingCylinderRetraction f).comp (orderMappingCylinderInr f) = OrderHom.id := rfl

/-- Every cylinder vertex lies below its retracted target vertex. -/
theorem orderMappingCylinder_le_retract (f : P →o Q) (x : OrderMappingCylinder f) :
    x ≤ orderMappingCylinderInr f (orderMappingCylinderRetraction f x) := by
  cases x <;> exact le_rfl

/-- An injective order map induces an actual simplicial monomorphism. -/
theorem nerveMap_mono_of_injective_orderHom (f : P →o Q) (hf : Function.Injective f) :
    Mono (nerveMap f.monotone.functor) := by
  letI (d : SimplexCategoryᵒᵖ) : Mono ((nerveMap f.monotone.functor).app d) :=
    (CategoryTheory.mono_iff_injective _).mpr (by
      intro s t h
      exact CategoryTheory.Functor.ext (fun k =>
        hf (congrArg (fun z : (nerve Q).obj d => z.obj k) h)))
  exact NatTrans.mono_of_mono_app _

/-- The source end is an actual simplicial subobject. -/
instance orderMappingCylinderSourceInclusion_mono (f : P →o Q) :
    Mono (orderMappingCylinderSourceInclusion f) :=
  nerveMap_mono_of_injective_orderHom (orderMappingCylinderInl f) Sum.inl_injective

/-- The target end is an actual simplicial subobject. -/
instance orderMappingCylinderTargetInclusion_mono (f : P →o Q) :
    Mono (orderMappingCylinderTargetInclusion f) :=
  nerveMap_mono_of_injective_orderHom (orderMappingCylinderInr f) Sum.inr_injective

/-- The actual cylinder nerve is finite when both original orders are finite. -/
instance orderMappingCylinder_nerve_finite (f : P →o Q) [Finite P] [Finite Q] :
    (nerve (OrderMappingCylinder f)).Finite :=
  finite_nerve_of_finite_order (OrderMappingCylinder f)

/-- The simplicial retraction restricts exactly to the given source map. -/
theorem orderMappingCylinder_source_projection (f : P →o Q) :
    orderMappingCylinderSourceInclusion f ≫ orderMappingCylinderProjection f =
      nerveMap f.monotone.functor := rfl

/-- The actual target inclusion is a strict section of the actual projection. -/
theorem orderMappingCylinder_target_projection (f : P →o Q) :
    orderMappingCylinderTargetInclusion f ≫ orderMappingCylinderProjection f =
      𝟙 (nerve Q) := rfl

/-- The actual order mapping-cylinder realization strongly deforms
onto its whole actual target realization. The homotopy fixes the entire
target image, rather than only its vertices. -/
theorem orderMappingCylinder_strongDeformation (f : P →o Q) :
    (ContinuousMap.id |nerve (OrderMappingCylinder f)|).HomotopicRel
      ((SSet.toTop.map (orderMappingCylinderTargetInclusion f)).hom.comp
        (SSet.toTop.map (orderMappingCylinderProjection f)).hom)
      (Set.range (SSet.toTop.map (orderMappingCylinderTargetInclusion f))) := by
  have H := orderMaps_homotopicRel_of_le (OrderHom.id : OrderMappingCylinder f →o _)
    ((orderMappingCylinderInr f).comp (orderMappingCylinderRetraction f))
    (orderMappingCylinder_le_retract f) (orderMappingCylinderInr f) (fun _ => rfl)
  have hs : nerveMap (OrderHom.id : OrderMappingCylinder f →o _).monotone.functor =
      𝟙 (nerve (OrderMappingCylinder f)) := rfl
  have ht : nerveMap ((orderMappingCylinderInr f).comp
      (orderMappingCylinderRetraction f)).monotone.functor =
      orderMappingCylinderProjection f ≫ orderMappingCylinderTargetInclusion f := rfl
  rw [hs,ht,CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_comp] at H
  exact H

end KIP126.Topology.SimplicialRealization
