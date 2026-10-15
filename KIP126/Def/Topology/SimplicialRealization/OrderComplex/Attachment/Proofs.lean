module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Attachment.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- The two actual inclusions agree exactly along the given suborder. -/
theorem orderAttachment_square (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    orderMappingCylinderSourceInclusion f ≫ orderAttachmentCylinderInclusion i hi f =
      nerveMap i.monotone.functor ≫ orderAttachmentPieceInclusion i hi f := rfl

instance orderAttachmentPieceInclusion_mono (i : P ↪o R)
    (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    Mono (orderAttachmentPieceInclusion i hi f) :=
  nerveMap_mono_of_injective_orderHom (orderAttachmentPieceEmbedding i hi f).toOrderHom
    (orderAttachmentPieceEmbedding i hi f).injective

instance orderAttachmentCylinderInclusion_mono (i : P ↪o R)
    (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    Mono (orderAttachmentCylinderInclusion i hi f) :=
  nerveMap_mono_of_injective_orderHom (orderAttachmentCylinderEmbedding i hi f).toOrderHom
    (orderAttachmentCylinderEmbedding i hi f).injective

/-- Every actual simplex of the attachment is entirely in its original
piece or its mapping-cylinder piece. -/
theorem orderAttachment_simplex_cover (i : P ↪o R) (hi : IsLowerSet (Set.range i))
    (f : P →o Q) (d : SimplexCategoryᵒᵖ) (s : (nerve (OrderAttachment i hi f)).obj d) :
    s ∈ Set.range ((orderAttachmentCylinderInclusion i hi f).app d) ∨
      s ∈ Set.range ((orderAttachmentPieceInclusion i hi f).app d) := by
  have hlast (k : Fin (d.unop.len + 1)) :
      s.obj k ≤ s.obj (Fin.last d.unop.len) := s.monotone (Fin.le_last k)
  cases he : s.obj (Fin.last d.unop.len) with
  | inl r =>
      right
      apply (nerveMap_orderEmbedding_range_iff (orderAttachmentPieceEmbedding i hi f) d s).mpr
      intro k
      have hk := hlast k
      rw [he] at hk
      cases hsk : s.obj k with
      | inl r' => exact ⟨r',rfl⟩
      | inr q => rw [hsk] at hk; exact hk.elim
  | inr q =>
      left
      apply (nerveMap_orderEmbedding_range_iff (orderAttachmentCylinderEmbedding i hi f) d s).mpr
      intro k
      have hk := hlast k
      rw [he] at hk
      cases hsk : s.obj k with
      | inl r =>
          rw [hsk] at hk
          obtain ⟨p,hp,_⟩ := hk
          exact ⟨Sum.inl p,congrArg Sum.inl hp⟩
      | inr q' => exact ⟨Sum.inr q',rfl⟩

/-- The two actual pieces intersect precisely in the specified source
suborder, in every simplicial degree. -/
theorem orderAttachment_simplex_intersection (i : P ↪o R) (hi : IsLowerSet (Set.range i))
    (f : P →o Q) (d : SimplexCategoryᵒᵖ)
    (s : (nerve (OrderMappingCylinder f)).obj d) (t : (nerve R).obj d)
    (h : (orderAttachmentCylinderInclusion i hi f).app d s =
      (orderAttachmentPieceInclusion i hi f).app d t) :
    ∃ a : (nerve P).obj d,
      (orderMappingCylinderSourceInclusion f).app d a = s ∧
      (nerveMap i.monotone.functor).app d a = t := by
  let e : P ↪o OrderMappingCylinder f :=
    { toFun := Sum.inl, inj' := Sum.inl_injective, map_rel_iff' := Iff.rfl }
  have hs : s ∈ Set.range ((nerveMap e.monotone.functor).app d) := by
    apply (nerveMap_orderEmbedding_range_iff e d s).mpr
    intro k
    have hk := congrArg (fun z : (nerve (OrderAttachment i hi f)).obj d => z.obj k) h
    change Sum.map i id (s.obj k) = Sum.inl (t.obj k) at hk
    cases ht : s.obj k with
    | inl p => exact ⟨p,rfl⟩
    | inr q => rw [ht] at hk; cases hk
  obtain ⟨a,ha⟩ := hs
  change (orderMappingCylinderSourceInclusion f).app d a = s at ha
  refine ⟨a,ha,?_⟩
  apply (CategoryTheory.mono_iff_injective ((orderAttachmentPieceInclusion i hi f).app d)).mp
    (inferInstance : Mono ((orderAttachmentPieceInclusion i hi f).app d))
  change (orderAttachmentCylinderInclusion i hi f).app d
    ((orderMappingCylinderSourceInclusion f).app d a) = _
  rw [ha]
  exact h

/-- Attachment along a lower induced suborder is an actual simplicial
pushout of the given piece and the attaching-map cylinder. -/
theorem orderAttachment_isPushout (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    IsPushout (orderMappingCylinderSourceInclusion f) (nerveMap i.monotone.functor)
      (orderAttachmentCylinderInclusion i hi f) (orderAttachmentPieceInclusion i hi f) := by
  apply IsPushout.of_forall_isPushout_app
  intro d
  apply Types.isPushout_of_isPullback_of_mono'
  · apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_,?_,orderAttachment_simplex_intersection i hi f d⟩
    · exact congrArg (fun z => z.app d) (orderAttachment_square i hi f)
    · intro x y h
      exact (CategoryTheory.mono_iff_injective
        ((orderMappingCylinderSourceInclusion f).app d)).mp inferInstance h.1
  · apply Set.eq_univ_of_forall
    exact orderAttachment_simplex_cover i hi f d
  · intro x y _ _ h
    exact (CategoryTheory.mono_iff_injective
      ((orderAttachmentPieceInclusion i hi f).app d)).mp inferInstance h

/-- Realization gives the genuine topological attachment pushout. -/
theorem orderAttachment_realization_isPushout (i : P ↪o R)
    (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    IsPushout (SSet.toTop.map (orderMappingCylinderSourceInclusion f))
      (SSet.toTop.map (nerveMap i.monotone.functor))
      (SSet.toTop.map (orderAttachmentCylinderInclusion i hi f))
      (SSet.toTop.map (orderAttachmentPieceInclusion i hi f)) :=
  (orderAttachment_isPushout i hi f).map SSet.toTop

end KIP126.Topology.SimplicialRealization
