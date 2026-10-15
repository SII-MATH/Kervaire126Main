module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Proofs
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A simplex belongs to an induced suborder exactly when all its vertices do. -/
theorem nerveMap_orderEmbedding_range_iff (e : P ↪o Q) (d : SimplexCategoryᵒᵖ)
    (s : (nerve Q).obj d) :
    s ∈ Set.range ((nerveMap e.monotone.functor).app d) ↔
      ∀ k, s.obj k ∈ Set.range e := by
  classical
  constructor
  · rintro ⟨t, rfl⟩ k
    exact ⟨t.obj k, rfl⟩
  · intro h
    let t : Fin (d.unop.len + 1) →o P :=
      { toFun := fun k => (h k).choose
        monotone' := by
          intro i j hij
          apply e.le_iff_le.mp
          change e ((h i).choose) ≤ e ((h j).choose)
          rw [(h i).choose_spec, (h j).choose_spec]
          exact s.monotone hij }
    refine ⟨t.monotone.functor, CategoryTheory.Functor.ext (fun k => ?_)⟩
    exact (h k).choose_spec

/-- The two inclusions agree exactly on the original source. -/
theorem orderMappingCone_square (f : P →o Q) :
    orderMappingCylinderSourceInclusion f ≫ orderMappingConeCylinderInclusion f =
      orderMappingConeSourceTopInclusion P ≫ orderMappingConeTopInclusion f := rfl

instance orderMappingConeCylinderInclusion_mono (f : P →o Q) :
    Mono (orderMappingConeCylinderInclusion f) :=
  nerveMap_mono_of_injective_orderHom (orderMappingConeCylinderEmbedding f).toOrderHom
    (orderMappingConeCylinderEmbedding f).injective

instance orderMappingConeTopInclusion_mono (f : P →o Q) :
    Mono (orderMappingConeTopInclusion f) :=
  nerveMap_mono_of_injective_orderHom (orderMappingConeTopEmbedding f).toOrderHom
    (orderMappingConeTopEmbedding f).injective

instance orderMappingConeSourceTopInclusion_mono (P : Type u) [PartialOrder P] :
    Mono (orderMappingConeSourceTopInclusion P) :=
  nerveMap_mono_of_injective_orderHom (orderMappingConeSourceTopEmbedding P).toOrderHom
    (orderMappingConeSourceTopEmbedding P).injective

/-- Every actual cone simplex lies wholly in one of the two pieces. -/
theorem orderMappingCone_simplex_cover (f : P →o Q) (d : SimplexCategoryᵒᵖ)
    (s : (nerve (OrderMappingCone f)).obj d) :
    s ∈ Set.range ((orderMappingConeCylinderInclusion f).app d) ∨
      s ∈ Set.range ((orderMappingConeTopInclusion f).app d) := by
  have hlast (k : Fin (d.unop.len + 1)) :
      s.obj k ≤ s.obj (Fin.last d.unop.len) := s.monotone (Fin.le_last k)
  cases he : s.obj (Fin.last d.unop.len) with
  | inl x =>
      left
      apply (nerveMap_orderEmbedding_range_iff (orderMappingConeCylinderEmbedding f) d s).mpr
      intro k
      have hk := hlast k
      rw [he] at hk
      cases hsk : s.obj k with
      | inl y => exact ⟨y, rfl⟩
      | inr t => rw [hsk] at hk; exact hk.elim
  | inr t =>
      right
      apply (nerveMap_orderEmbedding_range_iff (orderMappingConeTopEmbedding f) d s).mpr
      intro k
      have hk := hlast k
      rw [he] at hk
      cases hsk : s.obj k with
      | inl y =>
          cases y with
          | inl p => exact ⟨(p : WithTop P), rfl⟩
          | inr q => rw [hsk] at hk; exact hk.elim
      | inr t' => exact ⟨⊤, congrArg Sum.inr (Subsingleton.elim _ _)⟩

/-- The two actual simplicial pieces intersect exactly in the source nerve. -/
theorem orderMappingCone_simplex_intersection (f : P →o Q) (d : SimplexCategoryᵒᵖ)
    (s : (nerve (OrderMappingCylinder f)).obj d) (t : (nerve (WithTop P)).obj d)
    (h : (orderMappingConeCylinderInclusion f).app d s =
      (orderMappingConeTopInclusion f).app d t) :
    ∃ a : (nerve P).obj d,
      (orderMappingCylinderSourceInclusion f).app d a = s ∧
      (orderMappingConeSourceTopInclusion P).app d a = t := by
  let e : P ↪o OrderMappingCylinder f :=
    { toFun := Sum.inl, inj' := Sum.inl_injective, map_rel_iff' := Iff.rfl }
  have hs : s ∈ Set.range ((nerveMap e.monotone.functor).app d) := by
    apply (nerveMap_orderEmbedding_range_iff e d s).mpr
    intro k
    have hk := congrArg (fun z : (nerve (OrderMappingCone f)).obj d => z.obj k) h
    change Sum.inl (s.obj k) = orderMappingConeTopEmbedding f (t.obj k) at hk
    cases ht : t.obj k with
    | top => rw [ht] at hk; cases hk
    | coe p =>
        rw [ht] at hk
        exact ⟨p, (Sum.inl_injective hk).symm⟩
  obtain ⟨a, ha⟩ := hs
  change (orderMappingCylinderSourceInclusion f).app d a = s at ha
  refine ⟨a, ha, ?_⟩
  apply (CategoryTheory.mono_iff_injective ((orderMappingConeTopInclusion f).app d)).mp
    (inferInstance : Mono ((orderMappingConeTopInclusion f).app d))
  change (orderMappingConeCylinderInclusion f).app d
    ((orderMappingCylinderSourceInclusion f).app d a) = _
  rw [ha]
  exact h

/-- The mapping cone is the actual simplicial pushout of the source cone
and the actual mapping cylinder along the original source nerve. -/
theorem orderMappingCone_isPushout (f : P →o Q) :
    IsPushout (orderMappingCylinderSourceInclusion f) (orderMappingConeSourceTopInclusion P)
      (orderMappingConeCylinderInclusion f) (orderMappingConeTopInclusion f) := by
  apply IsPushout.of_forall_isPushout_app
  intro d
  apply Types.isPushout_of_isPullback_of_mono'
  · apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_, ?_, orderMappingCone_simplex_intersection f d⟩
    · exact congrArg (fun z => z.app d) (orderMappingCone_square f)
    · intro x y h
      exact (CategoryTheory.mono_iff_injective
        ((orderMappingCylinderSourceInclusion f).app d)).mp inferInstance h.1
  · apply Set.eq_univ_of_forall
    exact orderMappingCone_simplex_cover f d
  · intro x y _ _ h
    exact (CategoryTheory.mono_iff_injective
      ((orderMappingConeTopInclusion f).app d)).mp inferInstance h

/-- Geometric realization gives the actual topological pushout of these pieces. -/
theorem orderMappingCone_realization_isPushout (f : P →o Q) :
    IsPushout (SSet.toTop.map (orderMappingCylinderSourceInclusion f))
      (SSet.toTop.map (orderMappingConeSourceTopInclusion P))
      (SSet.toTop.map (orderMappingConeCylinderInclusion f))
      (SSet.toTop.map (orderMappingConeTopInclusion f)) :=
  (orderMappingCone_isPushout f).map SSet.toTop

/-- The actual cone nerve is finite when the original orders are finite. -/
instance orderMappingCone_nerve_finite (f : P →o Q) [Finite P] [Finite Q] :
    (nerve (OrderMappingCone f)).Finite :=
  finite_nerve_of_finite_order (OrderMappingCone f)

end KIP126.Topology.SimplicialRealization
