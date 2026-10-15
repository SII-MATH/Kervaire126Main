module

public import KIP126.Def.Topology.Pushout.Equivalence.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open KIP126.StableHomotopy.Spectra
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The explicit order-map homotopy remains in each fiber of an order
map which identifies its two endpoints. -/
theorem exists_orderMaps_homotopy_over
    {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) (q : Q →o R)
    (hq : ∀ p, q (f p) = q (g p)) :
    ∃ H : (SSet.toTop.map (nerveMap f.monotone.functor)).hom.Homotopy
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom,
      ∀ (t : I) (x : |nerve P|),
        SSet.toTop.map (nerveMap q.monotone.functor) (H (t,x)) =
          SSet.toTop.map (nerveMap (q.comp f).monotone.functor) x := by
  let C := orderMapCylinder f g hfg
  let E := realizationCylinderHomeomorph (nerve P)
  have hz (x : |nerve P|) : E.symm (x,0) =
      SSet.toTop.map (realizationCylinderEnd (nerve P) 0) x := by
    apply E.injective
    rw [Homeomorph.apply_symm_apply]
    exact (realizationCylinderHomeomorph_end (nerve P) 0 x).symm
  have ho (x : |nerve P|) : E.symm (x,1) =
      SSet.toTop.map (realizationCylinderEnd (nerve P) 1) x := by
    apply E.injective
    rw [Homeomorph.apply_symm_apply]
    exact (realizationCylinderHomeomorph_end (nerve P) 1 x).symm
  have hC : C ≫ nerveMap q.monotone.functor =
      fst (nerve P) Δ[1] ≫ nerveMap (q.comp f).monotone.functor := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact CategoryTheory.Functor.ext (fun k => by
      change q (if (SSet.stdSimplex.objEquiv z.2).toOrderHom k = 0
        then f (z.1.obj k) else g (z.1.obj k)) = q (f (z.1.obj k))
      split_ifs
      · rfl
      · exact (hq _).symm)
  refine ⟨{
    toFun := fun z => SSet.toTop.map C (E.symm (z.2,z.1))
    continuous_toFun := (SSet.toTop.map C).hom.continuous.comp
      (E.symm.continuous.comp (continuous_snd.prodMk continuous_fst))
    map_zero_left := ?_
    map_one_left := ?_ },?_⟩
  · intro x
    rw [hz,← TopCat.comp_app,← CategoryTheory.Functor.map_comp]
    exact congrArg (fun k => SSet.toTop.map k x) (orderMapCylinder_zero f g hfg)
  · intro x
    rw [ho,← TopCat.comp_app,← CategoryTheory.Functor.map_comp]
    exact congrArg (fun k => SSet.toTop.map k x) (orderMapCylinder_one f g hfg)
  · intro t x
    change SSet.toTop.map (nerveMap q.monotone.functor)
      (SSet.toTop.map C (E.symm (x,t))) = _
    rw [← TopCat.comp_app,← CategoryTheory.Functor.map_comp,hC,
      CategoryTheory.Functor.map_comp,TopCat.comp_app]
    have hp := congrArg Prod.fst (E.apply_symm_apply (x,t))
    exact congrArg (SSet.toTop.map (nerveMap (q.comp f).monotone.functor)) hp

/-- The actual mapping-cylinder projection has a deformation to its
strict section through its own fibers, at every realized point. -/
theorem exists_orderMappingCylinder_fiber_deformation
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :
    ∃ H : (ContinuousMap.id |nerve (OrderMappingCylinder f)|).Homotopy
      ((SSet.toTop.map (orderMappingCylinderTargetInclusion f)).hom.comp
        (SSet.toTop.map (orderMappingCylinderProjection f)).hom),
      ∀ (t : I) (x : |nerve (OrderMappingCylinder f)|),
        SSet.toTop.map (orderMappingCylinderProjection f) (H (t,x)) =
          SSet.toTop.map (orderMappingCylinderProjection f) x := by
  obtain ⟨H,hH⟩ := exists_orderMaps_homotopy_over
    (OrderHom.id : OrderMappingCylinder f →o _)
    ((orderMappingCylinderInr f).comp (orderMappingCylinderRetraction f))
    (orderMappingCylinder_le_retract f) (orderMappingCylinderRetraction f) (fun _ => rfl)
  have hs : nerveMap (OrderHom.id : OrderMappingCylinder f →o _).monotone.functor =
      𝟙 (nerve (OrderMappingCylinder f)) := rfl
  have ht : nerveMap ((orderMappingCylinderInr f).comp
      (orderMappingCylinderRetraction f)).monotone.functor =
      orderMappingCylinderProjection f ≫ orderMappingCylinderTargetInclusion f := rfl
  refine ⟨H.cast ?_ ?_,hH⟩
  · rw [hs,CategoryTheory.Functor.map_id]
    rfl
  · rw [ht,CategoryTheory.Functor.map_comp]
    rfl

/-- The actual order mapping cone is homotopy equivalent to the
continuous cone attachment of its order map. Both maps retain the old
target space exactly, and the forward map retains the attached cone. -/
theorem exists_orderMappingCone_attachment_homotopyEquiv
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q)
    {T : TopCat.{u}} (u : SSet.toTop.obj (nerve Q) ⟶ T)
    (v : SSet.toTop.obj (nerve (WithTop P)) ⟶ T)
    (hp : IsPushout (SSet.toTop.map (nerveMap f.monotone.functor))
      (SSet.toTop.map (orderMappingConeSourceTopInclusion P)) u v) :
    ∃ E : ContinuousMap.HomotopyEquiv |nerve (OrderMappingCone f)| T,
      (∀ y : |nerve Q|, E (SSet.toTop.map
        (orderMappingCylinderTargetInclusion f ≫ orderMappingConeCylinderInclusion f) y) = u y) ∧
      (∀ y : |nerve Q|, E.invFun (u y) = SSet.toTop.map
        (orderMappingCylinderTargetInclusion f ≫ orderMappingConeCylinderInclusion f) y) ∧
      ∀ x : |nerve (WithTop P)|, E (SSet.toTop.map (orderMappingConeTopInclusion f) x) = v x := by
  let c := SSet.toTop.map (orderMappingConeCylinderInclusion f)
  let d := SSet.toTop.map (orderMappingConeTopInclusion f)
  let e := SSet.toTop.map (orderMappingCylinderProjection f)
  let r := SSet.toTop.map (orderMappingCylinderTargetInclusion f)
  let a := SSet.toTop.map (orderMappingCylinderSourceInclusion f)
  let a' := SSet.toTop.map (nerveMap f.monotone.functor)
  let i := SSet.toTop.map (orderMappingConeSourceTopInclusion P)
  have hc : IsPushout a i c d := orderMappingCone_realization_isPushout f
  have he : a ≫ e = a' := by
    dsimp only [a,e,a']
    rw [← CategoryTheory.Functor.map_comp,orderMappingCylinder_source_projection]
  have hr : r ≫ e = 𝟙 _ := by
    dsimp only [r,e]
    rw [← CategoryTheory.Functor.map_comp,orderMappingCylinder_target_projection,
      CategoryTheory.Functor.map_id]
  have hw : a ≫ (e ≫ u) = i ≫ v := by
    rw [← Category.assoc,he]
    exact hp.w
  let F := hc.desc (e ≫ u) v hw
  obtain ⟨H,hH⟩ := exists_orderMappingCylinder_fiber_deformation f
  obtain ⟨E,hEF,hER⟩ := exists_homotopyEquiv_of_cofibration_pushout_fiber_deformation
    hc hp (realization_mono_hasHomotopyExtension (orderMappingConeSourceTopInclusion P))
    e r he hr H hH F (hc.inl_desc _ _ _) (hc.inr_desc _ _ _)
  refine ⟨E,?_,?_,?_⟩
  · intro y
    rw [hEF,CategoryTheory.Functor.map_comp,TopCat.comp_app]
    change F (c (r y)) = u y
    calc
      F (c (r y)) = u (e (r y)) := ConcreteCategory.congr_hom (hc.inl_desc _ _ _) _
      _ = u y := congrArg u (ConcreteCategory.congr_hom hr y)
  · intro y
    rw [CategoryTheory.Functor.map_comp,TopCat.comp_app]
    exact hER y
  · intro x
    rw [hEF]
    exact ConcreteCategory.congr_hom (hc.inr_desc _ _ _) x

end KIP126.Topology.SimplicialRealization
