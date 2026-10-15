module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Homotopy.Data
public import KIP126.Def.StableHomotopy.Spectra.Singular.Cylinder.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite MonoidalCategory CartesianMonoidalCategory
open KIP126.StableHomotopy.Spectra
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- The actual order-map cylinder starts at the lower order map. -/
theorem orderMapCylinder_zero (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) :
    realizationCylinderEnd (nerve P) 0 ≫ orderMapCylinder f g hfg = nerveMap f.monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  exact CategoryTheory.Functor.ext (fun k => by
    change (if (0 : Fin 2) = 0 then f (s.obj k) else g (s.obj k)) = f (s.obj k)
    simp)

/-- The actual order-map cylinder ends at the upper order map. -/
theorem orderMapCylinder_one (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) :
    realizationCylinderEnd (nerve P) 1 ≫ orderMapCylinder f g hfg = nerveMap g.monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  exact CategoryTheory.Functor.ext (fun k => by
    change (if (1 : Fin 2) = 0 then f (s.obj k) else g (s.obj k)) = g (s.obj k)
    simp)

/-- On an actual suborder map where both endpoint maps agree, the
entire simplicial prism is constant in its interval direction. -/
theorem orderMapCylinder_fixed (f g : P →o Q) (hfg : ∀ p, f p ≤ g p)
    (j : R →o P) (hj : ∀ r, f (j r) = g (j r)) :
    (nerveMap j.monotone.functor ▷ Δ[1]) ≫ orderMapCylinder f g hfg =
      fst (nerve R) Δ[1] ≫ nerveMap (f.comp j).monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  exact CategoryTheory.Functor.ext (fun k => by
    change (if (SSet.stdSimplex.objEquiv z.2).toOrderHom k = 0
      then f (j (z.1.obj k)) else g (j (z.1.obj k))) = f (j (z.1.obj k))
    rw [hj]
    split_ifs <;> rfl)

/-- Pointwise comparable actual order maps have a realized homotopy
relative to the whole realized image of any order map on which they agree. -/
theorem orderMaps_homotopicRel_of_le (f g : P →o Q) (hfg : ∀ p, f p ≤ g p)
    (j : R →o P) (hj : ∀ r, f (j r) = g (j r)) :
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom.HomotopicRel
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom
      (Set.range (SSet.toTop.map (nerveMap j.monotone.functor))) := by
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
  refine ⟨{
    toFun := fun z => SSet.toTop.map C (E.symm (z.2,z.1))
    continuous_toFun := (SSet.toTop.map C).hom.continuous.comp
      (E.symm.continuous.comp (continuous_snd.prodMk continuous_fst))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    rw [hz,← TopCat.comp_app,← Functor.map_comp]
    exact congrArg (fun k => SSet.toTop.map k x) (orderMapCylinder_zero f g hfg)
  · intro x
    rw [ho,← TopCat.comp_app,← Functor.map_comp]
    exact congrArg (fun k => SSet.toTop.map k x) (orderMapCylinder_one f g hfg)
  · intro t x hx
    obtain ⟨y,rfl⟩ := hx
    change SSet.toTop.map C ((realizationCylinderHomeomorph (nerve P)).symm
      (SSet.toTop.map (nerveMap j.monotone.functor) y,t)) = _
    rw [realizationCylinderHomeomorph_symm_natural,← TopCat.comp_app,← Functor.map_comp]
    change SSet.toTop.map ((nerveMap j.monotone.functor ▷ Δ[1]) ≫ orderMapCylinder f g hfg)
      ((realizationCylinderHomeomorph (nerve R)).symm (y,t)) = _
    rw [orderMapCylinder_fixed f g hfg j hj,Functor.map_comp,TopCat.comp_app]
    have hp := congrArg Prod.fst ((realizationCylinderHomeomorph (nerve R)).apply_symm_apply (y,t))
    change SSet.toTop.map (fst (nerve R) Δ[1])
      ((realizationCylinderHomeomorph (nerve R)).symm (y,t)) = y at hp
    rw [hp]
    have he : nerveMap (f.comp j).monotone.functor =
        nerveMap j.monotone.functor ≫ nerveMap f.monotone.functor := rfl
    rw [he,Functor.map_comp,TopCat.comp_app]

end KIP126.Topology.SimplicialRealization
