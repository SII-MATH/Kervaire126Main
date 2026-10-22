module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Singular/Cylinder/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Singular.Cylinder.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory Opposite Simplicial MonoidalCategory
open KIP126.Topology.SimplicialRealization
open scoped unitInterval

universe u
set_option backward.isDefEq.respectTransparency false

theorem realization_const_apply {K L : SSet.{u}} (v : L.obj (op ⦋0⦌)) (x : |K|) :
    SSet.toTop.map (SSet.const (X := K) v) x = (basedRealization L v).point := by
  let q : K ⟶ (Δ[0] : SSet.{u}) := SSet.const (SSet.yonedaEquiv (𝟙 _))
  rw [show SSet.const (X := K) v = q ≫ SSet.const v from (SSet.comp_const q v).symm,
    Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map q x) default]
  exact basedRealization_point L v

theorem realizationCylinderHomeomorph_natural {K L : SSet.{u}} (φ : K ⟶ L)
    (x : |K ⊗ Δ[1]|) :
    realizationCylinderHomeomorph L (SSet.toTop.map (φ ▷ Δ[1]) x) =
      (SSet.toTop.map φ (realizationCylinderHomeomorph K x).1,
        (realizationCylinderHomeomorph K x).2) := by
  apply Prod.ext
  · change SSet.toTop.map (CartesianMonoidalCategory.fst L Δ[1])
      (SSet.toTop.map (φ ▷ Δ[1]) x) =
      SSet.toTop.map φ (SSet.toTop.map (CartesianMonoidalCategory.fst K Δ[1]) x)
    have h : (φ ▷ Δ[1]) ≫ CartesianMonoidalCategory.fst L Δ[1] =
        CartesianMonoidalCategory.fst K Δ[1] ≫ φ := by simp
    have h' := congrArg SSet.toTop.map h
    simp only [Functor.map_comp] at h'
    exact ConcreteCategory.congr_hom h' x
  · apply congrArg (fun z => stdSimplexHomeomorphUnitInterval
      (SimplexCategory.toTopHomeo ⦋1⦌ z))
    change SSet.toTop.map (CartesianMonoidalCategory.snd L Δ[1])
      (SSet.toTop.map (φ ▷ Δ[1]) x) =
      SSet.toTop.map (CartesianMonoidalCategory.snd K Δ[1]) x
    have h : (φ ▷ Δ[1]) ≫ CartesianMonoidalCategory.snd L Δ[1] =
        CartesianMonoidalCategory.snd K Δ[1] := by simp
    have h' := congrArg SSet.toTop.map h
    simp only [Functor.map_comp] at h'
    exact ConcreteCategory.congr_hom h' x

theorem realizationCylinderHomeomorph_symm_natural {K L : SSet.{u}} (φ : K ⟶ L)
    (x : |K|) (t : I) :
    (realizationCylinderHomeomorph L).symm (SSet.toTop.map φ x,t) =
      SSet.toTop.map (φ ▷ Δ[1]) ((realizationCylinderHomeomorph K).symm (x,t)) := by
  apply (realizationCylinderHomeomorph L).injective
  rw [Homeomorph.apply_symm_apply,realizationCylinderHomeomorph_natural,
    Homeomorph.apply_symm_apply]

theorem realizationCylinderHomeomorph_end (K : SSet.{u}) (i : Fin 2) (x : |K|) :
    realizationCylinderHomeomorph K (SSet.toTop.map (realizationCylinderEnd K i) x) =
      (x, stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) := by
  apply Prod.ext
  · change SSet.toTop.map (CartesianMonoidalCategory.fst K Δ[1])
      (SSet.toTop.map (realizationCylinderEnd K i) x) = x
    rw [← TopCat.comp_app,← Functor.map_comp]
    have h : realizationCylinderEnd K i ≫ CartesianMonoidalCategory.fst K Δ[1] = 𝟙 K := by
      simp [realizationCylinderEnd]
    rw [h,CategoryTheory.Functor.map_id]
    rfl
  · change stdSimplexHomeomorphUnitInterval (SimplexCategory.toTopHomeo ⦋1⦌
      (SSet.toTop.map (CartesianMonoidalCategory.snd K Δ[1])
        (SSet.toTop.map (realizationCylinderEnd K i) x))) = _
    rw [← TopCat.comp_app,← Functor.map_comp]
    have h : realizationCylinderEnd K i ≫ CartesianMonoidalCategory.snd K Δ[1] =
        SSet.const (SSet.stdSimplex.obj₀Equiv.symm i) := by simp [realizationCylinderEnd]
    rw [h,realization_const_apply,← basedRealization_point]
    have hc : (SSet.const (SSet.stdSimplex.obj₀Equiv.symm i) : Δ[0] ⟶ Δ[1]) =
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) := by
      ext a f
      rfl
    rw [hc,SimplexCategory.toTopHomeo_naturality_apply,
      Subsingleton.elim (SimplexCategory.toTopHomeo ⦋0⦌ default) (stdSimplex.vertex 0),
      stdSimplex.map_vertex]
    rfl

theorem singularCylinder_endpoint (K : SSet.{u}) (B : TopCat.{u})
    (f : C(|K| × I,B)) (i : Fin 2) (x : |K|) :
    singularCylinder K B f (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
      SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B)
        (f.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _
          (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))))))) x := by
  have he : (realizationCylinderHomeomorph K).symm
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
      SSet.toTop.map (realizationCylinderEnd K i) x := by
    apply (realizationCylinderHomeomorph K).injective
    rw [Homeomorph.apply_symm_apply,realizationCylinderHomeomorph_end]
  have h : realizationCylinderEnd K i ≫ singularCylinderAdjoint K B f =
      sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B)
        (f.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _
          (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)))))) := by
    rw [singularCylinderAdjoint,← sSetTopAdj.homEquiv_naturality_left]
    apply congrArg (sSetTopAdj.homEquiv K B)
    apply ConcreteCategory.hom_ext
    intro y
    change f (realizationCylinderHomeomorph K
      (SSet.toTop.map (realizationCylinderEnd K i) y)) = _
    rw [realizationCylinderHomeomorph_end]
    rfl
  change SSet.toTop.map (singularCylinderAdjoint K B f)
    ((realizationCylinderHomeomorph K).symm
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))) = _
  rw [he,← TopCat.comp_app,← Functor.map_comp,h]

theorem singularCylinder_evaluation (K : SSet.{u}) (B : TopCat.{u})
    (f : C(|K| × I,B)) (x : |K| × I) :
    sSetTopAdj.counit.app B (singularCylinder K B f x) = f x := by
  have h := (sSetTopAdj.homEquiv _ _).symm_apply_apply
    (TopCat.ofHom (Y := B) (f.comp ⟨realizationCylinderHomeomorph K,
      (realizationCylinderHomeomorph K).continuous⟩))
  rw [Adjunction.homEquiv_counit] at h
  have hx := ConcreteCategory.congr_hom h ((realizationCylinderHomeomorph K).symm x)
  change sSetTopAdj.counit.app B (singularCylinder K B f x) =
    f ((realizationCylinderHomeomorph K) ((realizationCylinderHomeomorph K).symm x)) at hx
  simpa only [Homeomorph.apply_symm_apply] using hx

theorem singularCylinder_const (K : SSet.{u}) (B : TopCat.{u}) (b : B) (x : |K| × I) :
    singularCylinder K B (ContinuousMap.const _ b) x =
      (basedRealization (TopCat.toSSet.obj B) (TopCat.toSSetObj₀Equiv.symm b)).point := by
  have h : singularCylinderAdjoint K B (ContinuousMap.const _ b) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm b) := by
    change sSetTopAdj.homEquiv _ _ (TopCat.const b) = _
    simp [Adjunction.homEquiv_unit]
  change SSet.toTop.map (singularCylinderAdjoint K B (ContinuousMap.const _ b)) _ = _
  rw [h]
  exact realization_const_apply _ _

theorem singularCylinder_precomp {K L : SSet.{u}} (φ : K ⟶ L) (B : TopCat.{u})
    (f : C(|L| × I,B)) (x : |K|) (t : I) :
    singularCylinder L B f (SSet.toTop.map φ x,t) =
      singularCylinder K B
        (f.comp ((SSet.toTop.map φ).hom.prodMap (ContinuousMap.id I))) (x,t) := by
  have h : (φ ▷ Δ[1]) ≫ singularCylinderAdjoint L B f =
      singularCylinderAdjoint K B
        (f.comp ((SSet.toTop.map φ).hom.prodMap (ContinuousMap.id I))) := by
    rw [singularCylinderAdjoint,← sSetTopAdj.homEquiv_naturality_left]
    unfold singularCylinderAdjoint
    apply congrArg (sSetTopAdj.homEquiv _ _)
    apply ConcreteCategory.hom_ext
    intro y
    change f (realizationCylinderHomeomorph L (SSet.toTop.map (φ ▷ Δ[1]) y)) = _
    rw [realizationCylinderHomeomorph_natural]
    rfl
  change SSet.toTop.map (singularCylinderAdjoint L B f)
    ((realizationCylinderHomeomorph L).symm (SSet.toTop.map φ x,t)) = _
  rw [realizationCylinderHomeomorph_symm_natural,← TopCat.comp_app,← Functor.map_comp,h]
  rfl

theorem singularCylinder_postcomp (K : SSet.{u}) {B D : TopCat.{u}}
    (g : B ⟶ D) (f : C(|K| × I,B)) (x : |K| × I) :
    SSet.toTop.map (TopCat.toSSet.map g) (singularCylinder K B f x) =
      singularCylinder K D (g.hom.comp f) x := by
  have h : singularCylinderAdjoint K B f ≫ TopCat.toSSet.map g =
      singularCylinderAdjoint K D (g.hom.comp f) := by
    rw [singularCylinderAdjoint,← sSetTopAdj.homEquiv_naturality_right]
    rfl
  change SSet.toTop.map (TopCat.toSSet.map g)
    (SSet.toTop.map (singularCylinderAdjoint K B f) _) = _
  rw [← TopCat.comp_app,← Functor.map_comp,h]
  rfl

end KIP126.AdamsSynthetic.Source
