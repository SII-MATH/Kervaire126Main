module

public import KIP126.Def.Topology.SimplicialRealization.Pullback.Identification.Data
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem pullbackRealizationHomeomorph_fst {X Y Z : SSet.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (e : |X ⊗ Y| ≃ₜ (|X| × |Y|))
    (hfst : ∀ x, (e x).1 = SSet.toTop.map (CartesianMonoidalCategory.fst X Y) x)
    (hsnd : ∀ x, (e x).2 = SSet.toTop.map (CartesianMonoidalCategory.snd X Y) x)
    (x : |pullback f g|) :
    (pullbackRealizationHomeomorph f g e hfst hsnd x).val.1 =
      SSet.toTop.map (pullback.fst f g) x := by
  change (e (SSet.toTop.map (pullbackSubcomplex f g).ι
    (SSet.toTop.map (pullbackSubcomplexIso f g).inv x))).1 = _
  rw [hfst]
  have h := congrArg SSet.toTop.map (IsPullback.isoPullback_inv_fst (pullbackSubcomplex_isPullback f g))
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

@[simp] theorem pullbackRealizationHomeomorph_snd {X Y Z : SSet.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (e : |X ⊗ Y| ≃ₜ (|X| × |Y|))
    (hfst : ∀ x, (e x).1 = SSet.toTop.map (CartesianMonoidalCategory.fst X Y) x)
    (hsnd : ∀ x, (e x).2 = SSet.toTop.map (CartesianMonoidalCategory.snd X Y) x)
    (x : |pullback f g|) :
    (pullbackRealizationHomeomorph f g e hfst hsnd x).val.2 =
      SSet.toTop.map (pullback.snd f g) x := by
  change (e (SSet.toTop.map (pullbackSubcomplex f g).ι
    (SSet.toTop.map (pullbackSubcomplexIso f g).inv x))).2 = _
  rw [hsnd]
  have h := congrArg SSet.toTop.map (IsPullback.isoPullback_inv_snd (pullbackSubcomplex_isPullback f g))
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x


/-- The realized categorical pullback square is a genuine topological
pullback whenever its actual product comparison is a homeomorphism. -/
theorem realization_isPullback_of_product_homeomorph {X Y Z : SSet.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (e : |X ⊗ Y| ≃ₜ (|X| × |Y|))
    (hfst : ∀ x, (e x).1 = SSet.toTop.map (CartesianMonoidalCategory.fst X Y) x)
    (hsnd : ∀ x, (e x).2 = SSet.toTop.map (CartesianMonoidalCategory.snd X Y) x) :
    IsPullback (SSet.toTop.map (pullback.fst f g)) (SSet.toTop.map (pullback.snd f g))
      (SSet.toTop.map f) (SSet.toTop.map g) := by
  let i := TopCat.isoOfHomeo (pullbackRealizationHomeomorph f g e hfst hsnd) ≪≫
    (TopCat.pullbackIsoProdSubtype (SSet.toTop.map f) (SSet.toTop.map g)).symm
  apply IsPullback.of_iso_pullback ⟨by
    rw [← Functor.map_comp,← Functor.map_comp,pullback.condition]⟩ i
  · apply TopCat.ext
    intro x
    change pullback.fst (SSet.toTop.map f) (SSet.toTop.map g)
      ((TopCat.pullbackIsoProdSubtype (SSet.toTop.map f) (SSet.toTop.map g)).inv
        (pullbackRealizationHomeomorph f g e hfst hsnd x)) = _
    rw [TopCat.pullbackIsoProdSubtype_inv_fst_apply,pullbackRealizationHomeomorph_fst]
  · apply TopCat.ext
    intro x
    change pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)
      ((TopCat.pullbackIsoProdSubtype (SSet.toTop.map f) (SSet.toTop.map g)).inv
        (pullbackRealizationHomeomorph f g e hfst hsnd x)) = _
    rw [TopCat.pullbackIsoProdSubtype_inv_snd_apply,pullbackRealizationHomeomorph_snd]


end KIP126.Topology.SimplicialRealization
