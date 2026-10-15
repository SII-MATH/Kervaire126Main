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

end KIP126.Topology.SimplicialRealization
