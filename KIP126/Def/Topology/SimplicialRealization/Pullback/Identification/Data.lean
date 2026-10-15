module

public import KIP126.Def.Topology.SimplicialRealization.Pullback
public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Identification.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Identify the literal equality subcomplex with the chosen categorical pullback. -/
noncomputable def pullbackSubcomplexIso {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackSubcomplex f g).toSSet ≅ pullback f g :=
  (pullbackSubcomplex_isPullback f g).isoPullback

/-- A product comparison identifies its equality locus with the topological
pullback, using the original projections. -/
noncomputable def pullbackEqualityHomeomorph {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (e : |X ⊗ Y| ≃ₜ (|X| × |Y|))
    (hfst : ∀ x, (e x).1 = SSet.toTop.map (CartesianMonoidalCategory.fst X Y) x)
    (hsnd : ∀ x, (e x).2 = SSet.toTop.map (CartesianMonoidalCategory.snd X Y) x) :
    |(pullbackSubcomplex f g).toSSet| ≃ₜ
      {xy : |X| × |Y| // SSet.toTop.map f xy.1 = SSet.toTop.map g xy.2} :=
  (equalityHomeomorph (CartesianMonoidalCategory.fst X Y ≫ f)
    (CartesianMonoidalCategory.snd X Y ≫ g)).trans
      (e.subtype (fun x => by
        rw [hfst,hsnd,Functor.map_comp,Functor.map_comp]
        rfl))

/-- Actual realization of the categorical pullback, whenever the displayed
actual product comparison is a homeomorphism. -/
noncomputable def pullbackRealizationHomeomorph {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (e : |X ⊗ Y| ≃ₜ (|X| × |Y|))
    (hfst : ∀ x, (e x).1 = SSet.toTop.map (CartesianMonoidalCategory.fst X Y) x)
    (hsnd : ∀ x, (e x).2 = SSet.toTop.map (CartesianMonoidalCategory.snd X Y) x) :
    |pullback f g| ≃ₜ
      {xy : |X| × |Y| // SSet.toTop.map f xy.1 = SSet.toTop.map g xy.2} :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (pullbackSubcomplexIso f g).symm)).trans
    (pullbackEqualityHomeomorph f g e hfst hsnd)

end KIP126.Topology.SimplicialRealization
