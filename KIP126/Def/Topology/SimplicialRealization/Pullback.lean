module

public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Data
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual pullback, as a subcomplex of the simplicial product. -/
def pullbackSubcomplex {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : (X ⊗ Y).Subcomplex :=
  equalitySubcomplex (CartesianMonoidalCategory.fst X Y ≫ f)
    (CartesianMonoidalCategory.snd X Y ≫ g)


end KIP126.Topology.SimplicialRealization

end

section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

theorem pullbackSubcomplex_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback ((pullbackSubcomplex f g).ι ≫ CartesianMonoidalCategory.fst X Y)
      ((pullbackSubcomplex f g).ι ≫ CartesianMonoidalCategory.snd X Y) f g := by
  apply IsPullback.of_forall_isPullback_app
  intro a
  apply (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · ext x
    exact x.property
  · intro x y h
    apply Subtype.ext
    exact Prod.ext h.1 h.2
  · intro x y h
    exact ⟨⟨(x,y),h⟩,rfl,rfl⟩


end KIP126.Topology.SimplicialRealization

end
