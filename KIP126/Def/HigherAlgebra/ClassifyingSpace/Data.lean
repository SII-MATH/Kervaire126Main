module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Widesubcategory
public import KIP126.Def.Topology.HomotopyFiber.Data

@[expose] public section

/-!
# Classifying spaces and fibers of structure-forgetting functors

These are actual realizations of nerves, with the path-model homotopy fiber
over a specified object. In particular, the fiber remembers an identification
in the classifying space, rather than imposing equality of the underlying
objects. Morphism properties specify exactly which maps enter the nerves.

For an algebra forgetful functor, use the inverse image of the model's weak
equivalences. This construction alone does not prove that a particular
point-set algebra category presents a desired infinity category.
-/

namespace KIP126.HigherAlgebra.ClassifyingSpace

open CategoryTheory Opposite Simplicial

universe u v

noncomputable section

/-- The geometric realization of the actual ordinary nerve. -/
def space (C : Type u) [Category.{v} C] : TopCat.{max u v} :=
  SSet.toTop.obj (nerve C)

/-- The point represented by the zero-simplex of the specified object. -/
def vertex {C : Type u} [Category.{v} C] (X : C) : space C :=
  (TopCat.toSSetObjEquiv (space C) (op ⦋0⦌)
    ((sSetTopAdj.unit.app (nerve C)).app (op ⦋0⦌)
      (ComposableArrows.mk₀ X))) (stdSimplex.vertex (0 : Fin 1))

/-- The continuous map induced by the given functor, with no new choices. -/
def map {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    C(space C, space D) :=
  (SSet.toTop.map (nerveMap F)).hom

/-- Homotopy fiber of the classifying-space map at the specified object. -/
def fiber {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (Y : D) : TopCat.{max u v} :=
  KIP126.Topology.PathHomotopyFiber.space (map F) (vertex Y)

/-- Restrict a functor to the maps selected by two multiplicative properties. -/
def restrict {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
    [P.IsMultiplicative] [Q.IsMultiplicative] (hF : P ≤ Q.inverseImage F) :
    WideSubcategory P ⥤ WideSubcategory Q where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.hom, hF _ f.property⟩
  map_id X := InducedWideCategory.Hom.ext (F.map_id X.obj)
  map_comp f g := InducedWideCategory.Hom.ext (F.map_comp f.hom g.hom)

/-- The structure morphisms retained here are precisely the morphisms whose
underlying maps have property `W`. For model categories the intended `W` is
their actual weak-equivalence property. -/
def weakForgetful {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (W : MorphismProperty D) [W.IsMultiplicative] :
    WideSubcategory (W.inverseImage F) ⥤ WideSubcategory W :=
  restrict F (W.inverseImage F) W le_rfl

/-- The relative moduli space defined from weak-equivalence nerves. Its point
over `Y` includes a path to the vertex of `Y`; it is not a strict object fiber. -/
def relativeModuli {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (W : MorphismProperty D) [W.IsMultiplicative] (Y : D) :
    TopCat.{max u v} :=
  fiber (weakForgetful F W) ⟨Y⟩

end
end KIP126.HigherAlgebra.ClassifyingSpace
