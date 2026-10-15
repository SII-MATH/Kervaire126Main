module

public import KIP126.Def.HigherAlgebra.Operad.EnrichedAlgebra.Category.Data
public import KIP126.Def.HigherAlgebra.ClassifyingSpace.Data

@[expose] public section

/-!
# Relative operadic moduli from weak-equivalence nerves

The functor forgets an actual operadic action but retains its nullary unit.
Both weak-equivalence subcategories use the same property on underlying
model morphisms. The fiber is taken at the actual arrow `q`, not merely at
its codomain. One common universe above the finite-label universe accommodates
the algebra category, the under-category and their nerves.

This defines a space for any multiplicative morphism property. Calling it a
model for synthetic commutative algebras additionally requires the relevant
model structures, their weak-equivalence comparisons, and a comparison of
the unit under-category. None of those conclusions follows from this definition.
-/

namespace KIP126.HigherAlgebra.Operad.EnrichedAlgebra

open CategoryTheory MonoidalCategory EnrichedTensor

universe u

variable {M : Type (u + 1)} [Category.{u + 1} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{u + 1} M]

/-- Actual relative moduli of actions over the specified unit arrow. The
classifying spaces contain exactly maps whose underlying arrows satisfy `W`.
The path in the homotopy fiber retains a homotopy identification of units. -/
noncomputable def unitModuli (P : Presentation M) (hP : TensorLaws P)
    (O : TopologicalOperad.{u + 1}) (o : O.Op empty)
    (W : MorphismProperty M) [W.IsMultiplicative] {X : M} (q : 𝟙_ M ⟶ X) :
    TopCat.{u + 1} :=
  ClassifyingSpace.relativeModuli (unitForget P hP O o)
    (W.inverseImage (Under.forget (𝟙_ M))) (Under.mk q)

end KIP126.HigherAlgebra.Operad.EnrichedAlgebra
