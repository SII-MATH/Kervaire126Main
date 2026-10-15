module

public import KIP126.Def.HigherAlgebra.Operad.EnrichedAlgebra.Category.Data
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

@[expose] public section

/-!
A model structure on the actual category of enriched operadic algebras whose
weak equivalences and fibrations are created by the same forgetful functor.

This is data and its precise compatibility requirements, not an assertion that
the transferred model structure exists. Cofibrations and all lifting and
factorization axioms belong to the specified `ModelCategory` structure; no
independent replacement class of cofibrations is introduced. This record does
not assert a topological SM7 axiom, a monoidal model-category condition, or a
comparison with synthetic commutative algebra objects.
-/

namespace KIP126.HigherAlgebra.Operad

open CategoryTheory MonoidalCategory HomotopicalAlgebra EnrichedTensor

universe u v w

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M] [ModelCategory M]

/-- A specified model structure on the actual enriched operadic algebra
category, with weak equivalences and fibrations exactly those of the chosen
underlying model after forgetting the action. Both equalities use the same
`model` field through an explicit local instance. -/
structure TransferredModelStructure (P : Presentation M) (hP : TensorLaws P)
    (O : TopologicalOperad.{w}) where
  model : ModelCategory (EnrichedAlgebra P hP O)
  weakEquivalences_created :
    letI : ModelCategory (EnrichedAlgebra P hP O) := model
    weakEquivalences (EnrichedAlgebra P hP O) =
      (weakEquivalences M).inverseImage (EnrichedAlgebra.forget P hP O)
  fibrations_created :
    letI : ModelCategory (EnrichedAlgebra P hP O) := model
    fibrations (EnrichedAlgebra P hP O) =
      (fibrations M).inverseImage (EnrichedAlgebra.forget P hP O)

end KIP126.HigherAlgebra.Operad
