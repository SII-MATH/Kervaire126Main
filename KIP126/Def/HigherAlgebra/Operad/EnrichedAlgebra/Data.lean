module

public import KIP126.Def.HigherAlgebra.Operad.Endomorphism.Data

@[expose] public section

/-!
# Operadic algebras on enriched tensor objects

An action takes values in the actual mapping spaces out of finite tensor
powers. Algebra morphisms commute with every operation, including nullary
ones. The nullary unit is an ordinary morphism from the same monoidal unit.
No transferred model structure or derived comparison is asserted here.
-/

namespace KIP126.HigherAlgebra.Operad

open CategoryTheory MonoidalCategory EnrichedTensor

universe u v w

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]

/-- A continuous operadic action on the specified tensor object. -/
abbrev AlgebraOn (P : Presentation M) (hP : TensorLaws P)
    (O : TopologicalOperad.{w}) (X : M) :=
  TopologicalOperad.Hom O (Endomorphism.operad P hP X)

/-- An object and an operadic action on precisely that object. -/
structure EnrichedAlgebra (P : Presentation M) (hP : TensorLaws P)
    (O : TopologicalOperad.{w}) where
  carrier : M
  action : AlgebraOn P hP O carrier

namespace EnrichedAlgebra

variable {P : Presentation M} {hP : TensorLaws P} {O : TopologicalOperad.{w}}

/-- The actual arrow associated to one of the action's operations. -/
def operation (A : EnrichedAlgebra P hP O) (I : FintypeCat.{0}) (x : O.Op I) :
    P.tensorObj I (fun _ => A.carrier) ⟶ A.carrier :=
  arrow (A.action.app I x)

/-- The unit uses the specified nullary operation and the existing empty
tensor comparison. It is not an independently chosen map. -/
def unit (o : O.Op empty) (A : EnrichedAlgebra P hP O) : 𝟙_ M ⟶ A.carrier :=
  (P.emptyIso (fun _ => A.carrier)).inv ≫ A.operation empty o

/-- A morphism of actions respects every finite arity. -/
@[ext] structure Hom (A B : EnrichedAlgebra P hP O) where
  hom : A.carrier ⟶ B.carrier
  commutes : ∀ (I : FintypeCat.{0}) (x : O.Op I),
    A.operation I x ≫ hom = P.map I (fun _ => hom) ≫ B.operation I x

end EnrichedAlgebra
end KIP126.HigherAlgebra.Operad
