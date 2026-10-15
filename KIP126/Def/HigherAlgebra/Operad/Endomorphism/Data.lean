module

public import KIP126.Def.HigherAlgebra.EnrichedTensor.Proofs

@[expose] public section

/-!
The topological endomorphism operad of an object in a point-set model with
actual enriched finite tensor operations. No synthetic model, operad algebra
structure, admissibility result or derived structure space is constructed here.
-/

namespace KIP126.HigherAlgebra.Operad.Endomorphism

open CategoryTheory MonoidalCategory EnrichedTensor

universe u v

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]

/-- The genuine mapping-space endomorphism operad. Nullary operations are
maps from the chosen empty tensor, identified with the same monoidal unit by
`P.emptyIso`; operations are not cartesian powers of an underlying space. -/
def operad (P : Presentation M) (hP : TensorLaws P) (X : M) :
    TopologicalOperad.{v} where
  Op := P.Op X
  relabel := P.relabel X
  relabel_id := (endomorphismLaws P hP X).relabel_id
  relabel_comp := (endomorphismLaws P hP X).relabel_comp
  unit := P.unit X
  compose := P.compose X
  left_unit := (endomorphismLaws P hP X).left_unit
  right_unit := (endomorphismLaws P hP X).right_unit
  associativity := (endomorphismLaws P hP X).associativity
  outer_equivariance := (endomorphismLaws P hP X).outer_equivariance
  inner_equivariance := (endomorphismLaws P hP X).inner_equivariance

end KIP126.HigherAlgebra.Operad.Endomorphism
