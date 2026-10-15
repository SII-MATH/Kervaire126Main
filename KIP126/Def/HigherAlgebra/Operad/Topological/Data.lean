module

public import KIP126.Def.HigherAlgebra.Operad.Arity.Data
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-!
A unital symmetric operad in topological spaces, indexed by finite sets.
All substitution maps are continuous. The two equivariance fields are the
outer block permutation and the inner block permutations of May, *The Geometry
of Iterated Loop Spaces*, Definition 1.1. We do not impose his extra reduced
convention on arity zero; `IsReduced` is a separate predicate.
Our ambient category is all topological spaces with ordinary finite products;
May's compactly generated Hausdorff point-set convention is not imposed here.
Admissibility and comparison with a synthetic model are separate requirements.

Reference: https://www.math.uchicago.edu/~may/BOOKS/geom_iter.pdf, Section 1.
This is an actual topological operad, not a commutative monoid in a homotopy
category. No existence claim about a synthetic model or a specific operad is
part of this definition.
-/

namespace KIP126.HigherAlgebra.Operad

universe v w

/-- Operations on finite labelled inputs, together with all unit, associative,
and symmetric coherence laws. Finite bijections act covariantly on labels;
this is equivalent to the usual right-permutation convention by taking inverse
permutations. Empty input sets are included in every substitution law. -/
structure TopologicalOperad where
  Op : FintypeCat.{0} → TopCat.{v}
  relabel : {I J : FintypeCat.{0}} → (I ≃ J) → (Op I ≃ₜ Op J)
  relabel_id : ∀ (I : FintypeCat.{0}) (x : Op I), relabel (Equiv.refl I) x = x
  relabel_comp : ∀ {I J K : FintypeCat.{0}} (e : I ≃ J) (f : J ≃ K) (x : Op I),
    relabel (e.trans f) x = relabel f (relabel e x)
  unit : Op Arity.one
  compose : ∀ (I : FintypeCat.{0}) (J : I → FintypeCat.{0}),
    C(Op I × ((i : I) → Op (J i)), Op (Arity.sum I J))
  left_unit : ∀ (I : FintypeCat.{0}) (x : Op I),
    relabel (Arity.leftUnit I)
      (compose Arity.one (fun _ => I) (unit, fun _ => x)) = x
  right_unit : ∀ (I : FintypeCat.{0}) (x : Op I),
    relabel (Arity.rightUnit I)
      (compose I (fun _ => Arity.one) (x, fun _ => unit)) = x
  associativity : ∀ (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
    (K : (i : I) → J i → FintypeCat.{0}) (x : Op I)
    (y : (i : I) → Op (J i)) (z : (i : I) → (j : J i) → Op (K i j)),
    relabel (Arity.assoc I J K)
      (compose (Arity.sum I J) (fun ij => K ij.1 ij.2)
        (compose I J (x, y), fun ij => z ij.1 ij.2)) =
      compose I (fun i => Arity.sum (J i) (K i))
        (x, fun i => compose (J i) (K i) (y i, z i))
  outer_equivariance : ∀ {I I' : FintypeCat.{0}} (e : I ≃ I')
    (J : I' → FintypeCat.{0}) (x : Op I) (y : (i : I') → Op (J i)),
    relabel (Arity.outer e J)
      (compose I (fun i => J (e i)) (x, fun i => y (e i))) =
      compose I' J (relabel e x, y)
  inner_equivariance : ∀ (I : FintypeCat.{0}) (J J' : I → FintypeCat.{0})
    (e : (i : I) → J i ≃ J' i) (x : Op I) (y : (i : I) → Op (J i)),
    relabel (Arity.inner I e) (compose I J (x, y)) =
      compose I J' (x, fun i => relabel (e i) (y i))

namespace TopologicalOperad

/-- A morphism preserves the same labelled operations, identity, relabelling,
and every substitution; continuity is part of the actual component maps. -/
structure Hom (O : TopologicalOperad.{v}) (P : TopologicalOperad.{w}) where
  app : (I : FintypeCat.{0}) → C(O.Op I, P.Op I)
  map_unit : app Arity.one O.unit = P.unit
  map_relabel : ∀ {I J : FintypeCat.{0}} (e : I ≃ J) (x : O.Op I),
    app J (O.relabel e x) = P.relabel e (app I x)
  map_compose : ∀ (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
    (x : O.Op I) (y : (i : I) → O.Op (J i)),
    app (Arity.sum I J) (O.compose I J (x, y)) =
      P.compose I J (app I x, fun i => app (J i) (y i))

end TopologicalOperad
end KIP126.HigherAlgebra.Operad
