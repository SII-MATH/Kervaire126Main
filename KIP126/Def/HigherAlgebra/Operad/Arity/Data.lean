module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-!
Finite input labels for symmetric operads. Substitution uses the actual
dependent sum of the input sets, so block permutations and reassociation
are explicit equivalences of labels, rather than equalities of cardinalities.
-/

namespace KIP126.HigherAlgebra.Operad.Arity

universe u

/-- The singleton input set used by the operadic identity. -/
abbrev one : FintypeCat.{u} := FintypeCat.of PUnit.{u + 1}

/-- The finite set of all inputs after substituting the `J i` into `I`. -/
abbrev sum (I : FintypeCat.{u}) (J : I → FintypeCat.{u}) : FintypeCat.{u} :=
  FintypeCat.of ((i : I) × J i)

/-- Forget the outer singleton label. -/
def leftUnit (I : FintypeCat.{u}) : sum one (fun _ => I) ≃ I :=
  (Equiv.sigmaEquivProd PUnit I).trans (Equiv.punitProd I)

/-- Forget the singleton attached to each input. -/
def rightUnit (I : FintypeCat.{u}) : sum I (fun _ => one) ≃ I :=
  Equiv.sigmaPUnit I

/-- The label bijection comparing the two orders of a three-level substitution. -/
def assoc (I : FintypeCat.{u}) (J : I → FintypeCat.{u})
    (K : (i : I) → J i → FintypeCat.{u}) :
    sum (sum I J) (fun ij => K ij.1 ij.2) ≃ sum I (fun i => sum (J i) (K i)) :=
  Equiv.sigmaAssoc (fun i j => K i j)

/-- Move the outer labels while retaining their corresponding input blocks. -/
def outer {I I' : FintypeCat.{u}} (e : I ≃ I') (J : I' → FintypeCat.{u}) :
    sum I (fun i => J (e i)) ≃ sum I' J :=
  Equiv.sigmaCongrLeft (β := fun i' => (J i' : Type u)) e

/-- Relabel each input block without changing the outer labels. -/
def inner (I : FintypeCat.{u}) {J J' : I → FintypeCat.{u}}
    (e : (i : I) → J i ≃ J' i) : sum I J ≃ sum I J' :=
  Equiv.sigmaCongrRight e

end KIP126.HigherAlgebra.Operad.Arity
