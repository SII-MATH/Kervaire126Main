module

public import KIP126.Def.Synthetic.Sphere.Actions.Data

@[expose] public section

namespace KIP126.Synthetic.Context
open KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- A precise local no-λ-torsion condition: injectivity of the existing action
out of this bidegree. This is a predicate, not a fact about the chosen model. -/
def LambdaInjectiveAt (m n : ℤ) (X : Syn) : Prop :=
  Function.Injective (lambdaAction m n X)

/-- Injectivity of every finite λ power from this bidegree, on the existing
action. One-step injectivity at this weight alone does not imply this. -/
def LambdaPowersInjectiveAt (m n : ℤ) (X : Syn) : Prop :=
  ∀ k : ℕ, Function.Injective (fun a : BiHom m n X => lambdaMultiply k a)

variable [HasFunctorialCofiber (C := Syn)]

/-- Vanishing after the specified quotient map, allowing zero classes. -/
def VanishesModLambda {m n : ℤ} {X : Syn} (r : ℕ) (x : BiHom m n X) : Prop :=
  quotientClass r x = 0

end KIP126.Synthetic.Context
