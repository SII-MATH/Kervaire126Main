module

public import KIP126.Def.Synthetic.Completion.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Predicates

@[expose] public section

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Derived λ-completeness is vanishing of the actual iterated-λ
residual tower's homotopy limit. This is the criterion used in BHS,
`SynRevAdams.tex`, proof of `lemm:comp2`; it does not mean that ordinary
inverse limits of homotopy groups have no derived-limit term. -/
def IsLambdaComplete [HasProductsOfShape ℕ Syn] (A : Syn) : Prop :=
  (lambdaResidualSequence A).IsAcyclic

/-- The restriction maps are compatible with the actual boundaries of
the chosen λ-power cofibers and the actual residual λ transition.
Together with `rho_quotient`, this gives the displayed squares of the
successive cofiber triangles. It does not construct a higher model.
-/
def FiniteLambdaQuotientTower.ResidualCompatible
    [HasFunctorialCofiber (C := Syn)] {A : Syn}
    (T : FiniteLambdaQuotientTower A) : Prop :=
  ∀ n : ℕ,
    T.rho (n + 1) (n + 2) (by omega) ≫ XModLambdaN.proj A (n + 1) =
      XModLambdaN.proj A (n + 2) ≫
        ((lambdaResidualSequence A).step (n + 1))⟦(1 : ℤ)⟧'

end KIP126.Synthetic.Context
