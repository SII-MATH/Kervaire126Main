module

public import KIP126.Def.Synthetic.QuotientTower.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Data

@[expose] public section

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The actual residual λ tower. Its transition is the first factor in
the existing recursive definition of `lambdaPow (n+1) A`. -/
noncomputable def lambdaResidualSequence (A : Syn) : InverseSequence Syn where
  obj n := (SyntheticCategory.biShift (0, -(n : ℤ))).obj A
  step n :=
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj A)
      (by simp : ((0 : ℤ), -(↑(n + 1) : ℤ)) = (0, -1) + (0, -(n : ℤ)))) ≫
      (SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))).inv.app A ≫
        (SyntheticCategory.biShift (0, -(n : ℤ))).map (SyntheticCategory.lam.app A)

variable [HasFunctorialCofiber (C := Syn)]

/-- The positive finite quotient sequence belonging to one specified
λ–ρ–δ tower. Its `n`th object is the existing quotient by `λ^(n+1)`. -/
noncomputable def FiniteLambdaQuotientTower.toInverseSequence {A : Syn}
    (T : FiniteLambdaQuotientTower A) : InverseSequence Syn where
  obj n := XModLambdaN A (n + 1)
  step n := T.rho (n + 1) (n + 2) (by omega)

variable [HasProductsOfShape ℕ Syn]

/-- The precise λ-adic completion conclusion: `A` is a Milnor
homotopy-limit vertex for the same finite quotient tower, with every
projection equal to the actual cofiber inclusion. The finite λ–ρ–δ
triangles and restriction laws remain those of `T`.

This does not assert an ordinary limit universal property in `Ho(Syn)`
or identify maps into `A` with an ordinary limit of homotopy groups.
-/
structure LambdaAdicCompletion {A : Syn} (T : FiniteLambdaQuotientTower A) where
  homotopyLimit : SequentialHomotopyLimit T.toInverseSequence A
  projection_eq : ∀ n,
    homotopyLimit.π n = XModLambdaN.incl A (n + 1)

end KIP126.Synthetic.Context
