module

public import KIP126.Def.Synthetic.QuotientTower.Data

@[expose] public section

/-! Naturality conditions for maps of the same finite λ-quotient towers. -/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {X Y : Syn}

/-- All components are the actual `XModLambdaN.map f n`; this record supplies
their compatibility with the specified restrictions and λ–ρ–δ triangles. -/
structure FiniteLambdaQuotientTower.Hom (TX : FiniteLambdaQuotientTower X)
    (TY : FiniteLambdaQuotientTower Y) (f : X ⟶ Y) : Prop where
  rho_naturality : ∀ {i j : ℕ} (hij : i ≤ j),
    TX.rho i j hij ≫ XModLambdaN.map f i =
      XModLambdaN.map f j ≫ TY.rho i j hij
  lambda_naturality : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (SyntheticCategory.biShift (0, -(i : ℤ))).map
          (XModLambdaN.map f (j - i)) ≫
        (TY.triangle hi hij).lambdaMap =
      (TX.triangle hi hij).lambdaMap ≫ XModLambdaN.map f j
  delta_naturality : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    XModLambdaN.map f i ≫ (TY.triangle hi hij).delta =
      (TX.triangle hi hij).delta ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(i : ℤ))).map
            (XModLambdaN.map f (j - i)))

end KIP126.Synthetic.Context
