module

public import KIP126.Def.Synthetic.QuotientTower.Predicates
public import KIP126.Def.Synthetic.QuotientMap.Proofs

@[expose] public section

/-! Local laws of a supplied coherent tower. No tower inhabitant is assumed globally. -/

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {X Y : Syn} {i j : ℕ}

theorem LambdaRhoDeltaTriangle.lambda_comp_rho (T : LambdaRhoDeltaTriangle X i j) :
    T.lambdaMap ≫ T.rho = 0 :=
  comp_distTriang_mor_zero₁₂ _ T.distinguished

theorem LambdaRhoDeltaTriangle.rho_comp_delta (T : LambdaRhoDeltaTriangle X i j) :
    T.rho ≫ T.delta = 0 :=
  comp_distTriang_mor_zero₂₃ _ T.distinguished

theorem FiniteLambdaQuotientTower.lambda_comp_rho
    (T : FiniteLambdaQuotientTower X) (hi : 0 < i) (hij : i < j) :
    (T.triangle hi hij).lambdaMap ≫ T.rho i j hij.le = 0 := by
  rw [← T.triangle_rho hi hij]
  exact (T.triangle hi hij).lambda_comp_rho

theorem FiniteLambdaQuotientTower.rho_comp_delta
    (T : FiniteLambdaQuotientTower X) (hi : 0 < i) (hij : i < j) :
    T.rho i j hij.le ≫ (T.triangle hi hij).delta = 0 := by
  rw [← T.triangle_rho hi hij]
  exact (T.triangle hi hij).rho_comp_delta

/-! The following three lemmas record the adjacent-quotient exactness used
in the finite Bockstein lift argument.  They are stated for the tower's
actual restriction maps, so the comparison does not require a separate
second quotient model. -/

theorem FiniteLambdaQuotientTower.Hom.rho_comm
    {TX : FiniteLambdaQuotientTower X} {TY : FiniteLambdaQuotientTower Y}
    {f : X ⟶ Y} (F : FiniteLambdaQuotientTower.Hom TX TY f) (hij : i ≤ j) :
    TX.rho i j hij ≫ XModLambdaN.map f i =
      XModLambdaN.map f j ≫ TY.rho i j hij :=
  F.rho_naturality hij

end KIP126.Synthetic.Context
