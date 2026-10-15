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

@[simp] theorem FiniteLambdaQuotientTower.rho_self
    (T : FiniteLambdaQuotientTower X) (i : ℕ) :
    T.rho i i le_rfl = 𝟙 (XModLambdaN X i) :=
  T.rho_id i

theorem FiniteLambdaQuotientTower.rho_trans
    (T : FiniteLambdaQuotientTower X) {k i j : ℕ} (hki : k ≤ i) (hij : i ≤ j) :
    T.rho i j hij ≫ T.rho k i hki = T.rho k j (hki.trans hij) :=
  T.rho_comp hki hij

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

theorem FiniteLambdaQuotientTower.exists_adjacent_lambda_preimage
    (Q : FiniteLambdaQuotientTower X)
    (S : Syn) (i : ℕ) (hi : 0 < i)
    (a : S ⟶ XModLambdaN X (i + 1))
    (ha : a ≫ Q.rho 1 (i + 1) (by omega) = 0) :
    ∃ z : S ⟶ (SyntheticCategory.biShift (0, -1)).obj (XModLambdaN X i),
      z ≫ (Q.triangle (by omega : 0 < 1) (by omega : 1 < i + 1)).lambdaMap = a := by
  let hlt : 1 < i + 1 := by omega
  let D := Q.triangle (by omega : 0 < 1) hlt
  have hz : a ≫ D.rho = 0 := by
    rw [Q.triangle_rho (by omega : 0 < 1) hlt]
    exact ha
  obtain ⟨z, hz'⟩ := Triangle.coyoneda_exact₂ _ D.distinguished a hz
  exact ⟨z, hz'.symm⟩

theorem FiniteLambdaQuotientTower.adjacent_lift_boundary_difference
    (Q : FiniteLambdaQuotientTower X) (S : Syn) (i : ℕ) (hi : 0 < i)
    {A : Type*} [AddCommGroup A]
    (d : (S ⟶ XModLambdaN X (i + 1)) →+ A)
    (B : AddSubgroup A)
    (hfirst : ∀ z : S ⟶ (SyntheticCategory.biShift (0, -1)).obj
        (XModLambdaN X i),
      d (z ≫ (Q.triangle (by omega : 0 < 1)
        (by omega : 1 < i + 1)).lambdaMap) ∈ B)
    (a b : S ⟶ XModLambdaN X (i + 1))
    (hab : a ≫ Q.rho 1 (i + 1) (by omega) =
      b ≫ Q.rho 1 (i + 1) (by omega)) :
    d a - d b ∈ B := by
  have hzero : (a - b) ≫ Q.rho 1 (i + 1) (by omega) = 0 := by
    rw [Preadditive.sub_comp, hab, sub_self]
  obtain ⟨z, hz⟩ := Q.exists_adjacent_lambda_preimage S i hi (a - b) hzero
  rw [← map_sub, ← hz]
  exact hfirst z

theorem FiniteLambdaQuotientTower.adjacent_lift_boundary_eq_mod
    (Q : FiniteLambdaQuotientTower X) (S : Syn) (i : ℕ) (hi : 0 < i)
    {A : Type*} [AddCommGroup A]
    (d : (S ⟶ XModLambdaN X (i + 1)) →+ A)
    (B : AddSubgroup A)
    (hfirst : ∀ z : S ⟶ (SyntheticCategory.biShift (0, -1)).obj
        (XModLambdaN X i),
      d (z ≫ (Q.triangle (by omega : 0 < 1)
        (by omega : 1 < i + 1)).lambdaMap) ∈ B)
    (a b : S ⟶ XModLambdaN X (i + 1))
    (hab : a ≫ Q.rho 1 (i + 1) (by omega) =
      b ≫ Q.rho 1 (i + 1) (by omega)) :
    (QuotientAddGroup.mk (d a : A) : A ⧸ B) =
      (QuotientAddGroup.mk (d b : A) : A ⧸ B) := by
  apply QuotientAddGroup.eq.mpr
  have h := Q.adjacent_lift_boundary_difference S i hi d B hfirst a b hab
  convert B.neg_mem h using 1; abel

theorem FiniteLambdaQuotientTower.Hom.rho_comm
    {TX : FiniteLambdaQuotientTower X} {TY : FiniteLambdaQuotientTower Y}
    {f : X ⟶ Y} (F : FiniteLambdaQuotientTower.Hom TX TY f) (hij : i ≤ j) :
    TX.rho i j hij ≫ XModLambdaN.map f i =
      XModLambdaN.map f j ≫ TY.rho i j hij :=
  F.rho_naturality hij

end KIP126.Synthetic.Context
