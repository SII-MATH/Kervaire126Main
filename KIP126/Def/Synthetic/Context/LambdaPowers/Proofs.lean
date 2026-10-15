module

public import KIP126.Def.Synthetic.Context.LambdaPowers.Data

@[expose] public section

/-! Naturality of the existing powers, without replacing their components. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

private theorem transported_app {a b : ℤ × ℤ} (hab : a = b)
    (α : SyntheticCategory.biShift a ⟶ 𝟭 Syn) (X : Syn) :
    (hab ▸ α).app X = (hab ▸ α.app X) := by
  subst b
  rfl

/-- This natural-transformation presentation does not choose a different λ power. -/
@[simp] theorem lambdaPowNatTrans_app (n : ℕ) (X : Syn) :
    (lambdaPowNatTrans n).app X = lambdaPow n X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lambdaPowNatTrans, lambdaPow, transported_app, NatTrans.comp_app,
      Functor.whiskerRight_app, ih]

/-- Every existing λ-power is natural in the synthetic object. -/
theorem lambdaPow_naturality (n : ℕ) {X Y : Syn} (f : X ⟶ Y) :
    (SyntheticCategory.biShift (0, -(n : ℤ))).map f ≫ lambdaPow n Y =
      lambdaPow n X ≫ f := by
  have h := (lambdaPowNatTrans n).naturality f
  dsimp only [Functor.id_obj, Functor.id_map] at h
  simpa only [lambdaPowNatTrans_app] using h

end KIP126.Synthetic.Context
