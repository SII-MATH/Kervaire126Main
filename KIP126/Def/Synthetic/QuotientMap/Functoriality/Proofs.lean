module

public import KIP126.Def.Synthetic.QuotientMap.Data
public import KIP126.Def.StableHomotopy.Context.CofiberCoherence.Proofs

@[expose] public section

/-! Functor laws for the original `XModLambdaN.map`, conditional on the exact
identity and composition equations for the chosen cofiber construction. -/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

@[simp] theorem XModLambdaN.map_id (coh : FunctorialCofiberCoherence Syn)
    (X : Syn) (n : ℕ) : XModLambdaN.map (𝟙 X) n = 𝟙 (XModLambdaN X n) := by
  calc
    _ = HasFunctorialCofiber.cofibMap (lambdaPow n X) (lambdaPow n X)
        (𝟙 _) (𝟙 X) (by simp) := by
      exact HasFunctorialCofiber.cofibMap_congr _ _
        ((SyntheticCategory.biShift (0, -(n : ℤ))).map_id X) rfl _ _
    _ = _ := coh.map_id (lambdaPow n X) _

theorem XModLambdaN.map_comp (coh : FunctorialCofiberCoherence Syn)
    {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    XModLambdaN.map (f ≫ g) n = XModLambdaN.map f n ≫ XModLambdaN.map g n := by
  dsimp only [XModLambdaN.map]
  simp only [Functor.map_comp]
  symm
  exact coh.map_comp (lambdaPow n X) (lambdaPow n Y) (lambdaPow n Z)
    _ f _ g _ _ _

end KIP126.Synthetic.Context
