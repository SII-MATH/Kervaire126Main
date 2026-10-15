module

public import KIP126.Def.Synthetic.Context.LambdaPowers.Proofs

@[expose] public section

/-! Actual maps on the already chosen finite λ-power cofibers. -/

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

noncomputable def XModLambdaN.incl (X : Syn) (n : ℕ) : X ⟶ XModLambdaN X n :=
  HasFunctorialCofiber.cofibι (lambdaPow n X)

noncomputable def XModLambdaN.proj (X : Syn) (n : ℕ) :
    XModLambdaN X n ⟶ ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)⟦(1 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ (lambdaPow n X)

/-- The map supplied by the same chosen cofiber construction. No identity
or composition law for this choice is asserted by the minimal cofiber class. -/
noncomputable def XModLambdaN.map {X Y : Syn} (f : X ⟶ Y) (n : ℕ) :
    XModLambdaN X n ⟶ XModLambdaN Y n :=
  HasFunctorialCofiber.cofibMap (lambdaPow n X) (lambdaPow n Y)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map f) f (lambdaPow_naturality n f)

/-- This is the actual λⁿ cofiber triangle. The definition makes no
inverse-limit or completeness assertion. -/
noncomputable def XModLambdaN.cofiberTriangle (X : Syn) (n : ℕ) : Triangle Syn :=
  Triangle.mk (lambdaPow n X) (XModLambdaN.incl X n) (XModLambdaN.proj X n)

end KIP126.Synthetic.Context
