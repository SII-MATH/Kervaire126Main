module

public import KIP126.Def.Synthetic.QuotientMap.Data
public import KIP126.Def.Synthetic.Context.Proofs

@[expose] public section

/-! Naturality and local triangle laws for the specified quotient maps. -/

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

theorem XModLambdaN.incl_naturality {X Y : Syn} (f : X ⟶ Y) (n : ℕ) :
    f ≫ XModLambdaN.incl Y n = XModLambdaN.incl X n ≫ XModLambdaN.map f n :=
  HasFunctorialCofiber.cofibMap_ι (lambdaPow n X) (lambdaPow n Y)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map f) f (lambdaPow_naturality n f)

theorem XModLambdaN.cofiberTriangle_distinguished (X : Syn) (n : ℕ) :
    XModLambdaN.cofiberTriangle X n ∈ distTriang Syn :=
  XModLambdaN.triangle_distinguished X n

end KIP126.Synthetic.Context
