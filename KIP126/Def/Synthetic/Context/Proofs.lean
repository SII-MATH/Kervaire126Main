module

public import KIP126.Def.Synthetic.Context.Data

@[expose] public section

/-! Derived distinguished-triangle facts for synthetic λ-quotients. -/
namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy

universe u v u' v'

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The λⁿ cofiber triangle is distinguished. -/
theorem XModLambdaN.triangle_distinguished (X : Syn) (n : ℕ) :
    Triangle.mk (lambdaPow n X)
      (HasFunctorialCofiber.cofibι (lambdaPow n X))
      (HasFunctorialCofiber.cofibδ (lambdaPow n X)) ∈ distTriang Syn :=
  HasFunctorialCofiber.cofib_distinguished (lambdaPow n X)

end KIP126.Synthetic.Context
