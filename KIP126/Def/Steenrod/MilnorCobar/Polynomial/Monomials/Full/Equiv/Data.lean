module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Proofs
public import Mathlib.LinearAlgebra.Finsupp.Pi

@[expose] public section

namespace KIP126.Steenrod.Milnor

open KIP126.Algebra

noncomputable section

/-- Away from degree zero every monomial is a positive monomial. -/
def milnorMonomialEquivPositive (n : ℤ) (hn : n ≠ 0) :
    MilnorMonomial n ≃ PositiveMonomial n where
  toFun d := ⟨d.val, d.property, milnorMonomial_ne_zero hn d⟩
  invFun d := ⟨d.val, d.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The degree-zero full monomial space is precisely its constant coefficient. -/
def milnorZeroCoefficientsEquiv : (MilnorMonomial 0 →₀ F2) ≃ₗ[F2] F2 :=
  letI : Subsingleton (MilnorMonomial 0) :=
    ⟨fun d e => (milnorMonomial_zero_eq d).trans (milnorMonomial_zero_eq e).symm⟩
  Finsupp.uniqueLinearEquiv F2 F2 zeroMilnorMonomial

end

end KIP126.Steenrod.Milnor
