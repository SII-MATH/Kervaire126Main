module

public import KIP126.Def.Steenrod.MilnorCobar.Data
public import Mathlib.Algebra.MvPolynomial.Coeff

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra MvPolynomial
open scoped BigOperators

/-- Keep only ξ₁ in each tensor slot, killing all higher Milnor generators. -/
def xiOneProjection (s : ℕ) : TensorPower s →ₐ[F2] MvPolynomial (Fin s) F2 :=
  MvPolynomial.aeval fun a => if a.2 = 0 then MvPolynomial.X a.1 else 0

/-- The seven pure ξ₁ coefficients used to test the degree-128 square.
Their right-slot exponents are 1, 2, 4, 8, 16, 32, and 64. -/
def h6SquarePureDetector : MvPolynomial (Fin 2) F2 →ₗ[F2] F2 :=
  ∑ i ∈ Finset.range 7,
    MvPolynomial.lcoeff F2 (Finsupp.single 0 (128 - 2 ^ i) + Finsupp.single 1 (2 ^ i))

/-- The detector acts on the original two-slot polynomial model. -/
def h6SquareDetector : TensorPower 2 →ₗ[F2] F2 :=
  h6SquarePureDetector.comp (xiOneProjection 2).toLinearMap

end
end KIP126.Steenrod.Milnor
