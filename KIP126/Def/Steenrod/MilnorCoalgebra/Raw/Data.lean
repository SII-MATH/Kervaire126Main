module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Data
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
Full homogeneous Milnor coefficients, including the constant monomial.
The coproduct polynomial is the existing `splitSlot 0`; no coproduct is
chosen independently of that formula.
-/

namespace KIP126.Steenrod.Milnor.Coalgebra

noncomputable section
open KIP126.Algebra

/-- The full homogeneous component, with genuinely empty negative-degree
monomial indices. This is not the normalized one-slot cobar component. -/
abbrev Carrier (n : ℤ) := MilnorMonomial n →₀ F2

/-- One full Milnor monomial in the existing single-slot polynomial model. -/
def monomialPolynomial {n : ℤ} (m : MilnorMonomial n) : TensorPower 1 :=
  MvPolynomial.monomial
    ((slotExponentsEquiv 1).symm (fun _ => m.val)) 1

/-- Realization of the full homogeneous coefficients as actual polynomials. -/
def polynomial (n : ℤ) : Carrier n →ₗ[F2] TensorPower 1 :=
  Finsupp.linearCombination F2 monomialPolynomial

/-- The prescribed Milnor coproduct on a basis monomial, before separating
the two tensor-factor degrees. -/
def splitMonomial {n : ℤ} (m : MilnorMonomial n) : TensorPower 2 :=
  splitSlot (s := 1) 0 (monomialPolynomial m)

end
end KIP126.Steenrod.Milnor.Coalgebra
