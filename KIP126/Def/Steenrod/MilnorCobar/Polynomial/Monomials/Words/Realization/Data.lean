module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra

/-- Realize integer-graded word coefficients in the existing polynomial
tensor power. This changes coordinates, not the cochain model. -/
def milnorWordPolynomial (s : ℕ) (t : ℤ) :
    (MilnorWord s t →₀ F2) →ₗ[F2] TensorPower s :=
  Finsupp.linearCombination F2
    (fun d => MvPolynomial.monomial ((slotExponentsEquiv s).symm d.val) 1)

end
end KIP126.Steenrod.Milnor
