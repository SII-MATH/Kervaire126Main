module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

namespace KIP126.Algebra.PolynomialTruncation
open MvPolynomial
noncomputable section
variable {R σ : Type*} [CommRing R] (w : σ → ℕ × ℕ)

/-- The artificial cutoff ideal, used only to compare with a truncated presentation. -/
def highIdeal (N : ℕ) : Ideal (MvPolynomial σ R) :=
  Ideal.span {p | ∃ m : σ →₀ ℕ, N < (Finsupp.weight w m).2 ∧ p = monomial m 1}

end
end KIP126.Algebra.PolynomialTruncation
