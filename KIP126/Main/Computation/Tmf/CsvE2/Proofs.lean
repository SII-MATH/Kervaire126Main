module

public import KIP126.Computation.Tmf.CsvE2.Data
public import KIP126.Computation.WellFormedness.Tmf.Classes
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Tactic.Ring

@[expose] public section

namespace KIP126.Classical.Adams.Tmf.CsvE2
private instance polyCharTwo : CharP Poly 2 :=
  CharP.of_ringHom_of_ne_zero
    (MvPolynomial.C : KIP126.Algebra.F2 →+* Poly) 2 (by decide)

private theorem relation_mem (terms : List (List (Generator × ℕ)))
    (h : terms ∈ relationPowers) : relationPolynomial terms ∈ definingIdeal :=
  Ideal.subset_span ⟨terms, h, rfl⟩

/-- The archived relation g²=βγ, also BR21 Table 3.4 / Table 3.5. -/
theorem g_square_eq_beta_gamma : generator 9 ^ 2 = generator 7 * generator 10 := by
  have h := relation_mem [[(9, 2)], [(7, 1), (10, 1)]] (by decide)
  change projection (MvPolynomial.X 9 ^ 2) =
    projection (MvPolynomial.X 7 * MvPolynomial.X 10)
  apply Ideal.Quotient.eq.mpr
  simpa [relationPolynomial, polynomialOfPowers, CharTwo.sub_eq_add] using h

/-- The archived relation gγ=β³, also BR21 Table 3.4 / Table 3.5. -/
theorem g_gamma_eq_beta_cube : generator 9 * generator 10 = generator 7 ^ 3 := by
  have h := relation_mem [[(9, 1), (10, 1)], [(7, 3)]] (by decide)
  change projection (MvPolynomial.X 9 * MvPolynomial.X 10) =
    projection (MvPolynomial.X 7 ^ 3)
  apply Ideal.Quotient.eq.mpr
  simpa [relationPolynomial, polynomialOfPowers, CharTwo.sub_eq_add] using h

/-- An equality in the actual fixed quotient, not an equality of class names. -/
theorem g_cube_eq_beta_four : generator 9 ^ 3 = generator 7 ^ 4 := by
  calc
    generator 9 ^ 3 = generator 7 * (generator 9 * generator 10) := by
      rw [pow_succ, g_square_eq_beta_gamma]
      ring
    _ = generator 7 ^ 4 := by rw [g_gamma_eq_beta_cube]; ring

/-- Converts BR21's βg⁴ to the selected β⁵g using the exact quotient relations. -/
theorem betaGFourValue_eq_betaFiveGValue : betaGFourValue = betaFiveGValue := by
  unfold betaGFourValue betaFiveGValue
  calc
    generator 7 * generator 9 ^ 4 = generator 7 * (generator 9 ^ 3 * generator 9) := by ring
    _ = generator 7 ^ 5 * generator 9 := by rw [g_cube_eq_beta_four]; ring


end KIP126.Classical.Adams.Tmf.CsvE2
