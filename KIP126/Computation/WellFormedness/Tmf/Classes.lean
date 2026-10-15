module

public import KIP126.Computation.Tmf.CsvE2.Data
public import KIP126.Def.ComputationModel.PolynomialAlgebra.HomogeneousParts
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Tactic.Ring

@[expose] public section

namespace KIP126.Classical.Adams.Tmf.CsvE2
/-- The actual quotient-ring unit has bidegree `(0,0)`. -/
theorem one_mem_homogeneousPart : (1 : E2) ∈ homogeneousPart 0 0 :=
  KIP126.Algebra.PolynomialCoordinates.one_mem generatorDegree definingIdeal

/-- Multiplication in the fixed polynomial quotient adds bidegrees.
This is a property of the displayed monomial spans, not an extra product. -/
theorem mul_mem_homogeneousPart {s t s' t' : ℕ} {x y : E2}
    (hx : x ∈ homogeneousPart s t) (hy : y ∈ homogeneousPart s' t') :
    x*y ∈ homogeneousPart (s+s') (t+t') :=
  KIP126.Algebra.PolynomialCoordinates.multiply_mem generatorDegree definingIdeal hx hy

theorem v2SixteenValue_mem : v2SixteenValue ∈ homogeneousPart 16 112 := by
  apply Submodule.subset_span
  refine ⟨Finsupp.single 12 2, ?_, ?_⟩
  · norm_num [monomialDegree, generatorDegree, Finsupp.sum_single_index]
    decide
  · simp [v2SixteenValue, generator, ← map_pow, MvPolynomial.X_pow_eq_monomial]

theorem betaFiveGValue_mem : betaFiveGValue ∈ homogeneousPart 19 114 := by
  apply Submodule.subset_span
  refine ⟨Finsupp.single 7 5 + Finsupp.single 9 1, ?_, ?_⟩
  · norm_num [monomialDegree, Finsupp.sum_add_index', add_mul, generatorDegree]
    decide
  · change projection (MvPolynomial.X 7) ^ 5 * projection (MvPolynomial.X 9) = _
    rw [← map_pow, ← map_mul, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]

/-- The source expression has bidegree (19,114) directly from its monomial. -/
theorem betaGFourValue_mem : betaGFourValue ∈ homogeneousPart 19 114 := by
  apply Submodule.subset_span
  refine ⟨Finsupp.single 7 1 + Finsupp.single 9 4, ?_, ?_⟩
  · norm_num [monomialDegree, Finsupp.sum_add_index', add_mul, generatorDegree]
    decide
  · change projection (MvPolynomial.X 7) * projection (MvPolynomial.X 9) ^ 4 = _
    rw [← map_pow, ← map_mul, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]

end KIP126.Classical.Adams.Tmf.CsvE2
