module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Binomial.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Projection.Monomials.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Basis.Proofs

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra MvPolynomial

/-- Every degree-128 monomial is annihilated after the actual polynomial
cobar differential: higher generators disappear, and the two-generator
case is the proved binomial cancellation. -/
theorem h6SquareDetector_differential_monomial (d : (Fin 1 × ℕ) →₀ ℕ)
    (hd : Finsupp.weight weight d = 128) :
    h6SquareDetector (differentialPolynomial 1 (MvPolynomial.monomial d 1)) = 0 := by
  classical
  rw [h6SquareDetector_differential]
  by_cases hh : ∃ j, 2 ≤ j ∧ d (0, j) ≠ 0
  · obtain ⟨j, hj, hdj⟩ := hh
    rw [xiOneProjection_split_monomial_high d 1 j hj hdj, map_zero]
  · have hlo : ∀ j, 2 ≤ j → d (0, j) = 0 := by
      simpa only [not_exists, not_and, not_not] using hh
    have he := singleSlot_exponents_eq_two d hlo
    have hdegree : d (0, 0) + 3 * d (0, 1) = 128 := by
      exact (singleSlot_two_weight _ _).symm.trans ((congrArg (Finsupp.weight weight) he).symm.trans hd)
    rw [he, xiOneProjection_split_monomial_two]
    exact h6SquarePureDetector_binomial _ _ hdegree

/-- The seven-coefficient detector vanishes on all incoming normalized
cobar boundaries, not merely on selected computation-table entries. -/
theorem h6SquareDetector_differential_zero (b : cochains 1 128) :
    h6SquareDetector (differential 1 128 b).val = 0 := by
  let f := h6SquareDetector.comp ((differentialPolynomial 1).comp (cochains 1 128).subtype)
  have h : f = 0 := by
    apply (cochainsMonomialBasis 1 128).ext
    intro d
    change h6SquareDetector (differentialPolynomial 1 (cochainsMonomialBasis 1 128 d).val) = 0
    rw [cochainsMonomialBasis_val]
    exact h6SquareDetector_differential_monomial d.val d.property.1
  exact LinearMap.congr_fun h b

/-- The specified normalized square is not a cobar boundary. This is a
pure polynomial theorem and uses no Adams or Lin comparison input. -/
theorem h6SquareCochain_not_boundary (b : cochains 1 128) :
    differential 1 128 b ≠ h6SquareCochain := by
  intro hb
  have h := h6SquareDetector_differential_zero b
  rw [hb, h6SquareDetector_square] at h
  exact one_ne_zero h

end
end KIP126.Steenrod.Milnor
