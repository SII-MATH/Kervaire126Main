module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Projection.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Predicates

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra MvPolynomial
open scoped BigOperators

/-- A source containing a higher Milnor generator contributes no pure-ξ₁
term to the coproduct. -/
theorem xiOneProjection_split_monomial_high (d : (Fin 1 × ℕ) →₀ ℕ)
    (r : F2) (j : ℕ) (hj : 2 ≤ j) (hd : d (0, j) ≠ 0) :
    xiOneProjection 2 (splitSlot (0 : Fin 1) (MvPolynomial.monomial d r)) = 0 := by
  rw [MvPolynomial.monomial_eq, map_mul, map_mul, Finsupp.prod, map_prod, map_prod]
  have hzero : (∏ a ∈ d.support,
      xiOneProjection 2 (splitSlot (0 : Fin 1) (MvPolynomial.X a ^ d a))) = 0 := by
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hd)
    rw [map_pow, map_pow, xiOneProjection_split_X]
    simp [show j ≠ 0 by omega, show j ≠ 1 by omega, zero_pow hd]
  rw [hzero, mul_zero]

/-- With no higher generator, a one-slot exponent vector has exactly its
ξ₁ and ξ₂ components. -/
theorem singleSlot_exponents_eq_two (d : (Fin 1 × ℕ) →₀ ℕ)
    (hd : ∀ j, 2 ≤ j → d (0, j) = 0) :
    d = Finsupp.single (0, 0) (d (0, 0)) + Finsupp.single (0, 1) (d (0, 1)) := by
  ext ⟨slot, j⟩
  have hs : slot = 0 := Subsingleton.elim _ _
  subst slot
  rcases j with _ | (_ | j)
  · simp
  · simp
  · simp [hd (j + 1 + 1) (by omega)]

/-- The remaining source monomial has the explicitly specified binomial
projection of its coproduct. -/
theorem xiOneProjection_split_monomial_two (a b : ℕ) :
    xiOneProjection 2 (splitSlot (0 : Fin 1)
      (MvPolynomial.monomial (Finsupp.single (0, 0) a + Finsupp.single (0, 1) b) 1)) =
      ((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) F2) ^ a) *
        (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) ^ b := by
  have hm : (MvPolynomial.monomial (Finsupp.single ((0 : Fin 1), 0) a +
      Finsupp.single (0, 1) b) (1 : F2)) = MvPolynomial.X (0, 0) ^ a * MvPolynomial.X (0, 1) ^ b := by
    simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
  rw [hm, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
  simp [xiOneProjection_split_X]

theorem singleSlot_two_weight (a b : ℕ) :
    Finsupp.weight (weight (s := 1))
      (Finsupp.single (0, 0) a + Finsupp.single (0, 1) b) = a + 3 * b := by
  simp [Finsupp.weight_single, weight, mul_comm]

end
end KIP126.Steenrod.Milnor
