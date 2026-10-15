module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Parity.Proofs

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra MvPolynomial
open scoped BigOperators

/-- Pure ξ₁ coproduct coefficients of ξ₁ᵃξ₂ᵇ are the expected shifted
binomial coefficients, including sources too large for either target slot. -/
theorem h6Square_binomial_coefficient (a b j : ℕ) (hdegree : a + 3 * b = 128)
    (hj : j ≤ 128) :
    coeff (Finsupp.single 0 (128 - j) + Finsupp.single 1 j)
      (((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) F2) ^ a) *
        (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) ^ b) =
      if b ≤ j then (a.choose (j - b) : F2) else 0 := by
  have hm : ((MvPolynomial.X 0 : MvPolynomial (Fin 2) F2) ^ 2 * MvPolynomial.X 1) ^ b =
      MvPolynomial.monomial (Finsupp.single 0 (2 * b) + Finsupp.single 1 b) 1 := by
    rw [mul_pow, ← pow_mul, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  rw [hm, MvPolynomial.coeff_mul_monomial']
  simp only [MvPolynomial.coeff_add_pow]
  simp only [Finsupp.le_def, Fin.forall_fin_two, Finsupp.tsub_apply,
    Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add,
    Finset.mem_antidiagonal, mul_one]
  by_cases hb : b ≤ j
  · rw [if_pos hb]
    by_cases hl : 2 * b ≤ 128 - j
    · rw [if_pos ⟨hl, hb⟩, if_pos (by omega)]
      exact congrArg (fun k : ℕ => (k : F2)) (Nat.choose_symm_of_eq_add (by omega))
    · rw [if_neg (by tauto), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  · rw [if_neg hb, if_neg (by tauto)]

/-- The detector vanishes on every degree-128 monomial's possible
pure-ξ₁ coproduct contribution. This is a proved finite arithmetic reduction. -/
theorem h6SquarePureDetector_binomial (a b : ℕ) (hdegree : a + 3 * b = 128) :
    h6SquarePureDetector
      (((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) F2) ^ a) *
        (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) ^ b) = 0 := by
  rw [h6SquarePureDetector_apply]
  have h : (∑ i ∈ Finset.range 7,
      coeff (Finsupp.single 0 (128 - 2 ^ i) + Finsupp.single 1 (2 ^ i))
        (((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) F2) ^ a) *
          (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) ^ b)) =
      ∑ i ∈ Finset.range 7, if b ≤ 2 ^ i then (a.choose (2 ^ i - b) : F2) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply h6Square_binomial_coefficient a b _ hdegree
    exact le_of_lt (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (Finset.mem_range.mp hi))
  rw [h]
  have ha : a = 128 - 3 * b := by omega
  subst a
  exact h6Square_binomial_parity ⟨b, by omega⟩

end
end KIP126.Steenrod.Milnor
