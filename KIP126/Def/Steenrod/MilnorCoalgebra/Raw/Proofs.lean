module

public import KIP126.Def.Steenrod.MilnorCoalgebra.Raw.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Grading.Proofs

@[expose] public section

namespace KIP126.Steenrod.Milnor.Coalgebra

/-- Every actual term of the Milnor coproduct has the original total
degree. The construction of the graded coproduct uses all these terms. -/
theorem splitMonomial_support_degree {n : ℤ} (m : MilnorMonomial n)
    (d : (Fin 2 × ℕ) →₀ ℕ) (hd : d ∈ (splitMonomial m).support) :
    (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) +
      (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) = n := by
  have hm : MvPolynomial.IsWeightedHomogeneous weight (monomialPolynomial m)
      (slotWeight m.val) := by
    apply MvPolynomial.isWeightedHomogeneous_monomial
    simp [weight_eq_sum_slotWeight]
  have hs := homogeneous_splitSlot (0 : Fin 1) hm
  have he := hs (MvPolynomial.mem_support_iff.mp hd)
  have he' : slotWeight (slotExponentsEquiv 2 d 0) +
      slotWeight (slotExponentsEquiv 2 d 1) = slotWeight m.val := by
    simpa [weight_eq_sum_slotWeight, Fin.sum_univ_two] using he
  exact (by exact_mod_cast he' :
    (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) +
      (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) = (slotWeight m.val : ℤ)).trans m.property

end KIP126.Steenrod.Milnor.Coalgebra
