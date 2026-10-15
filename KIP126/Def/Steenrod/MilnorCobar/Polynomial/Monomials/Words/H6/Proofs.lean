module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra

/-- The inverse word coordinate is the specified polynomial monomial. -/
theorem cochainsWordEquiv_symm_single_val (s t : ℕ) (d : MilnorWord s t) (r : F2) :
    ((cochainsWordEquiv s t).symm (Finsupp.single d r)).val =
      MvPolynomial.monomial ((slotExponentsEquiv s).symm d.val) r := by
  let m := (cochainMonomialEquivWord s t).symm d
  have he : (cochainsWordEquiv s t).symm (Finsupp.single d r) =
      ⟨MvPolynomial.monomial m.val r, monomial_mem_cochains m.val m.property r⟩ := by
    apply (cochainsWordEquiv s t).injective
    rw [LinearEquiv.apply_symm_apply]
    simp [cochainsWordEquiv, cochainsMonomialEquiv_monomial, m]
  exact congrArg Subtype.val he

theorem h6MilnorWord_exponents :
    (slotExponentsEquiv 1).symm h6MilnorWord.val = Finsupp.single (0, 0) 64 := by
  apply (slotExponentsEquiv 1).injective
  rw [Equiv.apply_symm_apply]
  funext i
  fin_cases i
  ext j
  simp [slotExponentsEquiv, h6MilnorWord, wordConsEquiv, h6PositiveMonomial,
    Finsupp.single_apply]

theorem h6SquareMilnorWord_exponents :
    (slotExponentsEquiv 2).symm h6SquareMilnorWord.val =
      Finsupp.single (0, 0) 64 + Finsupp.single (1, 0) 64 := by
  apply (slotExponentsEquiv 2).injective
  rw [Equiv.apply_symm_apply]
  funext i
  fin_cases i <;> ext j <;>
    simp [slotExponentsEquiv, h6SquareMilnorWord, h6MilnorWord,
      wordConsEquiv, h6PositiveMonomial, Finsupp.single_apply]

/-- The one-slot word is exactly the existing standard h₆ cochain. -/
theorem cochainsWordEquiv_h6 :
    cochainsWordEquiv 1 64 h6Cochain = Finsupp.single h6MilnorWord 1 := by
  apply (cochainsWordEquiv 1 64).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [cochainsWordEquiv_symm_single_val, h6MilnorWord_exponents]
  simp [h6Cochain, h6Polynomial, MvPolynomial.X_pow_eq_monomial]

/-- The two-slot word is exactly the existing concatenation square cochain. -/
theorem cochainsWordEquiv_h6Square :
    cochainsWordEquiv 2 128 h6SquareCochain = Finsupp.single h6SquareMilnorWord 1 := by
  apply (cochainsWordEquiv 2 128).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [cochainsWordEquiv_symm_single_val, h6SquareMilnorWord_exponents]
  simp [h6SquareCochain, cup, h6Cochain, h6Polynomial, cupPolynomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.rename_monomial, MvPolynomial.monomial_mul]

end
end KIP126.Steenrod.Milnor
