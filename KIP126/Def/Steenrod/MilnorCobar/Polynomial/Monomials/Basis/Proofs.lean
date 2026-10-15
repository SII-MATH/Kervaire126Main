module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Basis.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra MvPolynomial

theorem cochainsMonomialEquiv_apply {s t : ℕ} (x : cochains s t)
    (d : CochainMonomial s t) :
    cochainsMonomialEquiv s t x d = coeff d.val x.val := rfl

theorem cochainsMonomialEquiv_monomial {s t : ℕ} (d : CochainMonomial s t)
    (r : F2) :
    cochainsMonomialEquiv s t ⟨monomial d.val r, monomial_mem_cochains d.val d.property r⟩ =
      Finsupp.single d r := by
  classical
  ext e
  simp [cochainsMonomialEquiv_apply, coeff_monomial, Finsupp.single_apply,
    Subtype.ext_iff]

/-- A basis vector is the corresponding monomial, with no unspecified change of basis. -/
theorem cochainsMonomialBasis_val {s t : ℕ} (d : CochainMonomial s t) :
    (cochainsMonomialBasis s t d).val = monomial d.val 1 := by
  classical
  have h : cochainsMonomialBasis s t d =
      ⟨monomial d.val 1, monomial_mem_cochains d.val d.property 1⟩ := by
    apply (cochainsMonomialEquiv s t).injective
    change cochainsMonomialEquiv s t ((cochainsMonomialEquiv s t).symm _) = _
    rw [LinearEquiv.apply_symm_apply, cochainsMonomialEquiv_monomial]
  exact congrArg Subtype.val h

end

end KIP126.Steenrod.Milnor
