module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Realization.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Proofs
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra

theorem milnorWordPolynomial_single (s : ℕ) (t : ℤ) (d : MilnorWord s t) (r : F2) :
    milnorWordPolynomial s t (Finsupp.single d r) =
      MvPolynomial.monomial ((slotExponentsEquiv s).symm d.val) r := by
  simp [milnorWordPolynomial, Finsupp.linearCombination_single, MvPolynomial.smul_monomial]

/-- Distinct words have distinct slot exponents; polynomial realization
therefore loses no information at any fixed integer degree. -/
theorem milnorWordPolynomial_injective (s : ℕ) (t : ℤ) :
    Function.Injective (milnorWordPolynomial s t) := by
  have hi : Function.Injective (fun d : MilnorWord s t => (slotExponentsEquiv s).symm d.val) := by
    intro a b h
    exact Subtype.ext ((slotExponentsEquiv s).symm.injective h)
  exact ((MvPolynomial.basisMonomials (Fin s × ℕ) F2).linearIndependent.comp _ hi).finsuppLinearCombination_injective

/-- At natural internal degrees this is exactly the inverse word coordinate
of the original normalized polynomial cochains, followed by inclusion. -/
theorem milnorWordPolynomial_eq_cochainsWordEquiv_symm (s t : ℕ)
    (z : MilnorWord s t →₀ F2) :
    milnorWordPolynomial s t z = ((cochainsWordEquiv s t).symm z).val := by
  have h : milnorWordPolynomial s t =
      (cochains s t).subtype.comp (cochainsWordEquiv s t).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro d r
    exact (milnorWordPolynomial_single s t d r).trans
      (cochainsWordEquiv_symm_single_val s t d r).symm
  exact LinearMap.congr_fun h z

end
end KIP126.Steenrod.Milnor
