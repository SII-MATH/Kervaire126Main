module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data
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

end
end KIP126.Steenrod.Milnor
