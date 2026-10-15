module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra
open scoped TensorProduct DirectSum

set_option backward.isDefEq.respectTransparency false

theorem cochainsWordEquiv_apply {s t : ℕ} (x : cochains s t)
    (d : CochainMonomial s t) :
    cochainsWordEquiv s t x (cochainMonomialEquivWord s t d) =
      MvPolynomial.coeff d.val x.val := by
  simp [cochainsWordEquiv, cochainsMonomialEquiv_apply]

/-- Tensor basis vectors become the concatenated word, with product coefficient. -/
theorem wordTensorEquiv_single (s : ℕ) (t i : ℤ) (a : PositiveMonomial i)
    (d : MilnorWord s (t - i)) (r q : F2) :
    wordTensorEquiv s t
      (DirectSum.lof F2 ℤ
        (fun j => (PositiveMonomial j →₀ F2) ⊗[F2] (MilnorWord s (t - j) →₀ F2)) i
        (Finsupp.single a r ⊗ₜ[F2] Finsupp.single d q)) =
      Finsupp.single (wordConsEquiv s t ⟨i, a, d⟩) (r * q) := by
  classical
  simp only [wordTensorEquiv, LinearEquiv.trans_apply, DirectSum.coe_congrLinearEquiv,
    DirectSum.lmap_lof, LinearEquiv.coe_coe, finsuppTensorFinsuppLid_single_tmul_single,
    smul_eq_mul]
  have h : (sigmaFinsuppLequivDFinsupp F2).symm
      (DFinsupp.single i (Finsupp.single (a, d) (r * q))) =
        Finsupp.single (⟨i, a, d⟩ : Σ j : ℤ, PositiveMonomial j × MilnorWord s (t - j))
          (r * q) := by
    apply (sigmaFinsuppLequivDFinsupp F2).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (sigmaFinsuppEquivDFinsupp_single
      (⟨i, a, d⟩ : Σ j : ℤ, PositiveMonomial j × MilnorWord s (t - j)) (r * q)).symm
  change (Finsupp.domLCongr (wordConsEquiv s t))
    ((sigmaFinsuppLequivDFinsupp F2).symm
      (DFinsupp.single i (Finsupp.single (a, d) (r * q)))) = _
  rw [h, Finsupp.domLCongr_single]

end

end KIP126.Steenrod.Milnor
