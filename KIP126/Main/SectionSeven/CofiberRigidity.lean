module
import all KIP126.Main.SectionSeven.Predicates

import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.Internal.CofiberRigidity

/-! The final Cν rigidity step in LWX Proposition 7.9.
Adapted from Kervaire126 bbac1fc05843,
Main/Solution/Route/Section7/CnuRigidity.lean (MIT; see the retained source LICENSE).
The representative comparison, actual λν zero composite and contradiction
are retained as proofs using the fixed upstream interfaces. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Core.SpectralSequence
open KIP126.Computation.Standard (T nuCofiberSequence bottom)
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Paper-local specialization of BHS: the actual bottom-cell image
survives to E₆, so λ⁴ times the image of this detected representative is
nonzero. The old proof compares actual quotient representatives with B₅.
The finite survival and BHS comparison are fixed upstream interfaces. -/
private theorem detected_target_bottom_lambda_four_nonzero
    (t : BiHom 125 139 (S_0_0 : SyntheticSpectrum))
    (ht : SphereDetected 14 139 0 T t) :
    lambdaMultiply 4 t ≫ nuBottom ≠ 0 := by
  have hlabel := Internal.Rigidity.sphere_zero_weight_label_14_139 T t ht.1
  have hd := model.sphereDetectionCompatible.homotopy_lambda 14 139 4 t
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hlabel
  rw [hlabel] at hd
  have hm := KIP126.ProofTools.Internal.detects_map .sphere (.nu .nuCofiber) nuBottom
    (14,139,135) (model.comparison.sphereE2 14 139 4 T) (lambdaMultiply 4 t) hd
  have hl := Internal.Rigidity.sphere_to_nu_label .nuCofiber
    (HasFunctorialCofiber.cofibι model.auxiliary.nuMap) T
  change KIP126.Synthetic.SpectralSequence.familyPageMap model.family nuBottom 2 (14,139,135)
    (model.comparison.sphereE2 14 139 4 T) = _ at hl
  erw [hl] at hm
  intro hz
  rw [hz] at hm
  obtain ⟨e,he,a',ha',hgr⟩ := hm
  have hne := Internal.Rigidity.nu_lambda_four_infinity_nonzero .nuCofiber _
    KIP126.Computation.Standard.cofiber_target_to_e6 e he
  apply hne
  have ha0 : a'=0 := by
    apply (ModuleCat.mono_iff_injective
      ((model.syntheticTower.filtration ((KIP126.Kervaire.Route.SyntheticObject.nu .nuCofiber).obj
        model.nu model.auxiliary)).F 14 (139-14,135)).arrow).mp inferInstance
    simpa only [map_zero] using ha'
  apply (ModuleCat.mono_iff_injective ((model.convergence (.nu .nuCofiber)).identification
    (14,139,135)).hom).mp inferInstance
  rw [hgr,ha0,map_zero,map_zero]

/-- The exact λν equation contradicts that nonzero bottom-cell image. -/
private theorem target_divisibility_contradiction : ¬ TargetNuDivisible T hopfNu := by
  rintro ⟨t, a, ht, heq⟩
  apply detected_target_bottom_lambda_four_nonzero t ht
  rw [← heq]
  exact lambda_nu_multiple_bottom_zero a

/-- The original last-step formulation exposes the finite incoming window
2..5 on the same actual Cν class. It makes no permanence assertion about Cν. -/
private theorem target_divisibility_forces_cnu_incoming
    (hdiv : TargetNuDivisible T hopfNu) :
    ∃ r : ℤ, 2 ≤ r ∧ r ≤ 5 ∧
      HitOnPage nuCofiberSequence r (14,139) (bottom 14 139 T) := by
  exact False.elim (target_divisibility_contradiction hdiv)

end
end KIP126.Main.SectionSeven
