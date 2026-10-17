module
import all KIP126.Main.Internal.Theta.RealizationKernel
import all KIP126.Main.Internal.Choice.OrderTwo
/-! Original exponent-two consequence in weight 70, Lambda.lean:116–140
and 1426–1460, bbac1fc05843 (MIT). No lambda injectivity in this
weight is assumed: the preceding proved filtered kernel descent is used. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Literature KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive :=
  KIP126.AdamsSynthetic.Standard.graded_shiftAdditive p
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem lambda_h0_map_zero_iff
    {T : Type*} [Category T] [Preadditive T] (R : SyntheticSpectrum ⥤ T) [R.Additive]
    (coh : BiShiftCoherence SyntheticSpectrum) (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (hlambda : lambdaMultiply 1 h0 = KIP126.Literature.Route.syntheticTwo)
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum)) :
    R.map (lambdaMultiply 1 (sphereProduct h0 b)) = 0 ↔ R.map (b+b) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (62,70)
    have ht : R.map (F.map (lambdaMultiply 1 h0) ≫ b) = 0 ↔
        R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫ R.map (F.map h0) ≫ R.map b = 0 := by
      simp only [lambdaMultiply, lambdaPow_one coh, F, eqToHom_refl,
        Functor.map_comp, Category.id_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    simp only [lambdaMultiply, lambdaPow_one coh, eqToHom_refl,
      Functor.map_comp, Category.id_comp, Limits.comp_eq_zero_iff_of_epi]
    dsimp only [sphereProduct]
    have hn := SyntheticCategory.lam.naturality
      ((SyntheticCategory.biShift_comp (0,1) (62,70)).inv.app (S_0_0 : SyntheticSpectrum))
    simp only [Prod.mk_add_mk, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    erw [← hn]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    erw [coh.lambda_comm (62,70) (Smn 0 1)]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    change R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫
      R.map (F.map h0) ≫ R.map b = 0 ↔ _
    rw [← ht, hlambda]
    simp only [KIP126.Literature.Route.syntheticTwo, Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add,
      Category.assoc, Preadditive.add_comp,
      ← Preadditive.comp_add, Limits.comp_eq_zero_iff_of_epi]

private theorem two_torsion_62_70 (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum)) : b + b = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    letI := Choice.realization_additive
    have hb : model.recovery.realization.map (b+b) = 0 := by
      rw [Functor.map_add]
      let α : HomotopyGroup (C := Spectrum) 62 SphereSpectrum :=
        (KIP126.Literature.Standard.realization_sphere 62 70).hom ≫ model.recovery.realization.map b ≫
          model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum
      have h := KIP126.Literature.Standard.stem62_exponent_two α
      apply (cancel_epi (KIP126.Literature.Standard.realization_sphere 62 70).hom).mp
      apply (cancel_mono (model.recovery.realization.map model.nu.unitIso.inv)).mp
      apply (cancel_mono ((model.recovery.nuRealizationIso.app SphereSpectrum).hom)).mp
      erw [Preadditive.comp_add, Preadditive.add_comp, Preadditive.add_comp,
        Limits.comp_zero, Limits.zero_comp, Limits.zero_comp]
      repeat erw [Category.assoc]
      exact h
    have hl := (lambda_h0_map_zero_iff model.recovery.realization model.quotients.coherence
      KIP126.Literature.Standard.syntheticH0 KIP126.Literature.Standard.toda_lambda_h0 b).mpr hb
    have hp : model.recovery.realization.map (sphereProduct KIP126.Literature.Standard.syntheticH0 b) = 0 := by
      have hm : lambdaMultiply 1 (sphereProduct KIP126.Literature.Standard.syntheticH0 b) =
          lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) 62 71)) ≫ sphereProduct KIP126.Literature.Standard.syntheticH0 b := by
        simp only [lambdaMultiply, Category.assoc, Category.id_comp]
        rfl
      have hc := congrArg (fun z => (KIP126.Literature.Standard.realization_sphere 62 70).hom ≫ z) hl
      rw [hm, Functor.map_comp, ← Category.assoc] at hc
      erw [KIP126.Literature.Standard.realization_lambda 62 71 1] at hc
      exact (Limits.comp_eq_zero_iff_of_epi (KIP126.Literature.Standard.realization_sphere 62 71).hom).mp
        (by simpa only [Limits.comp_zero] using hc)
    have hk := lambda_kills_realization_kernel_62_71 (sphereProduct KIP126.Literature.Standard.syntheticH0 b) hp
    exact (lambda_h0_map_zero_iff (𝟭 SyntheticSpectrum) model.quotients.coherence KIP126.Literature.Standard.syntheticH0 KIP126.Literature.Standard.toda_lambda_h0 b).mp hk

end
end KIP126.Main.Internal.Theta
