module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.High125.Source
import all KIP126.Main.Internal.High125.Detector
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.DetectionOperations
/-! The original Main high-filtration tmf argument (Computation/High125 and
Computation/Lambda, bbac1fc05843, MIT). The repeated infinity-frame algebra
is shared with Selected. All source computation and realization inputs are
called on the fixed system; no Main result is supplied as an extra input. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Literature KIP126.Main.Internal.Selected
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The sourced h₀η null-product and λh₀=2 imply genuine order two on
η itself.  Consequently each actual η-product used by the paper, including
the difference between two choices, has no odd-primary ambiguity. -/
local instance high125_shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive :=
  KIP126.AdamsSynthetic.Standard.graded_shiftAdditive p

private theorem lambda_h0_map_zero_iff
    {T : Type*} [Category T] [Preadditive T] (R : SyntheticSpectrum ⥤ T) [R.Additive]
    (coh : BiShiftCoherence SyntheticSpectrum) (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (hlambda : lambdaMultiply 1 h0 = KIP126.Literature.Route.syntheticTwo)
    (b : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) :
    R.map (lambdaMultiply 1 (sphereProduct h0 b)) = 0 ↔ R.map (b+b) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (1,2)
    have ht : R.map (F.map (lambdaMultiply 1 h0) ≫ b) = 0 ↔
        R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫ R.map (F.map h0) ≫ R.map b = 0 := by
      simp only [lambdaMultiply, lambdaPow_one coh, F, eqToHom_refl,
        Functor.map_comp, Category.id_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    simp only [lambdaMultiply, lambdaPow_one coh, eqToHom_refl,
      Functor.map_comp, Category.id_comp, Limits.comp_eq_zero_iff_of_epi]
    dsimp only [sphereProduct]
    have hn := SyntheticCategory.lam.naturality
      ((SyntheticCategory.biShift_comp (0,1) (1,2)).inv.app (S_0_0 : SyntheticSpectrum))
    simp only [Prod.mk_add_mk, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    erw [← hn]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    erw [coh.lambda_comm (1,2) (Smn 0 1)]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    change R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫
      R.map (F.map h0) ≫ R.map b = 0 ↔ _
    rw [← ht, hlambda]
    simp only [KIP126.Literature.Route.syntheticTwo, Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add,
      Category.assoc, Preadditive.add_comp,
      ← Preadditive.comp_add, Limits.comp_eq_zero_iff_of_epi]


private theorem eta_order_two : KIP126.Literature.Standard.eta + KIP126.Literature.Standard.eta = 0 := by
  apply (lambda_h0_map_zero_iff (𝟭 SyntheticSpectrum) model.quotients.coherence
    KIP126.Literature.Standard.syntheticH0 KIP126.Literature.Standard.toda_lambda_h0
    KIP126.Literature.Standard.eta).mp
  rw [KIP126.Literature.Standard.toda_h0_eta]
  simp only [lambdaMultiply, comp_zero, Functor.id_map]

private theorem eta_product_order_two (m w : ℤ)
    (b : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    sphereProduct KIP126.Literature.Standard.eta b +
      sphereProduct KIP126.Literature.Standard.eta b = 0 := by
  dsimp only [sphereProduct]
  rw [←Preadditive.comp_add, ←Preadditive.add_comp, ←Functor.map_add,
    eta_order_two, Functor.map_zero, zero_comp, comp_zero]

private theorem eta_product_difference_order_two (m w : ℤ)
    (b c : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    (sphereProduct KIP126.Literature.Standard.eta b -
      sphereProduct KIP126.Literature.Standard.eta c) +
      (sphereProduct KIP126.Literature.Standard.eta b -
        sphereProduct KIP126.Literature.Standard.eta c) = 0 := by
  have hb := eta_product_order_two m w b
  have hc := eta_product_order_two m w c
  calc
    _ = (sphereProduct KIP126.Literature.Standard.eta b +
        sphereProduct KIP126.Literature.Standard.eta b) -
        (sphereProduct KIP126.Literature.Standard.eta c +
        sphereProduct KIP126.Literature.Standard.eta c) := by abel
    _ = 0 := by rw [hb,hc,sub_self]

private theorem high_frame :
    ∀ e : (model.family.sphere.sequence.ssData (25,150,130)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (25,150,130)
        (model.comparison.sphereE2 25 150 20 KIP126.Computation.Standard.highClass) e := by
  obtain ⟨z,hz,_,_,_⟩ := source_high_detected
  obtain ⟨a,ha,_,hall⟩ := KIP126.Computation.Standard.high_e5
  exact sphere_frame_of_permanent_quotient 25 150 20 KIP126.Computation.Standard.highClass
    (permanent_quotient_frame_of_page 5 21 (by decide) (by decide) 25 150 _ ⟨z,hz⟩ a ha hall)

private theorem realize_lambda {m w : ℤ} (k : ℕ)
    (b : BiHom m w (S_0_0 : SyntheticSpectrum)) :
    Standard.realizeSphere m (w-k) (lambdaMultiply k b)=Standard.realizeSphere m w b := by
  have hb : lambdaMultiply k b=lambdaMultiply k (𝟙 (Smn m w)) ≫ b := by
    simp only [lambdaMultiply,Category.comp_id,Category.assoc]
  rw [hb]
  change (Standard.realization_sphere m (w-k)).hom ≫ model.recovery.realization.map
      (lambdaMultiply k (𝟙 (Smn m w)) ≫ b) ≫ model.recovery.realization.map model.nu.unitIso.inv ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum =
    (Standard.realization_sphere m w).hom ≫ model.recovery.realization.map b ≫
      model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum
  simp only [Functor.map_comp,←Category.assoc]
  rw [Standard.realization_lambda]

private theorem realize_lift (b : BiHom 125 150 (nuZero model .sphere)) :
    Standard.realizeSphere 125 150
      (b ≫ SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom)=
        Standard.realizeNu .sphere b := by
  change (Standard.realization_sphere 125 150).hom ≫ model.recovery.realization.map
      (b ≫ SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom) ≫
      model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum =
    (Standard.realization_sphere 125 150).hom ≫ model.recovery.realization.map b ≫
      model.recovery.realization.map (SyntheticCategory.biShift_zero.hom.app _) ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum
  simp only [Functor.map_comp,Category.assoc]
  rw [←Category.assoc (model.recovery.realization.map model.nu.unitIso.hom),
    ←Functor.map_comp,Iso.hom_inv_id,CategoryTheory.Functor.map_id,Category.id_comp]

private theorem realize_detector_zero {m w : ℤ}
    (a : BiHom m w (S_0_0 : SyntheticSpectrum)) (ha : a ≫ detectorMap=0) :
    Standard.realizeSphere m w a ≫ model.auxiliary.detectorUnit=0 := by
  letI := Standard.realization_additive
  have hn := model.recovery.nuRealizationIso.hom.naturality model.auxiliary.detectorUnit
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  have hz := congrArg model.recovery.realization.map ha
  rw [Functor.map_zero] at hz
  dsimp only [detectorMap] at hz
  simp only [Functor.map_comp,Category.assoc] at hz
  change ((Standard.realization_sphere m w).hom ≫ model.recovery.realization.map a ≫
    model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum) ≫
      model.auxiliary.detectorUnit=0
  simp only [Category.assoc]
  rw [←hn]
  simpa only [Category.assoc,comp_zero,zero_comp] using
    congrArg (fun f => (Standard.realization_sphere m w).hom ≫ f ≫
      model.recovery.nuRealizationIso.hom.app model.auxiliary.detector) hz

theorem detector_injective_filtration15
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 15 a)
    (h2 : a+a=0)
    (hz : a ≫ detectorMap=0) : a=0 := by
  have hImageNonodd := Standard.tmf_high125_nonzero
  obtain ⟨b0,hb0,hreal⟩ := Standard.selected_realization_prescribed_lift .sphere 25 150
    KIP126.Computation.Standard.highClass Standard.high125
    high_nonzero_survival source_high_detected
  let f := SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj SphereSpectrum) ≫ model.nu.unitIso.hom
  let b : BiHom 125 150 (S_0_0 : SyntheticSpectrum) := b0 ≫ f
  have hb : sphereFirstQuotient model 25 150 (quotientClass 1 b)=KIP126.Computation.Standard.highClass := by
    have hc : quotientClass 1 b=quotientClass 1 b0 ≫ XModLambdaN.map f 1 := by
      unfold quotientClass
      simp only [b,Category.assoc]
      exact congrArg (fun h => b0 ≫ h) (XModLambdaN.incl_naturality f 1)
    rw [hc,hb0]
    exact KIP126.ProofTools.Operations.sphere_first_quotient_label 25 150 _
  have h25 := synthetic_filtration_fifteen_to_twentyfive a ha
  rcases theta_detection_step (25,150,130) _ high_frame a h25 with hd|h26
  · have hbdet := model.sphereDetectionCompatible.homotopy_lambda 25 150 20 b
    change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
      model.firstQuotient 25 150 (quotientClass 1 b)=_ at hb
    rw [hb] at hbdet
    have hdiff : FiltrationAtLeast model.syntheticTower 26 (a-(show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 20 b)) :=
      detects_sub_filtration (model.convergence .sphere) (25,150,130) hd.1 hbdet
    have hOdd := infinite_realization_odd _ (synthetic_filtration26_infinite _ hdiff)
    have hzero := realize_detector_zero a hz
    have hzeroTmf : Standard.realizeSphere 125 130 a ≫ Standard.tmfUnit=0 := by
      apply (cancel_mono Standard.tmfIso.hom).mp
      simpa only [Category.assoc,Standard.tmfUnit_agrees,zero_comp] using hzero
    have hr : Standard.realizeSphere 125 130 (lambdaMultiply 20 b)=Standard.high125 :=
      (realize_lambda 20 b).trans ((realize_lift b0).trans hreal)
    have hOddImage := odd_postcompose _ Standard.tmfUnit hOdd
    rw [map_sub,Preadditive.sub_comp,hzeroTmf,hr,zero_sub] at hOddImage
    exact False.elim (hImageNonodd (odd_neg _ hOddImage))
  · exact synthetic_filtration26_zero a h26 h2

end
end KIP126.Main.Internal.High125
