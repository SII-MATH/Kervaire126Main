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

private theorem high_frame :
    ∀ e : (model.family.sphere.sequence.ssData (25,150,130)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (25,150,130)
        (model.comparison.sphereE2 25 150 20 KIP126.Computation.Standard.highClass) e := by
  obtain ⟨z,hz,_⟩ := high_nonzero_survival
  obtain ⟨a,ha,_,hall⟩ := KIP126.Computation.Standard.high_e5
  exact sphere_frame_of_permanent_quotient 25 150 20 KIP126.Computation.Standard.highClass
    (permanent_quotient_frame_of_page 5 21 (by decide) (by decide) 25 150 _ ⟨z,hz⟩ a ha hall)

private theorem high_exhaustion
    (b : BiHom 125 150 (S_0_0 : SyntheticSpectrum))
    (hb : sphereFirstQuotient model 25 150 (quotientClass 1 b)=KIP126.Computation.Standard.highClass)
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 15 a) :
    a=0 ∨ a=lambdaMultiply 20 b := by
  have h25 := synthetic_filtration_fifteen_to_twentyfive a ha
  rcases theta_detection_step (25,150,130) _ high_frame a h25 with hd|h26
  · right
    have hb' := model.sphereDetectionCompatible.homotopy_lambda 25 150 20 b
    change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
      model.firstQuotient 25 150 (quotientClass 1 b)=_ at hb
    rw [hb] at hb'
    apply sub_eq_zero.mp
    exact synthetic_filtration26_zero _
      (detects_sub_filtration (model.convergence .sphere) (25,150,130) hd.1 hb')
  · exact Or.inl (synthetic_filtration26_zero a h26)

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
    (hz : a ≫ detectorMap=0) : a=0 := by
  obtain ⟨b0,hb0,hreal⟩ := Standard.selected_realization_prescribed_lift .sphere 25 150
    KIP126.Computation.Standard.highClass Standard.high125 high_nonzero_survival source_high_detected
  let f := SyntheticCategory.biShift_zero.hom.app (model.nu.functor.obj SphereSpectrum) ≫ model.nu.unitIso.hom
  let b : BiHom 125 150 (S_0_0 : SyntheticSpectrum) := b0 ≫ f
  have hb : sphereFirstQuotient model 25 150 (quotientClass 1 b)=KIP126.Computation.Standard.highClass := by
    have hc : quotientClass 1 b=quotientClass 1 b0 ≫ XModLambdaN.map f 1 := by
      unfold quotientClass
      simp only [b,Category.assoc]
      exact congrArg (fun h => b0 ≫ h) (XModLambdaN.incl_naturality f 1)
    rw [hc,hb0]
    exact KIP126.ProofTools.Operations.sphere_first_quotient_label 25 150 _
  rcases high_exhaustion b hb a ha with h0|h1
  · exact h0
  · have hr : Standard.realizeSphere 125 130 a=Standard.high125 := by
      rw [h1]
      exact (realize_lambda 20 b).trans ((realize_lift b0).trans hreal)
    have hzero := realize_detector_zero a hz
    rw [hr] at hzero
    exact False.elim (high_detected_detector_nonzero _ source_high_detected hzero)

end
end KIP126.Main.Internal.High125
