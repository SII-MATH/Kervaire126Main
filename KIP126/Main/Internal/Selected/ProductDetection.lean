module

public import KIP126.Main.Conditions
public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Choice.Filtration

/-! The eta-product and filtration-error arguments of Selected/DetectionData
673–845,1371–1412,1477–1515 and Assembly:158–209 at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations
open KIP126.Literature.Standard (eta)
open KIP126.Computation.Standard (U T correction)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem eta_detected : Detects (model.convergence .sphere) (1,2,2)
    (model.comparison.sphereE2 1 2 0 (model.standardClasses.standardHi 1)) eta := by
  have h := model.sphereDetectionCompatible.homotopy_lambda 1 2 0 eta
  rw [lambda_zero_1_2] at h
  have hl := KIP126.Literature.Standard.eta_label
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hl
  rw [hl] at h
  exact h

private theorem theta5_square_eta_filtration_fourteen
    (hp : KIP126.Computation.Standard.product (r := (11,136))
      KIP126.Computation.Standard.h1 U=0)
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (hc4 : Theta5SquareNonzeroDetectionAt theta) :
    FiltrationAtLeast model.syntheticTower 14 (sphereProduct eta (sphereProduct theta theta)) := by
  have hd := model.multiplicationCompatible 1 2 10 134 0 6
    (model.standardClasses.standardHi 1) U eta (sphereProduct theta theta) eta_detected hc4.1
  change Detects (model.convergence .sphere) (11,136,130)
    (model.comparison.sphereE2 11 136 6
      (KIP126.Computation.Standard.product (r := (11,136)) KIP126.Computation.Standard.h1 U))
    (sphereProduct eta (sphereProduct theta theta)) at hd
  rw [hp,map_zero] at hd
  exact stem125_filtration_twelve_to_fourteen 130 (by decide) _
    (detects_zero_filtration (model.convergence .sphere) (11,136,130) hd)

private theorem u_choice_eta_lambda_three_filtration_fourteen
    (hp : KIP126.Computation.Standard.product (r := (11,136))
      KIP126.Computation.Standard.h1 U=0)
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    FiltrationAtLeast model.syntheticTower 14 (lambdaMultiply 3 (sphereProduct eta u)) := by
  have hfirst := sphere_zero_weight_label_10_134 U u hu.1
  have hdu := model.sphereDetectionCompatible.homotopy_lambda 10 134 3 u
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hfirst
  rw [hfirst] at hdu
  have hd := model.multiplicationCompatible 1 2 10 134 0 3
    (model.standardClasses.standardHi 1) U eta (lambdaMultiply 3 u) eta_detected hdu
  change Detects (model.convergence .sphere) (11,136,133)
    (model.comparison.sphereE2 11 136 3
      (KIP126.Computation.Standard.product (r := (11,136)) KIP126.Computation.Standard.h1 U))
    (sphereProduct eta (lambdaMultiply 3 u)) at hd
  rw [hp,map_zero,eta_lambda3_right eta u] at hd
  exact stem125_filtration_twelve_to_fourteen 133 (by decide) _
    (detects_zero_filtration (model.convergence .sphere) (11,136,133) hd)

private theorem eta_weight128_branches_filtration_fifteen
    (b : BiHom 124 128 (S_0_0 : SyntheticSpectrum))
    (hbranch : DetectsNonzero (model.convergence .sphere) (13,137,128)
        (model.comparison.sphereE2 13 137 9 correction) b ∨
      ∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 10 a=b) :
    FiltrationAtLeast model.syntheticTower 15 (sphereProduct eta b) := by
  rcases hbranch with h13 | ⟨a,ha⟩
  · have hd := model.multiplicationCompatible 1 2 13 137 0 9
      (model.standardClasses.standardHi 1) correction eta b eta_detected h13.1
    change Detects (model.convergence .sphere) (14,139,130)
      (model.comparison.sphereE2 14 139 9 (KIP126.Computation.Standard.product (r := (14,139))
        KIP126.Computation.Standard.h1 correction)) (sphereProduct eta b) at hd
    rw [KIP126.Computation.Standard.h1_correction_zero,map_zero] at hd
    exact detects_zero_filtration (model.convergence .sphere) (14,139,130) hd
  · have had := model.sphereDetectionCompatible.homotopy_lambda 14 138 10 a
    rw [ha] at had
    have hd := model.multiplicationCompatible 1 2 14 138 0 10
      (model.standardClasses.standardHi 1) (sphereFirstQuotient model 14 138 (quotientClass 1 a))
      eta b eta_detected had
    change Detects (model.convergence .sphere) (15,140,130) _ (sphereProduct eta b) at hd
    obtain ⟨e,he,a',ha',hgr⟩ := hd
    rw [←ha']
    have hm : ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 15 (125,130)).arrow a' ∈
        (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : SyntheticSpectrum) (125,130)))
          ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 15 (125,130)) := ⟨a',rfl⟩
    simpa only [FiltrationAtLeast,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm

private theorem stem124_weight128_filtration11_branches
    (hframe : ∀ e : (model.family.sphere.sequence.ssData (13,137,128)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (13,137,128)
        (model.comparison.sphereE2 13 137 9 correction) e)
    (a : BiHom 124 128 (S_0_0 : SyntheticSpectrum))
    (ha11 : FiltrationAtLeast model.syntheticTower 11 a) :
    DetectsNonzero (model.convergence .sphere) (13,137,128)
        (model.comparison.sphereE2 13 137 9 correction) a ∨
      ∃ b : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 10 b=a := by
  have ha13 : FiltrationAtLeast model.syntheticTower 13 a := by
    apply (filtration_iff_of_infinity_zero (model.convergence .sphere)
      11 13 124 128 (by decide) ?_ a).mp ha11
    intro j hj hj'
    apply sphere_infinity_zero_of_permanent_quotient_zero j (124+j) 128 (by omega)
    interval_cases j
    · exact permanent_quotient_zero_of_page_zero .sphere 5 8 (by decide) (by decide) (11,135)
        KIP126.Computation.Standard.e5_stem124_af11
    · exact permanent_quotient_zero_of_page_zero .sphere 4 9 (by decide) (by decide) (12,136)
        KIP126.Computation.Standard.e4_stem124_af12
  rcases theta_detection_step (13,137,128)
    (model.comparison.sphereE2 13 137 9 correction) hframe a ha13 with hdet|ha14
  · exact Or.inl hdet
  right
  have h := KIP126.Literature.Standard.selected_filtration_lambda .sphere 124 128 14 (by decide)
    (a ≫ model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 14 (a ≫ model.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (model.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ model.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha14)
  refine ⟨b ≫ model.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ model.nu.unitIso.hom) hb

private theorem theta_u_eta_filtration_error
    (hframe : ∀ e : (model.family.sphere.sequence.ssData (13,137,128)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (13,137,128)
        (model.comparison.sphereE2 13 137 9 correction) e)
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (hc4 : Theta5SquareNonzeroDetectionAt theta)
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    FiltrationAtLeast model.syntheticTower 15
      ((show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from sphereProduct eta (sphereProduct theta theta))-
        (show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 (lambdaMultiply 3 (sphereProduct eta u)))) := by
  have hfirst := sphere_zero_weight_label_10_134 U u hu.1
  have hu6 := model.sphereDetectionCompatible.homotopy_lambda 10 134 6 u
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hfirst
  rw [hfirst] at hu6
  have hdelta := detects_sub_filtration (model.convergence .sphere) (10,134,128) hc4.1 hu6
  have heta := eta_weight128_branches_filtration_fifteen _
    (stem124_weight128_filtration11_branches hframe _ hdelta)
  have he : sphereProduct eta ((show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from sphereProduct theta theta)-
      (show BiHom 124 128 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 u))=
      (show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from sphereProduct eta (sphereProduct theta theta))-
      (show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from sphereProduct eta (lambdaMultiply 6 u)) := by
    simp only [sphereProduct,Preadditive.comp_sub,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat]
  rw [he,eta_lambda6_right eta u,←lambda_three_3_136 (sphereProduct eta u)] at heta
  exact heta

private theorem theta5_square_eta_extension_target_detected
    (hframe : ∀ e : (model.family.sphere.sequence.ssData (13,137,128)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (13,137,128)
        (model.comparison.sphereE2 13 137 9 correction) e)
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (hc4 : Theta5SquareNonzeroDetectionAt theta)
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) (hc5 : EtaExtensionDetectionAt u) :
    Detects (model.convergence .sphere) (14,139,130) (model.comparison.sphereE2 14 139 9 T)
      (sphereProduct eta (sphereProduct theta theta)) := by
  have hlow := target_detection_lambda_three T KIP126.Computation.Standard.t_permanent_cycle _ hc5
  exact Choice.detects_of_difference_in_next_filtration (model.convergence .sphere) (14,139,130) hlow
    (theta_u_eta_filtration_error hframe theta hc4 u hu)

end
end KIP126.Main.Internal.Selected
