module
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Choice.Filtration
import all KIP126.Main.Internal.AlphaOne.Classical
/-! The original theta-b-eta vanishing branch from WeakRepresentative:
2120–2627 (bbac1fc05843, MIT), reusing the already proved stable-boundary
frame and retaining the actual filtration of the same representative. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main.Internal KIP126.Main.Internal.Selected KIP126.Main.Internal.Choice
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Computation.Standard (correction)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
private theorem eta_weight129_branches_filtration_fifteen
    (eta : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (heta : Detects (model.convergence .sphere) (1,2,2)
      (model.comparison.sphereE2 1 2 0 (model.standardClasses.standardHi 1)) eta)
    (b : BiHom 124 129 (S_0_0 : SyntheticSpectrum))
    (hbranch : DetectsNonzero (model.convergence .sphere) (13,137,129)
        (model.comparison.sphereE2 13 137 8 correction) b ∨
      ∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 9 a=b) :
    FiltrationAtLeast model.syntheticTower 15 (sphereProduct eta b) := by
  rcases hbranch with h13 | ⟨a,ha⟩
  · have hd := model.multiplicationCompatible 1 2 13 137 0 8
      (model.standardClasses.standardHi 1) correction eta b heta h13.1
    change Detects (model.convergence .sphere) (14,139,131)
      (model.comparison.sphereE2 14 139 8 (KIP126.Computation.Standard.product (r := (14,139))
        KIP126.Computation.Standard.h1 correction)) (sphereProduct eta b) at hd
    rw [KIP126.Computation.Standard.h1_correction_zero,map_zero] at hd
    exact detects_zero_filtration (model.convergence .sphere) (14,139,131) hd
  · have had := model.sphereDetectionCompatible.homotopy_lambda 14 138 9 a
    rw [ha] at had
    have hd := model.multiplicationCompatible 1 2 14 138 0 9
      (model.standardClasses.standardHi 1) (sphereFirstQuotient model 14 138 (quotientClass 1 a))
      eta b heta had
    change Detects (model.convergence .sphere) (15,140,131) _ (sphereProduct eta b) at hd
    obtain ⟨e,he,a',ha',hgr⟩ := hd
    rw [←ha']
    have hm : ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 15 (125,131)).arrow a' ∈
        (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : SyntheticSpectrum) (125,131)))
          ((model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)).F 15 (125,131)) := ⟨a',rfl⟩
    simpa only [FiltrationAtLeast,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm

private theorem stem124_weight129_filtration11_branches
    (hframe : ∀ e : (model.family.sphere.sequence.ssData (13,137,129)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (13,137,129)
        (model.comparison.sphereE2 13 137 8 correction) e)
    (a : BiHom 124 129 (S_0_0 : SyntheticSpectrum))
    (ha11 : FiltrationAtLeast model.syntheticTower 11 a) :
    DetectsNonzero (model.convergence .sphere) (13,137,129)
        (model.comparison.sphereE2 13 137 8 correction) a ∨
      ∃ b : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 9 b=a := by
  have ha13 : FiltrationAtLeast model.syntheticTower 13 a := by
    apply (filtration_iff_of_infinity_zero (model.convergence .sphere)
      11 13 124 129 (by decide) ?_ a).mp ha11
    intro j hj hj'
    apply sphere_infinity_zero_of_permanent_quotient_zero j (124+j) 129 (by omega)
    interval_cases j
    · exact permanent_quotient_zero_of_page_zero .sphere 5 7 (by decide) (by decide) (11,135)
        KIP126.Computation.Standard.e5_stem124_af11
    · exact permanent_quotient_zero_of_page_zero .sphere 4 8 (by decide) (by decide) (12,136)
        KIP126.Computation.Standard.e4_stem124_af12
  rcases theta_detection_step (13,137,129)
    (model.comparison.sphereE2 13 137 8 correction) hframe a ha13 with hdet|ha14
  · exact Or.inl hdet
  right
  have h := KIP126.Literature.Standard.selected_filtration_lambda .sphere 124 129 14 (by decide)
    (a ≫ model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 14 (a ≫ model.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (model.nu.functor.obj SphereSpectrum), lambdaMultiply 9 b=a ≫ model.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv a ha14)
  refine ⟨b ≫ model.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ model.nu.unitIso.hom) hb


private theorem main_eta_right_five (eta : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    {X : SyntheticSpectrum} (c : BiHom 124 134 X) :
    sphereAction eta (lambdaMultiply 5 c) = lambdaMultiply 5 (sphereAction eta c) := by
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (124,134) (0,-5)
    (125,136) (124,129) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub,Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 5
    ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 5 ((SyntheticCategory.biShift (124,134)).map eta))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-5)).inv.naturality eta)]
  rfl

private theorem lambda_zero_theta (a : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) : lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (62,64) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 62 64 : SyntheticSpectrum) := by
    change (biShiftAddIso (62,64) (0,0) (62,64) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

theorem theta_b_eta_fifth_mod_nine_zero_from_choice
    (eta : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (heta : sphereFirstQuotient model 1 2 (quotientClass 1 eta)=model.standardClasses.standardHi 1)
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta)
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum))
    (hb : SphereDetected 8 70 0 (KIP126.Computation.Standard.atom .b) b) :
    quotientClass 9 (lambdaMultiply 5 (sphereProduct eta (sphereProduct theta b)))=0 := by
  have hη := model.sphereDetectionCompatible.homotopy_lambda 1 2 0 eta
  have hθ := model.sphereDetectionCompatible.homotopy_lambda 2 64 0 theta
  change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
    model.firstQuotient 1 2 (quotientClass 1 eta)=_ at heta
  change KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality
    model.firstQuotient 2 64 (quotientClass 1 theta)=_ at htheta
  rw [lambda_zero_1_2,heta] at hη
  rw [lambda_zero_theta,htheta] at hθ
  have hd := model.multiplicationCompatible 2 64 8 70 0 0
    (model.standardClasses.standardHiSquare 5) (KIP126.Computation.Standard.atom .b) theta b hθ hb.1
  change Detects (model.convergence .sphere) (10,134,134)
    (model.comparison.sphereE2 10 134 0 (KIP126.Computation.Standard.product (r := (10,134))
      KIP126.Computation.Standard.h5Square (KIP126.Computation.Standard.atom .b))) (sphereProduct theta b) at hd
  rw [KIP126.Computation.Standard.h5Square_b_zero,map_zero] at hd
  have hf := detects_zero_filtration (model.convergence .sphere) (10,134,134) hd
  have hf5 : FiltrationAtLeast model.syntheticTower 11 (lambdaMultiply 5 (sphereProduct theta b)) := by
    obtain ⟨z,hz⟩ := hf
    refine ⟨lambdaMultiply 5 z,?_⟩
    change lambdaMultiply 5 z ≫ (model.syntheticTower.tower _).projection 11=_
    change z ≫ (model.syntheticTower.tower _).projection 11=_ at hz
    simpa only [lambdaMultiply,Category.assoc,hz,Int.reduceSub,Int.reduceAdd]
  have hframe := theta_sphere_frame 13 137 8 (by decide) (by decide) correction
    AlphaOne.classical_stem124_af13_generated
  have hbranch := stem124_weight129_filtration11_branches hframe _ hf5
  have h15 := eta_weight129_branches_filtration_fifteen eta hη _ hbranch
  have hv : quotientClass 9 (sphereProduct eta (lambdaMultiply 5 (sphereProduct theta b)))=0 := by
    apply sphere_quotient_high_filtration_zero 9 (by decide) 125 131 15 (by decide)
    exact map_filtration .sphere (.quotient 9 .sphere) (XModLambdaN.incl _ 9) _ h15
  change quotientClass 9 (sphereAction eta (lambdaMultiply 5 (sphereProduct theta b)))=0 at hv
  rw [main_eta_right_five] at hv
  exact hv

end
end KIP126.Main.SectionSeven.Internal
