module
import all KIP126.Main.SectionSeven.AnyYError
import all KIP126.Main.SectionSeven.NuTargetLambda
/-! Exact lambda-six splitting of a target representative,
AnyYHelpers:2764–2820 at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
theorem anyy_sphere_exact_target_split
    (T : model.classical.sphere.Page 2 (14,139))
    (hT : IsPermanentCycle (model.classical.sphere) (14,139) T)
    (a : BiHom 125 133 (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (14,139,133) (model.comparison.sphereE2 14 139 6 T) a) :
    ∃ t : BiHom 125 139 (S_0_0 : SyntheticSpectrum),
      (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t)=T ∧ lambdaMultiply 6 t=a := by
  obtain ⟨t00,ht0⟩ := sphere_permanent_first_quotient_lift 14 139 T hT
  let t0 : BiHom 125 139 (S_0_0 : SyntheticSpectrum) := t00
  change (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t0)=T at ht0
  let a0 : BiHom 125 133 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 6 t0
  have ha0 : Detects (model.convergence .sphere) (14,139,133) (model.comparison.sphereE2 14 139 6 T) a0 := by
    have h := model.sphereDetectionCompatible.homotopy_lambda 14 139 6 t0
    change Detects (model.convergence .sphere) (14,139,133)
      (sphereLabel 14 139 6 ((KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t0))) (lambdaMultiply 6 t0) at h
    rw [ht0] at h
    exact h
  have hdiff : FiltrationAtLeast model.syntheticTower 15 (a-a0) :=
    detects_sub_filtration (model.convergence .sphere) (14,139,133) ha ha0
  have hnu := KIP126.Main.Internal.Selected.map_filtration .sphere (.nu .sphere) model.nu.unitIso.inv (a-a0) hdiff
  have hlam := KIP126.Literature.Standard.selected_filtration_lambda .sphere 125 133 15 (by omega) ((a-a0)≫model.nu.unitIso.inv)
  change FiltrationAtLeast model.syntheticTower 15 ((a-a0)≫model.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (model.nu.functor.obj SphereSpectrum), lambdaMultiply 7 b=(a-a0)≫model.nu.unitIso.inv at hlam
  obtain ⟨b,hb⟩ := hlam.mp hnu
  let c : BiHom 125 140 (S_0_0 : SyntheticSpectrum) := b≫model.nu.unitIso.hom
  have hc : lambdaMultiply 7 c=a-a0 := by
    simpa only [c,lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun x=>x≫model.nu.unitIso.hom) hb
  let lc : BiHom 125 139 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 1 c
  have hq : quotientClass 1 lc=0 := by
    exact (KIP126.Main.Internal.Selected.vanishes_mod_lambda_iff_multiple 1 125 140 lc).mpr ⟨c,rfl⟩
  refine ⟨t0+lc,?_,?_⟩
  · change (KIP126.Literature.sphereFirstQuotient model) 14 139 ((t0+lc)≫XModLambdaN.incl _ 1)=T
    rw [Preadditive.add_comp,map_add]
    change (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t0)+
      (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 lc)=T
    rw [ht0,hq,map_zero,add_zero]
  · let c7 : BiHom 125 133 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 7 c
    have he1 : (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 lc)=c7 :=
      y_detection_toda_main_lambda_six_one c
    have he : (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 (t0+lc))=a0+c7 := by
      calc
        _ = a0+(show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 lc) := by
          simp only [a0,lambdaMultiply,Preadditive.comp_add]
        _ = a0+c7 := by rw [he1]
    change (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 (t0+lc))=a
    rw [he]
    have hc7 : c7=a-a0 := hc
    rw [hc7]
    abel
end
end KIP126.Main.SectionSeven.Internal
