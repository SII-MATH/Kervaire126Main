module
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.Paper.DoublingMaximalLift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
@[expose] section
namespace KIP126.ProofTools.Paper.DoublingWarning
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

private theorem paper6_10_actual_nonzero_image_pair :
    ∃ a : BiHom 14 17 (S_0_0:SyntheticSpectrum),
      ∃ β : BiHom 14 19 (S_0_0:SyntheticSpectrum),
        a≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 3 17).symm h0h3Square ∧
        β≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 ∧
        shiftHomotopyClass (0,1) (14,17) a≫KIP126.Literature.Standard.syntheticH0=
          lambdaMultiply 1 β := by
  obtain ⟨aPos,βν,haposFirst,hβν,heq⟩ := paper6_8_full_two_representatives
  let E := suspInvarianceAddEquiv 14 17 0 1
    (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
  let aν := E.symm aPos
  have hE (b : BiHom 14 17
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :
      E b=shiftHomotopyClass (0,1) (14,17) b := by
    simp [E,suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,Iso.homCongr]
  have haPos : shiftHomotopyClass (0,1) (14,17) aν=aPos := by
    rw [←hE]
    exact E.apply_symm_apply aPos
  have hsource := shifted_full_source_detects_of_first .sphere 1 3 17 h0h3Square
    h0h3Square_permanent aPos haposFirst
  have haν := shifted_nu_source_first .sphere 1 3 17 (Or.inr rfl) h0h3Square aν (by
    rw [←haPos] at hsource
    convert hsource using 1
    norm_num [homotopyRegrade]
    rfl)
  change aν≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square at haν
  let a : BiHom 14 17 (S_0_0:SyntheticSpectrum) := aν≫model.nu.unitIso.hom
  let β : BiHom 14 19 (S_0_0:SyntheticSpectrum) := βν≫model.nu.unitIso.hom
  have haFirst : a≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square≫
      XModLambdaN.map model.nu.unitIso.hom 1 := by
    dsimp only [a]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,haν]
  have hβFirst : β≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 5 19 h0d0≫
      XModLambdaN.map model.nu.unitIso.hom 1 := by
    dsimp only [β]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hβν]
  refine ⟨a,β,?_,?_,?_⟩
  · apply (KIP126.Literature.sphereFirstQuotient model 3 17).injective
    rw [haFirst,sphere_native_quotient_label]
    exact ((KIP126.Literature.sphereFirstQuotient model 3 17).apply_symm_apply _).symm
  · apply (KIP126.Literature.sphereFirstQuotient model 5 19).injective
    rw [hβFirst,sphere_native_quotient_label]
    exact ((KIP126.Literature.sphereFirstQuotient model 5 19).apply_symm_apply _).symm
  · calc
      _ = (shiftHomotopyClass (0,1) (14,17) aν≫selectedTwoNormalized)≫model.nu.unitIso.hom := by
        rw [selectedTwoNormalized_eq_h0]
        simp only [h0NormalizedMap,shiftHomotopyClass,a,Functor.map_comp,
          Category.assoc,Iso.inv_hom_id,Category.comp_id]
      _ = (aPos≫selectedTwoNormalized)≫model.nu.unitIso.hom := by rw [haPos]
      _ = (lambdaMultiply 1 βν)≫model.nu.unitIso.hom := congrArg (fun z => z≫model.nu.unitIso.hom) heq
      _ = lambdaMultiply 1 β := by simp only [β,lambdaMultiply,Category.assoc]

private theorem actual_h0d0_lift_lambda_nonzero
    (β : BiHom 14 19 (S_0_0:SyntheticSpectrum))
    (hβ : β≫XModLambdaN.incl _ 1=
      (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0) :
    lambdaMultiply 1 β≠0 := by
  let βν : BiHom 14 19
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    β≫model.nu.unitIso.inv
  have hlabel : nativeFirstLabel .sphere 5 19 h0d0≫
      XModLambdaN.map model.nu.unitIso.hom 1=
      (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 := by
    apply (KIP126.Literature.sphereFirstQuotient model 5 19).injective
    rw [sphere_native_quotient_label,LinearEquiv.apply_symm_apply]
  let Q := (model.quotients.functoriality.functor 1).mapIso model.nu.unitIso
  letI : IsIso (XModLambdaN.map model.nu.unitIso.hom 1) := by
    change IsIso Q.hom
    infer_instance
  have hβν : βν≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 5 19 h0d0 := by
    apply (cancel_mono (XModLambdaN.map model.nu.unitIso.hom 1)).mp
    rw [hlabel]
    have hh : (βν≫XModLambdaN.incl _ 1)≫XModLambdaN.map model.nu.unitIso.hom 1=
        β≫XModLambdaN.incl _ 1 := by
      have hn := congrArg (fun z => β≫z≫XModLambdaN.map model.nu.unitIso.hom 1)
        (XModLambdaN.incl_naturality model.nu.unitIso.inv 1)
      simpa only [βν,ClassicalObject.obj,S_0_0,Category.assoc,
        ←model.quotients.functoriality.map_comp,Iso.inv_hom_id,
        model.quotients.functoriality.map_id,Category.comp_id] using hn
    exact hh.trans hβ
  have hβp := first_label_lift_permanent .sphere 5 19 h0d0 βν hβν
  have hdet := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hβp βν hβν
  have hnb : h0d0∉boundaries model .sphere (1+19-18) (5,19) := by
    norm_num only
    rw [KIP126.ProofTools.Internal.KernelClassical.stem14_s5_boundaries_two,
      Submodule.mem_bot]
    exact h0d0_ne_zero
  have hnot := KIP126.ProofTools.Internal.DoublingKernel.nu_detects_not_next_filtration
    .sphere 5 19 18 (by decide) h0d0 hnb (lambdaMultiply 1 βν) hdet
  have hnν : lambdaMultiply 1 βν≠0 := by
    intro hz
    apply hnot
    rw [hz]
    exact Submodule.zero_mem _
  intro hz
  apply hnν
  have hf : lambdaMultiply 1 βν=(lambdaMultiply 1 β)≫model.nu.unitIso.inv := by
    simp only [βν,lambdaMultiply,Category.assoc]
  rw [hf,hz,zero_comp]

private theorem paper6_10_actual_nonzero_image_pair_strong :
    ∃ a : BiHom 14 17 (S_0_0:SyntheticSpectrum),
      ∃ β : BiHom 14 19 (S_0_0:SyntheticSpectrum),
        a≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 3 17).symm h0h3Square ∧
        β≫XModLambdaN.incl _ 1=
          (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 ∧
        shiftHomotopyClass (0,1) (14,17) a≫KIP126.Literature.Standard.syntheticH0=
          lambdaMultiply 1 β ∧ lambdaMultiply 1 β≠0 := by
  obtain ⟨a,β,ha,hβ,he⟩ := paper6_10_actual_nonzero_image_pair
  exact ⟨a,β,ha,hβ,he,actual_h0d0_lift_lambda_nonzero β hβ⟩

end
end KIP126.ProofTools.Paper.DoublingWarning
end
