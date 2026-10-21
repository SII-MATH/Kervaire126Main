module

public import KIP126.ProofTools.Language
public import KIP126.ProofTools.ConvergenceOperations
public import KIP126.E2Computation.Standard
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions
import all KIP126.ProofTools.Paper.DoublingCrossing
import all KIP126.ProofTools.Paper.DoublingMaximalLift
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta

/-! Actual sphere representatives for the multiplication-by-two crossing example. -/
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

/-! The fixed numerical labels and complete multiplication-by-two crossing warning. -/
@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The fixed archive generator d_0 in the actual sphere Adams E2 page. -/
@[no_expose] public def d0 : model.classical.sphere.Page 2 (4,18) :=
  KIP126.ProofTools.Paper.NumericalExamples.d0

/-- The actual product of the fixed standard h0 with that d_0. -/
public def h0d0 : model.classical.sphere.Page 2 (5,19) := product h0 d0

/-- Complete fixed multiplication-by-two warning of Example 6.8 and
Remarks 6.9--6.10. Every equality concerns the specified actual map and
labels. In particular the last clause is strict zero in homotopy, not
only a zero infinity-page label. -/
public theorem paper6_8_complete_crossing_warning :
    let f : SphereSpectrum (C := Spectrum) ⟶ SphereSpectrum := 2 • 𝟙 _
    let x : Ambient model .sphere (3,17) :=
      product h0 (model.standardClasses.standardHiSquare 3)
    let e := normalizedExponent model.classicalTower f
    ∃ he : e = 1,
    let F : (SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ⟶
        model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary) := by
      have hef : normalizedExponent model.classicalTower f = 1 := he
      simpa only [hef,Nat.cast_one] using (model.normalizedMap .sphere .sphere f).map
    F = (SyntheticCategory.biShift (0,1)).map model.nu.unitIso.hom ≫
      KIP126.Literature.Standard.syntheticH0 ≫ model.nu.unitIso.inv ∧
    DifferentialAt model .sphere 2 (1,16) (3,17) h4 x ∧
    FiniteExtension model .sphere .sphere f 2 1 1 16 h4
      (KIP126.Literature.Standard.hiProduct 0 4) ∧
    NoCrossingOn model .sphere 2 2 (1,16) ∧
    FiniteNoCrossing model .sphere .sphere f 2 1 1 16 ∧
    InfiniteExtension model .sphere .sphere f 2 3 17 x 0 ∧
    (∃ W : InfiniteExtensionWitness model .sphere .sphere f 1 4 18 d0 h0d0,
      W.Essential) ∧
    InfiniteExtension model .sphere .sphere f 2 3 17 x h0d0 ∧
    InfiniteHasCrossing model .sphere .sphere f 2 3 17 ∧
    (∀ W : InfiniteExtensionWitness model .sphere .sphere f 2 3 17 x h0d0,
      ¬ W.Essential ∧ W.target ≠ 0) ∧
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) h0d0 ∧
    ¬ DifferentialAt model .sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) 0 ∧
    -- A genuine shorter essential extension at the SAME weight 18 as
    -- the long relation, whose source represents lambda times a d0 lift.
    (∃ a : BiHom 14 19 ((SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))),
      ∃ b : BiHom 14 19
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      ∃ source target,
        Detects (model.convergence (.shift (0,(e:ℤ)) (.nu .sphere))) (4,18,19)
          (regradeE2 (by rw [he]; norm_num)
            (model.comparison.nuE2 .sphere e 4 18 0 d0)) a ∧
        a ≫ (model.normalizedMap .sphere .sphere f).map = b ∧
        HasInfinityRepresentative _ 2 (5,19,18)
          (nuWeightLabel model .sphere 5 19 18 (by decide) h0d0) target ∧
        TowerEssentialExtension (F := model.family) (P := model.syntheticTower)
          (cx := model.convergence (.shift (0,(e:ℤ)) (.nu .sphere)))
          (cy := model.convergence (.nu .sphere))
          (model.convergentMap (.shift (0,(e:ℤ)) (.nu .sphere)) (.nu .sphere)
            (model.normalizedMap .sphere .sphere f).map)
          (14,18) 4 1 source target ∧
        ∃ ar : (Subobject.underlying.obj ((model.syntheticTower.filtration
          ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).F
              4 (14,18)) : ModuleCat.{0} ℤ),
          ((model.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).F
              4 (14,18)).arrow ar = lambdaMultiply 1 a ∧
          (model.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).toAssociatedGraded
              4 (14,18) ar =
            (infinityGradedIso (model.convergence (.shift (0,(e:ℤ)) (.nu .sphere)))
              (14,18) 4).hom source) ∧
    -- An actual second source lift and its nonzero-label image. The
    -- factor lambda is explicit at weights 17, 18 and 19.
    (∃ a : BiHom 14 17 (S_0_0 : SyntheticSpectrum),
      ∃ β : BiHom 14 19 (S_0_0 : SyntheticSpectrum),
        a ≫ XModLambdaN.incl _ 1 =
          (KIP126.Literature.sphereFirstQuotient model 3 17).symm x ∧
        β ≫ XModLambdaN.incl _ 1 =
          (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 ∧
        shiftHomotopyClass (0,1) (14,17) a ≫
          KIP126.Literature.Standard.syntheticH0 = lambdaMultiply 1 β ∧
        lambdaMultiply 1 β ≠ 0) ∧
    -- A lift with strictly zero actual image, hence with every finite
    -- lambda division of that same image (the maximal-image assertion).
    (∃ a : BiHom 14 17 (S_0_0 : SyntheticSpectrum),
      a ≫ XModLambdaN.incl _ 1 =
        (KIP126.Literature.sphereFirstQuotient model 3 17).symm x ∧
      shiftHomotopyClass (0,1) (14,17) a ≫
        KIP126.Literature.Standard.syntheticH0 = 0 ∧
      ∀ q : ℕ, ∃ b : BiHom 14 (18+(q:ℤ)) (S_0_0 : SyntheticSpectrum),
        homotopyRegrade rfl (by dsimp; omega) (lambdaMultiply q b) =
          shiftHomotopyClass (0,1) (14,17) a ≫
            KIP126.Literature.Standard.syntheticH0) := by
  dsimp only
  have he : normalizedExponent model.classicalTower
      (2 • 𝟙 (SphereSpectrum (C := Spectrum))) = 1 :=
    KIP126.ProofTools.Paper.DoublingNumericalExtensions.twoMap_exponent
  refine ⟨he, ?_⟩
  obtain ⟨hd2,hfinite,hzero,hshort,hlong,hnotzero⟩ :=
    KIP126.ProofTools.Paper.DoublingNumericalExtensions.paper6_8_crossing_warning
  refine ⟨?_,hd2,hfinite,?_,?_,hzero,hshort,hlong,?_,?_,?_,hnotzero,?_,?_,?_⟩
  · change KIP126.ProofTools.Paper.NuNumericalExtensions.normalizedMapInPositiveCoordinates
      .sphere .sphere KIP126.ProofTools.Paper.DoublingNumericalExtensions.twoMap
      KIP126.ProofTools.Paper.DoublingNumericalExtensions.twoMap_exponent =
        KIP126.ProofTools.Paper.DoublingNumericalExtensions.h0NormalizedMap
    exact KIP126.ProofTools.Paper.DoublingNumericalExtensions.selectedTwoNormalized_eq_positive.symm.trans
      KIP126.ProofTools.Paper.DoublingNumericalExtensions.selectedTwoNormalized_eq_h0
  · refine ⟨by decide,by decide,?_⟩
    rintro ⟨a,b,ha,hab,_⟩
    omega
  · rintro ⟨a,b,ha,hab,_⟩
    omega
  · exact KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_has_paper_crossing
  · intro W
    exact ⟨KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_long_inessential W,
      KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_long_target_nonzero W⟩
  · exact KIP126.ProofTools.Paper.NumericalExamples.paper6_8_classical_d3
  · exact KIP126.ProofTools.Paper.DoublingCrossing.paper6_8_lowered_actual_crossing
  · exact KIP126.ProofTools.Paper.DoublingWarning.paper6_10_actual_nonzero_image_pair_strong
  · obtain ⟨a,ha,hzero,hmax⟩ :=
      KIP126.ProofTools.Paper.DoublingMaximalLift.paper6_10_actual_maximal_zero_image_lift
    refine ⟨a,?_,hzero,hmax⟩
    apply (KIP126.Literature.sphereFirstQuotient model 3 17).injective
    rw [ha,KIP126.ProofTools.Paper.NuNumericalExtensions.sphere_native_quotient_label]
    exact ((KIP126.Literature.sphereFirstQuotient model 3 17).apply_symm_apply _).symm

end
end KIP126.ProofTools.Standard
end
