module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Main.SectionSeven.Lambda
public import KIP126.Def.AdamsSynthetic.Conditions.D12Criterion
import all KIP126.Main.SectionSeven.DifferentialCriterion.ThetaSquareClassification
import all KIP126.Main.SectionSeven.DifferentialCriterion.ClassicalDifferentials
import all KIP126.Main.SectionSeven.DifferentialCriterion.ChoiceInvariance
import all KIP126.Main.SectionSeven.DifferentialCriterion.EtaDetection

@[expose] public section

namespace KIP126.Main.SectionSeven.DifferentialCriterion

open private theta_square_choice_invariance from KIP126.Main.SectionSeven.DifferentialCriterion.ChoiceInvariance
open private d12_criterion_classical_differentials from KIP126.Main.SectionSeven.DifferentialCriterion.ClassicalDifferentials
open private eta_detection_criterion from KIP126.Main.SectionSeven.DifferentialCriterion.EtaDetection
open private theta_square_detection_cases from KIP126.Main.SectionSeven.DifferentialCriterion.ThetaSquareClassification
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.SphereAndCofiber
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
  {L : SphereAdamsClasses H} {G : TmfDetectionClasses H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem h6_square_dichotomy_realization_additive {D : AdamsComparison H M Syn} : D.recovery.realization.Additive := by
  classical
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem h6_square_dichotomy_realize_detector {D : AdamsComparison H M Syn} {m wt : ℤ} (R : KIP126.Literature.AdamsSynthetic.RealizationCoordinates D)
    (a : BiHom m wt (S_0_0 : Syn)) :
    KIP126.Literature.AdamsSynthetic.realizeNu D R .sphere (a ≫ D.nu.unitIso.inv) ≫ D.hopfAndDetector.detectorUnit =
      KIP126.Literature.AdamsSynthetic.realizeNu D R .detector (a ≫ KIP126.Literature.AdamsSynthetic.detectorMap D) := by
  classical
  have hn := D.recovery.nuRealizationIso.hom.naturality D.hopfAndDetector.detectorUnit
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [KIP126.Literature.AdamsSynthetic.realizeNu, KIP126.Literature.AdamsSynthetic.detectorMap, ClassicalObject.obj, Functor.map_comp, Category.assoc]
  rw [← hn]

private theorem h6_square_dichotomy_high125_detector_nonzero_parts {D : AdamsComparison H M Syn}
    (TM : KIP126.Literature.AdamsSynthetic.TmfDetectionTheorems D G) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (G.high125 M) a) : a ≫ D.hopfAndDetector.detectorUnit ≠ 0 := by
  classical
  obtain ⟨_, b, hb, hnonzero⟩ := TM.high125_detected
  have heq : a = b := high125_detected_choice_unique I V S a b
    (by simpa only [high125_label I] using ha)
    (by simpa only [high125_label I] using hb)
  simpa only [heq] using hnonzero

private theorem h6_square_dichotomy_theta_detector_zero_parts {D : AdamsComparison H M Syn}
    (BHS : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
    (RL : KIP126.Literature.AdamsSynthetic.RealizationDetectionData D)
    (CL : KIP126.Literature.AdamsSynthetic.ClassicalTheorems D η)
    (TM : KIP126.Literature.AdamsSynthetic.TmfDetectionTheorems D G)
    (theta : BiHom 62 64 (S_0_0 : Syn))
    (htheta : ThetaChoice M D.toAdamsComparisonData theta) :
    theta ≫ KIP126.Literature.AdamsSynthetic.detectorMap D = 0 := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    letI := h6_square_dichotomy_realization_additive (D := D)
    let a : BiHom 62 64 (KIP126.Literature.AdamsSynthetic.nuZero D .sphere) :=
      theta ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _
    have ha : quotientClass 1 a = KIP126.Literature.AdamsSynthetic.firstLabel D .sphere 2 64 (Sphere.Internal.hiSquare H M 5) := by
      apply (D.firstQuotient SphereSpectrum 0 2 64).injective
      change (D.firstQuotient SphereSpectrum 0 2 64) (quotientClass 1 a) =
        (D.firstQuotient SphereSpectrum 0 2 64)
          ((D.firstQuotient SphereSpectrum 0 2 64).symm (Sphere.Internal.hiSquare H M 5))
      rw [AddEquiv.apply_symm_apply, ← htheta]
      change (D.firstQuotient SphereSpectrum 0 2 64) _ =
        (D.firstQuotient SphereSpectrum 0 2 64)
          (quotientClass 1 theta ≫ XModLambdaN.map
            (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1)
      apply congrArg (D.firstQuotient SphereSpectrum 0 2 64)
      simp only [a, quotientClass, Category.assoc, XModLambdaN.incl_naturality,
        D.quotientFunctoriality.map_comp]
    have hd := RL.detection.detection .sphere 2 64
      (Sphere.Internal.hiSquare H M 5) a CL.theta5_exists.1 ha
    have he : KIP126.Literature.AdamsSynthetic.realizeNuZero D RL.coordinates .sphere a =
        KIP126.Literature.AdamsSynthetic.realizeNu D RL.coordinates .sphere (theta ≫ D.nu.unitIso.inv) := by
      simp only [KIP126.Literature.AdamsSynthetic.realizeNuZero, a, ClassicalObject.obj, Category.assoc, Iso.inv_hom_id_app,
        Functor.id_obj, Category.comp_id]
    rw [he] at hd
    have hz := TM.theta5_vanishes _ hd
    rw [h6_square_dichotomy_realize_detector] at hz
    apply detector_realization_injective_62_64 BHS TM.low_filtration_63
    change D.recovery.realization.map (theta ≫ KIP126.Literature.AdamsSynthetic.detectorMap D) = D.recovery.realization.map 0
    rw [Functor.map_zero]
    apply (cancel_epi (RL.coordinates.sphere 62 64).hom).mp
    apply (cancel_mono (D.recovery.nuRealizationIso.app D.hopfAndDetector.detector).hom).mp
    dsimp only [KIP126.Literature.AdamsSynthetic.realizeNu, ClassicalObject.obj] at hz
    erw [Limits.comp_zero, Limits.zero_comp, Category.assoc]
    exact hz

private theorem h6_square_dichotomy (BHS : SyntheticComparisonTheorems D) (RL : RealizationDetectionData D)
    (CL : ClassicalTheorems D η) (AF : SphereActionFiltrationCompatible D)
    (TM : TmfDetectionTheorems D G) (BX : BXDistinguishedThetaTheorem D η)
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H) :
    KIP126.Main.Stem126.OnlyD12.d12_dichotomy_and_condition_equivalence M D L η := by
  classical
  /- The synthetic tmf image used in the high-filtration contradiction.
  The product and unit are the ones bound by `A.algebra.detector`, on D's
  chosen completed tmf; no separate homotopy-ring model is selected. -/
  have eta_theta_square_detector_zero_parts {D : AdamsComparison H M Syn}
      (BHS : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
      (RL : KIP126.Literature.AdamsSynthetic.RealizationDetectionData D)
      (CL : KIP126.Literature.AdamsSynthetic.ClassicalTheorems D η)
      (TM : KIP126.Literature.AdamsSynthetic.TmfDetectionTheorems D G)
      (theta : BiHom 62 64 (S_0_0 : Syn))
      (htheta : ThetaChoice M D.toAdamsComparisonData theta) :
      sphereProduct η (sphereProduct theta theta) ≫
        KIP126.Literature.AdamsSynthetic.detectorMap D = 0 := by
    have h := h6_square_dichotomy_theta_detector_zero_parts BHS RL CL TM theta htheta
    dsimp only [sphereProduct]
    simp only [Smn] at h
    simp only [Smn, Category.assoc]
    rw [h]
    erw [Limits.comp_zero, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]
  have detector_injective_fifteen_parts {D : AdamsComparison H M Syn}
      (BHS : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
      (RL : KIP126.Literature.AdamsSynthetic.RealizationDetectionData D)
      (TM : KIP126.Literature.AdamsSynthetic.TmfDetectionTheorems D G) (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
      (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
      (a : BiHom 125 130 (S_0_0 : Syn))
      (ha : KIP126.Synthetic.SpectralSequence.FiltrationAtLeast
        (nuCoefficientUnit H.unit D.nu) 15 a)
      (hz : a ≫ KIP126.Literature.AdamsSynthetic.detectorMap D = 0) : a = 0 := by
    set_option backward.isDefEq.respectTransparency false in
      letI := h6_square_dichotomy_realization_additive (D := D)
      by_contra hne
      have hd := high125_weight130_nonzero_classical_detection I BHS RL V
        TM.high125_detected.1 a ha hne
      have hn := h6_square_dichotomy_high125_detector_nonzero_parts TM I V S
        (KIP126.Literature.AdamsSynthetic.realizeNu D RL.coordinates .sphere
          (a ≫ D.nu.unitIso.inv)) hd
      apply hn
      rw [h6_square_dichotomy_realize_detector, hz]
      simp only [KIP126.Literature.AdamsSynthetic.realizeNu, Functor.map_zero,
        Limits.comp_zero, Limits.zero_comp]
  have non_c4_branch_eta_filtration_fifteen {D : AdamsComparison H M Syn}
      (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (SF : Derived.SphereFacts I.interpretation)
      (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toAdamsComparisonData η)
      (θ : BiHom 62 64 (S_0_0 : Syn))
      (hbranch : SphereDetected D 13 137 9 (I.interpretation.sphere 13 137 correction)
          (sphereProduct θ θ) ∨
        ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=sphereProduct θ θ) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (sphereProduct η (sphereProduct θ θ)) := by
    have hη0 : lambdaMultiply 0 η=η := by
      have hc := D.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
        change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ η=η
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
    rw [hη0,hη] at hηd
    rcases hbranch with h13 | ⟨a,ha⟩
    · have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
          (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)=0 := by
        have h := I.products ⟨1,2,13,137⟩ (by simp [Raw.products]) dataH1 correction
        dsimp only at h
        rw [I.distinguishedClasses.h1] at h
        exact h.symm.trans SF.h1_correction_zero
      have hd := D.multiplicationCompatible 1 2 13 137 0 9
        (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)
        η (sphereProduct θ θ) hηd h13.1
      change Detects D.sphereConvergence (14,139,130)
        (D.sphereE2 14 139 9 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
          (Sphere.Internal.hi H M 1) (I.interpretation.sphere 13 137 correction)))
        (sphereProduct η (sphereProduct θ θ)) at hd
      rw [hp,map_zero] at hd
      exact detects_zero_filtration D.sphereConvergence (14,139,130) hd
    · have had := D.comparisonCompatible.homotopy_lambda 14 138 10 a
      rw [ha] at had
      have hd := D.multiplicationCompatible 1 2 14 138 0 10
        (Sphere.Internal.hi H M 1) (D.sphereFirstQuotient 14 138 (quotientClass 1 a))
        η (sphereProduct θ θ) hηd had
      change Detects D.sphereConvergence (15,140,130) _ (sphereProduct η (sphereProduct θ θ)) at hd
      obtain ⟨e,he,a',ha',hgr⟩ := hd
      rw [←ha']
      have hm : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)).arrow a'∈
          (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (125,130)))
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)) := ⟨a',rfl⟩
      simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm
  have theta_detection_step {D : AdamsComparison H M Syn}
      (i : Tridegree) (x : (D.family.sphere).E₂ i)
      (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
        e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
      (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
      DetectsNonzero D.sphereConvergence i x a ∨
        FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
    have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
        (F.F i.1 (i.2.1-i.1,i.2.2)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
    let e := (D.sphereConvergence.identification i).inv q
    have he : (D.sphereConvergence.identification i).hom e=q :=
      ConcreteCategory.congr_hom (D.sphereConvergence.identification i).inv_hom_id q
    by_cases he0 : e=0
    · right
      have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
        rw [he0,map_zero] at he
        exact he.symm
      have hmem := (subobject_cokernel_π_eq_zero_iff
        (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
        (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
      rw [ha'] at hmem
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
    · left
      have hr := (hframe e).resolve_left he0
      exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩
  /- The two complete frames and the intervening finite-page gap yield the
  three branches, retaining an actual lambda preimage in the last branch. -/
  intro hη
  obtain ⟨h13,hcases⟩ := theta_square_detection_cases I BHS V SF
  obtain ⟨hc3,hdnp,hbx,hframe6⟩ := d12_criterion_classical_differentials I SF
  obtain ⟨h9,h10,huex,h4f14,huf14,hframe,herr,hlambda,hdetect,hnonzero⟩ :=
    eta_detection_criterion I BHS SF h13 hframe6
  obtain ⟨theta,htheta,hboundary,hcriterion⟩ := BX
  let a : BiHom 125 130 (S_0_0:Syn) := sphereProduct η (sphereProduct theta theta)
  have permanent_of_f15 (hf : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) :
      PermanentH6Square M := by
    have hz : a=0 := detector_injective_fifteen_parts BHS RL TM I V S _ hf
      (eta_theta_square_detector_zero_parts BHS RL CL TM theta htheta.2.1)
    apply hcriterion.mpr
    change lambdaAction 125 130 S_0_0 a=0
    rw [hz]
    simp only [lambdaAction,CategoryTheory.Limits.comp_zero]
  have dichotomy : (PermanentH6Square M ∧ ¬H6SquareSupportsD12 M L) ∨
      (H6SquareSupportsD12 M L ∧ ¬PermanentH6Square M) := by
    have hf14 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
      rcases hcases theta with h4|hbranch
      · exact h4f14 η hη theta h4
      · exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu) (S_0_0:Syn)
          (125,130) (by decide : (14:ℤ)≤15)
          (non_c4_branch_eta_filtration_fifteen I SF η hη theta hbranch)
    by_cases hf15 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a
    · have hp := permanent_of_f15 hf15
      exact Or.inl ⟨hp,fun hd=>(hdnp hd).1 hp⟩
    · have hd := hbx η theta htheta ((h9 a).mpr hf14) (fun h=>hf15 ((h10 a).mp h))
      exact Or.inr ⟨hd,(hdnp hd).1⟩
  refine ⟨dichotomy,?_,?_⟩
  · intro hd
    have impossible (hf : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) : False :=
      (hdnp hd).1 (permanent_of_f15 hf)
    have h4 : Theta5SquareNonzeroDetectionAt M D.toAdamsComparisonData L theta := by
      rcases hcases theta with h4|hbranch
      · exact h4
      · exact False.elim (impossible
          (non_c4_branch_eta_filtration_fifteen I SF η hη theta hbranch))
    refine ⟨(hdnp hd).2,⟨theta,htheta.2.1,h4⟩,?_⟩
    obtain ⟨u,hu⟩ := huex
    let c : BiHom 125 133 (S_0_0:Syn) := lambdaMultiply 3 (sphereProduct η u)
    have hc14 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 c := huf14 η hη u hu
    rcases theta_detection_step (14,139,133) (D.sphereE2 14 139 6 (L.target M))
        hframe c hc14 with hdet|hc15
    · exact ⟨u,hu,hdet.1⟩
    · exfalso
      apply impossible
      have he := herr η hη theta h4 u hu
      have hl := hlambda c hc15
      change (show BiHom 125 130 (S_0_0:Syn) from a)-
        (show BiHom 125 130 (S_0_0:Syn) from lambdaMultiply 3 c) ∈
        towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) (S_0_0:Syn) 15 (125,130) at he
      have hh := (towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
        (S_0_0:Syn) 15 (125,130)).add_mem he hl
      simpa only [sub_add_cancel,FiltrationAtLeast,Int.reduceAdd] using hh
  · rintro ⟨hc,⟨theta',htheta',h4'⟩,u,hu,h5⟩
    have h4 := theta_square_choice_invariance I BHS RL CL AF theta theta' htheta.2.1 htheta' h4'
    have hn := hnonzero (hc3.mp hc) _ (hdetect η hη theta h4 u hu h5)
    exact hbx η theta htheta ((h9 a).mpr (h4f14 η hη theta h4))
      (fun h=>hn ((h10 a).mp h))

end
end KIP126.Main.SectionSeven.DifferentialCriterion
