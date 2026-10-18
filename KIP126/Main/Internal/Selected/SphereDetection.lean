module

public import KIP126.Main.Conditions
public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Choice.Filtration

/-! Nonzero sphere detections and the chosen U lift, from
Selected/DetectionData.lean:929–948,1023–1130 at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem nu_target_label_iff (s t : ℤ) (k : ℕ)
    (x : model.classical.sphere.Page 2 (s,t))
    (e : ((model.family.nu model.nu SphereSpectrum).sequence.ssData (s,t,t-k)).eInfty) :
    HasInfinityRepresentative _ 2 (s,t,t-k) (targetNuLabel model .sphere s t k x) e ↔
      ∃ hx : x ∈ permanentCycles model .sphere (s,t),
        KIP126.Literature.Standard.infinityNuWindow .sphere (s,t) (t-k) (by omega) e =
          subquotientClass (permanentCycles model .sphere (s,t))
            (boundaries model .sphere (1+t-(t-k)) (s,t)) ⟨x,hx⟩ := by
  have hlabel : nuWeightLabel model .sphere s t (t-k) (by omega) x =
      targetNuLabel model .sphere s t k x := by
    have hk' : (t-(t-k)).toNat = k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model .sphere s t a x) = targetNuLabel model .sphere s t b x := by
      subst b
      rfl
    exact transport _ k hk' _
  have h := KIP126.Literature.Standard.eInfinity_nu_labels .sphere s t (t-k) (by omega) x e
  rw [hlabel] at h
  exact h

private theorem sphere_target_nine_nonzero_of_survives_twelve
    (x : model.classical.sphere.Page 2 (14,139))
    (hs : SurvivesTo model.classical.sphere 12 (14,139) x)
    (e : (model.family.sphere.sequence.ssData (14,139,130)).eInfty)
    (he : HasInfinityRepresentative model.family.sphere 2 (14,139,130)
      (model.comparison.sphereE2 14 139 9 x) e) : e≠0 := by
  have hn := family_infinity_representative_map model.nu.unitIso.inv (14,139,130) _ _ he
  have hl := sphere_label_to_nu 9 14 139 x
  change familyPageMap model.family model.nu.unitIso.inv 2 (14,139,130)
    (model.comparison.sphereE2 14 139 9 x)=_ at hl
  rw [hl] at hn
  obtain ⟨hx,hf⟩ := (nu_target_label_iff 14 139 9 x _).mp hn
  intro hz
  rw [hz,map_zero,map_zero] at hf
  have hb : x ∈ boundaries model .sphere 10 (14,139) :=
    (subquotientClass_eq_zero_iff _ _ ⟨x,hx⟩).mp hf.symm
  exact survives_twelve_not_boundary_eleven .sphere (14,139) x hs
    (boundaries_monotone model .sphere (14,139) (by decide : (10:ℤ)≤11) hb)

private theorem target_detected_not_filtration_fifteen
    (x : model.classical.sphere.Page 2 (14,139))
    (hs : SurvivesTo model.classical.sphere 12 (14,139) x)
    (a : BiHom 125 130 (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (14,139,130)
      (model.comparison.sphereE2 14 139 9 x) a) :
    ¬FiltrationAtLeast model.syntheticTower 15 a := by
  intro hf
  have hz : Detects (model.convergence .sphere) (14,139,130) 0 0 :=
    ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,0,map_zero _,by simp only [map_zero]⟩
  have hza : Detects (model.convergence .sphere) (14,139,130) 0 a :=
    Choice.detects_of_difference_in_next_filtration (model.convergence .sphere) (14,139,130) hz
      (by simpa only [sub_zero,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hf)
  obtain ⟨e,he,he0⟩ := detects_infinity_equal .sphere (14,139,130) a _ 0 ha hza
  exact sphere_target_nine_nonzero_of_survives_twelve x hs e he
    (he0.unique (HasInfinityRepresentative.zero _ 2 (by decide) _))

private theorem finite_sphere_infinity_nonzero (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t)) (hne : x≠0)
    (e : ((model.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData (s,t,t-0)).eInfty)
    (he : HasInfinityRepresentative (model.family.quotient (S_0_0 : SyntheticSpectrum) q) 2 (s,t,t-0)
      (quotientLabel q s t 0 x) e) : e≠0 := by
  let g := XModLambdaN.map model.nu.unitIso.inv q
  have hh := family_infinity_representative_map g (s,t,t-0) _ _ he
  have hl := sphere_quotient_label_to_nu q 0 s t x
  change familyPageMap model.family g 2 (s,t,t-0) (quotientLabel q s t 0 x)=_ at hl
  rw [hl] at hh
  have hlabel : nuWeightLabel model .sphere s t (t-0) (by omega) x =
      targetNuLabel model .sphere s t 0 x := by
    have hzero : (t-(t-0)).toNat=0 := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model .sphere s t a x) = targetNuLabel model .sphere s t b x := by
      subst b; rfl
    exact transport _ 0 hzero _
  have hi := KIP126.Literature.Standard.eInfinity_finite_labels .sphere q hq s t (t-0)
    (by constructor <;> omega) x ((model.family.map g).eInftyMap (s,t,t-0) e)
  rw [hlabel] at hi
  obtain ⟨hx,hp⟩ := hi.mp hh
  intro he0
  rw [he0,map_zero,map_zero] at hp
  have hm := (subquotientClass_eq_zero_iff _ _ ⟨x,hx⟩).mp hp.symm
  change x ∈ boundaries model .sphere (1+t-(t-0)) (s,t) at hm
  have hb : (1:ℤ)+t-(t-0)=1 := by omega
  rw [hb,boundaries_one model .sphere (s,t),Submodule.mem_bot] at hm
  exact hne hm

private theorem sphere_zero_weight_label_10_134
    (x : model.classical.sphere.Page 2 (10,134))
    (a : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (10,134,134)
      (model.comparison.sphereE2 10 134 0 x) a) :
    sphereFirstQuotient model 10 134 (quotientClass 1 a)=x := by
  let y := sphereFirstQuotient model 10 134 (quotientClass 1 a)
  have hd := detects_map .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1) (10,134,134) _ a ha
  have hd' := model.sphereDetectionCompatible.first_quotient 10 134 y
  have hy : (sphereFirstQuotient model 10 134).symm y=quotientClass 1 a :=
    (sphereFirstQuotient model 10 134).symm_apply_apply _
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hy
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := detects_infinity_equal (.quotient 1 .sphere) (10,134,134)
    (quotientClass 1 a) _ _ hd hd'
  let g := XModLambdaN.map model.nu.unitIso.inv 1
  have he' := family_infinity_representative_map g (10,134,134) _ _ he
  have hf' := family_infinity_representative_map g (10,134,134) _ _ hf
  change HasInfinityRepresentative _ 2 (10,134,134)
    (familyPageMap model.family g 2 (10,134,134) (quotientLabel 1 10 134 0 x)) _ at he'
  change HasInfinityRepresentative _ 2 (10,134,134)
    (familyPageMap model.family g 2 (10,134,134) (quotientLabel 1 10 134 0 y)) _ at hf'
  have hlx := sphere_quotient_label_to_nu 1 0 10 134 x
  have hly := sphere_quotient_label_to_nu 1 0 10 134 y
  change familyPageMap model.family g 2 (10,134,134) (quotientLabel 1 10 134 0 x)=_ at hlx
  change familyPageMap model.family g 2 (10,134,134) (quotientLabel 1 10 134 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  have hi (v : model.classical.sphere.Page 2 (10,134)) :=
    KIP126.Literature.Standard.eInfinity_finite_labels .sphere 1 (by decide)
      10 134 134 (by decide) v ((model.family.map g).eInftyMap (10,134,134) e)
  obtain ⟨hx,hxq⟩ := (hi x).mp he'
  obtain ⟨hy,hyq⟩ := (hi y).mp hf'
  let xx : cycles model .sphere 1 (10,134) := ⟨x,hx⟩
  let yy : cycles model .sphere 1 (10,134) := ⟨y,hy⟩
  have heq : subquotientClass _ (boundaries model .sphere 1 (10,134)) xx =
      subquotientClass _ (boundaries model .sphere 1 (10,134)) yy := hxq.symm.trans hyq
  have hz : subquotientClass _ (boundaries model .sphere 1 (10,134)) (xx-yy)=0 := by
    rw [map_sub,heq,sub_self]
  have hm := (subquotientClass_eq_zero_iff _ _ (xx-yy)).mp hz
  change x-y ∈ boundaries model .sphere 1 (10,134) at hm
  rw [boundaries_one model .sphere (10,134),Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm

private theorem lambda_zero_124_134 (a : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (124,134) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (124,134) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 124 134 : SyntheticSpectrum) := by
    change (biShiftAddIso (124,134) (0,0) (124,134) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (124,134) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift_comp (124,134) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

private theorem lambda_zero_1_2 (a : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (1,2) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : SyntheticSpectrum) := by
    change (biShiftAddIso (1,2) (0,0) (1,2) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

private theorem sphere_zero_weight_nonzero_detection_u
    (x : model.classical.sphere.Page 2 (10,134))
    (a : BiHom (134-10) 134 (S_0_0 : SyntheticSpectrum))
    (ha : sphereFirstQuotient model 10 134 (quotientClass 1 a)=x) (hne : x≠0) :
    DetectsNonzero (model.convergence .sphere) (10,134,134)
      (model.comparison.sphereE2 10 134 0 x) a := by
  have hd := model.sphereDetectionCompatible.homotopy_lambda 10 134 0 a
  dsimp only [KIP126.Literature.sphereFirstQuotient] at ha
  rw [lambda_zero_124_134,ha] at hd
  refine ⟨hd,?_⟩
  obtain ⟨e,he,_⟩ := hd
  refine ⟨e,he,?_⟩
  let f := XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1
  have hf := family_infinity_representative_map f (10,134,134-0) _ _ he
  have hfn := finite_sphere_infinity_nonzero 1 (by decide) 10 134 x hne _ hf
  intro hz
  apply hfn
  rw [hz,map_zero]

private theorem u_choice_exists : ∃u,UChoice u := by
  have hp := KIP126.Computation.Standard.u_permanent
  obtain ⟨z,hz,hzn⟩ := hp
  have hcycle : IsPermanentCycle model.classical.sphere (10,134) KIP126.Computation.Standard.U := ⟨z,hz⟩
  have hn : KIP126.Computation.Standard.U≠0 := by
    intro h0
    let P := model.classical.sphere.ssData (10,134)
    have hh := P.infinity_projection_eq_of_page_projection_eq ↑(2-model.classical.sphere.r₀).toNat z 0
      (by simpa only [map_zero] using hz.trans h0)
    exact hzn (by simpa only [map_zero] using hh)
  obtain ⟨u,hu⟩ := sphere_permanent_first_quotient_lift 10 134 KIP126.Computation.Standard.U hcycle
  exact ⟨u,sphere_zero_weight_nonzero_detection_u KIP126.Computation.Standard.U u hu hn⟩

private theorem target_detection_lambda_three
    (x : model.classical.sphere.Page 2 (14,139))
    (hx : IsPermanentCycle model.classical.sphere (14,139) x)
    (c : BiHom 125 133 (S_0_0 : SyntheticSpectrum))
    (hc : Detects (model.convergence .sphere) (14,139,133) (model.comparison.sphereE2 14 139 6 x) c) :
    Detects (model.convergence .sphere) (14,139,130) (model.comparison.sphereE2 14 139 9 x)
      (lambdaMultiply 3 c) := by
  obtain ⟨t,ht⟩ := sphere_permanent_first_quotient_lift 14 139 x hx
  dsimp only [KIP126.Literature.sphereFirstQuotient] at ht
  have ht6 := model.sphereDetectionCompatible.homotopy_lambda 14 139 6 t
  rw [ht] at ht6
  have hdiff := detects_sub_filtration (model.convergence .sphere) (14,139,133) hc ht6
  have hdiff3 := lambda_three_preserves_filtration_fifteen _ hdiff
  have hlin : lambdaMultiply 3 (c-(show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 t))=
      (show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 c)-
      (show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 (lambdaMultiply 6 t)) := by
    simp only [lambdaMultiply,Preadditive.comp_sub,Nat.cast_ofNat,Int.reduceSub]
  rw [hlin,lambda_three_6_139 t] at hdiff3
  have ht9 := model.sphereDetectionCompatible.homotopy_lambda 14 139 9 t
  rw [ht] at ht9
  exact Choice.detects_of_difference_in_next_filtration (model.convergence .sphere) (14,139,130) ht9 hdiff3

end
end KIP126.Main.Internal.Selected
