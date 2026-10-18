module
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.WeakStrip
import all KIP126.Main.Internal.Selected.LambdaOperations
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.SectionSeven.ThetaEta
/-! Final nonzero-preserving removal in WeakRepresentative.lean:2649–2973,
bbac1fc05843 (MIT). The finite layers and theta–eta vanishing are proved
in their shared internal files; no result package is an input. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem main_h0_right_two_132
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    {X : SyntheticSpectrum} (c : BiHom 125 132 X) :
    sphereAction h0 (lambdaMultiply 2 c) = lambdaMultiply 2 (sphereAction h0 c) := by
  have ha := shift_assoc_inv graded_coherence (0,1) (125,132) (0,-2)
    (125,133) (125,130) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (0,1) (125,132)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift (125,132)).map h0))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,132) (0,-2)).inv.naturality h0)]
  rfl
private theorem main_h0_right_two_134
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    {X : SyntheticSpectrum} (c : BiHom 125 134 X) :
    sphereAction h0 (lambdaMultiply 2 c) = lambdaMultiply 2 (sphereAction h0 c) := by
  have ha := shift_assoc_inv graded_coherence (0,1) (125,134) (0,-2)
    (125,135) (125,132) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (0,1) (125,134)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift (125,134)).map h0))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,134) (0,-2)).inv.naturality h0)]
  rfl
private theorem main_lambda_two_three_136
    {X : SyntheticSpectrum} (c : BiHom 125 136 X) :
    lambdaMultiply 2 (lambdaMultiply 3 c) = lambdaMultiply 5 c := by
  have ha := shift_assoc_inv graded_coherence (125,136) (0,-3) (0,-2)
    (125,133) (0,-5) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 2 (lambdaPow 3 (Smn 125 136)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add graded_coherence 3 2 5 (by decide) (Smn 125 136)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl
private theorem main_af7_correction_killed
     (h0 : BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (c : BiHom 125 132 (S_0_0:SyntheticSpectrum)) (hc : lambdaMultiply 2 c=0) :
    lambdaMultiply 2 (sphereAction h0 (quotientClass 9 c))=0 := by
  have hh := main_h0_right_two_132 h0 c
  rw [hc] at hh
  have hz : lambdaMultiply 2 (sphereAction h0 c)=0 := by
    exact hh.symm.trans (by simp only [sphereAction,Limits.comp_zero])
  simpa only [lambdaMultiply,sphereAction,quotientClass,Category.assoc,Limits.zero_comp] using
    congrArg (fun a => a≫XModLambdaN.incl (S_0_0:SyntheticSpectrum) 9) hz
private theorem main_af9_correction_killed
     (h0 : BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (z : BiHom 125 134 (S_0_0:SyntheticSpectrum))
    (p : BiHom 125 136 (S_0_0:SyntheticSpectrum))
    (hz : quotientClass 9 (lambdaMultiply 2 (sphereAction h0 z))=
      quotientClass 9 (lambdaMultiply 3 p))
    (hp : quotientClass 9 (lambdaMultiply 5 p)=0) :
    lambdaMultiply 2 (sphereAction h0 (quotientClass 9 (lambdaMultiply 2 z)))=0 := by
  have hq : quotientClass 9 (lambdaMultiply 2 (sphereAction h0 (lambdaMultiply 2 z))) =
      quotientClass 9 (lambdaMultiply 5 p) := by
    rw [main_h0_right_two_134]
    have hq' : quotientClass 9 (lambdaMultiply 2 (lambdaMultiply 2 (sphereAction h0 z))) =
        quotientClass 9 (lambdaMultiply 2 (lambdaMultiply 3 p)) := by
      simpa only [quotientClass,lambdaMultiply,Category.assoc,
        Nat.cast_ofNat,Int.reduceAdd,Int.reduceSub] using congrArg (lambdaMultiply 2) hz
    rw [main_lambda_two_three_136] at hq'
    exact hq'
  rw [hp] at hq
  simpa only [lambdaMultiply,sphereAction,quotientClass,Category.assoc] using hq
private theorem sphere_zero_weight_label_9_134
    (x : model.classical.sphere.Page 2 (9,134))
    (a : BiHom 125 134 (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (9,134,134)
      (model.comparison.sphereE2 9 134 0 x) a) :
    sphereFirstQuotient model 9 134 (quotientClass 1 a)=x := by
  let y := sphereFirstQuotient model 9 134 (quotientClass 1 a)
  have hd := detects_map .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1) (9,134,134) _ a ha
  have hd' := model.sphereDetectionCompatible.first_quotient 9 134 y
  have hy : (sphereFirstQuotient model 9 134).symm y=quotientClass 1 a :=
    (sphereFirstQuotient model 9 134).symm_apply_apply _
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hy
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := detects_infinity_equal (.quotient 1 .sphere) (9,134,134)
    (quotientClass 1 a) _ _ hd hd'
  let g := XModLambdaN.map model.nu.unitIso.inv 1
  have he' := family_infinity_representative_map g (9,134,134) _ _ he
  have hf' := family_infinity_representative_map g (9,134,134) _ _ hf
  change HasInfinityRepresentative _ 2 (9,134,134)
    (familyPageMap model.family g 2 (9,134,134) (quotientLabel 1 9 134 0 x)) _ at he'
  change HasInfinityRepresentative _ 2 (9,134,134)
    (familyPageMap model.family g 2 (9,134,134) (quotientLabel 1 9 134 0 y)) _ at hf'
  have hlx := sphere_quotient_label_to_nu 1 0 9 134 x
  have hly := sphere_quotient_label_to_nu 1 0 9 134 y
  change familyPageMap model.family g 2 (9,134,134) (quotientLabel 1 9 134 0 x)=_ at hlx
  change familyPageMap model.family g 2 (9,134,134) (quotientLabel 1 9 134 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  have hi (v : model.classical.sphere.Page 2 (9,134)) :=
    KIP126.Literature.Standard.eInfinity_finite_labels .sphere 1 (by decide)
      9 134 134 (by decide) v ((model.family.map g).eInftyMap (9,134,134) e)
  obtain ⟨hx,hxq⟩ := (hi x).mp he'
  obtain ⟨hy,hyq⟩ := (hi y).mp hf'
  let xx : cycles model .sphere 1 (9,134) := ⟨x,hx⟩
  let yy : cycles model .sphere 1 (9,134) := ⟨y,hy⟩
  have heq : subquotientClass _ (boundaries model .sphere 1 (9,134)) xx =
      subquotientClass _ (boundaries model .sphere 1 (9,134)) yy := hxq.symm.trans hyq
  have hz : subquotientClass _ (boundaries model .sphere 1 (9,134)) (xx-yy)=0 := by
    rw [map_sub,heq,sub_self]
  have hm := (subquotientClass_eq_zero_iff _ _ (xx-yy)).mp hz
  change x-y ∈ boundaries model .sphere 1 (9,134) at hm
  rw [boundaries_one model .sphere (9,134),Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm


private theorem h6b_basis_label : KIP126.Computation.Table.basis .sphere 9 134 2 =
    KIP126.Computation.Standard.product (r := (9,134)) KIP126.Computation.Standard.h6
      (KIP126.Computation.Standard.atom .b) := by
  have h := KIP126.Computation.Table.basis_value ⟨.mul (.named .h6) (.named .b),2⟩ (by decide)
  simpa only [KIP126.Computation.Table.Expression.value,KIP126.Computation.Table.Expression.degree,
    KIP126.Computation.Standard.atom_h6] using h

private theorem main_af9_correction_detected
    (z : BiHom 125 134 (S_0_0 : SyntheticSpectrum))
    (hz : SphereDetected 9 134 0 (KIP126.Computation.Standard.product (r := (9,134))
      KIP126.Computation.Standard.h6 (KIP126.Computation.Standard.atom .b)) z) :
    Detects (model.convergence (.quotient 9 .sphere)) (9,134,132)
      (quotientLabel 9 9 134 2 (KIP126.Computation.Table.basis .sphere 9 134 2))
      (quotientClass 9 (lambdaMultiply 2 z)) := by
  have hfirst := sphere_zero_weight_label_9_134 _ z hz.1
  have hl := model.sphereDetectionCompatible.homotopy_lambda 9 134 2 z
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hfirst
  rw [hfirst,←h6b_basis_label] at hl
  exact detects_map .sphere (.quotient 9 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 9) (9,134,132) _ (lambdaMultiply 2 z) hl

private theorem main_strip_preserving_nonzero
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (zTheta : BiHom 125 134 (S_0_0 : SyntheticSpectrum))
    (hzTheta : SphereDetected 9 134 0 (KIP126.Computation.Standard.product (r := (9,134))
      KIP126.Computation.Standard.h6 (KIP126.Computation.Standard.atom .b)) zTheta)
    (p : BiHom 125 136 (S_0_0 : SyntheticSpectrum))
    (hshuffle : quotientClass 9 (lambdaMultiply 2 (sphereAction h0 zTheta))=
      quotientClass 9 (lambdaMultiply 3 p))
    (hp : quotientClass 9 (lambdaMultiply 5 p)=0)
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hzn : lambdaMultiply 2 (sphereAction h0 z)≠0) :
    ∃ y : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiltrationAtLeast model.syntheticTower 11 y ∧ lambdaMultiply 2 (sphereAction h0 y)≠0 := by
  let Phi : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) →+
      BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := {
    toFun := fun a => lambdaMultiply 2 (sphereAction h0 a)
    map_zero' := by simp only [sphereAction,lambdaMultiply,comp_zero]
    map_add' := by intro a b; simp only [sphereAction,lambdaMultiply,Preadditive.comp_add] }
  have hc9 := main_af9_correction_detected zTheta hzTheta
  have hkill9 : Phi (quotientClass 9 (lambdaMultiply 2 zTheta))=0 :=
    main_af9_correction_killed h0 zTheta p hshuffle hp
  obtain ⟨y,hy,he⟩ := main_two_layer_strip (quotientClass 9 (lambdaMultiply 2 zTheta)) hc9 Phi
    (fun c hc => main_af7_correction_killed h0 c hc) hkill9 z
  exact ⟨y,hy,fun h => hzn (he.symm.trans h)⟩


theorem main_weak_high_representative
    (eta : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (heta : KIP126.Literature.sphereFirstQuotient model 1 2 (quotientClass 1 eta)=KIP126.Computation.Standard.h1)
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (htheta : ThetaChoice theta)
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum))
    (hb : SphereDetected 8 70 0 (KIP126.Computation.Standard.atom .b) b)
    (zTheta : BiHom 125 134 (S_0_0 : SyntheticSpectrum))
    (hzTheta : SphereDetected 9 134 0 (KIP126.Computation.Standard.product (r := (9,134))
      KIP126.Computation.Standard.h6 (KIP126.Computation.Standard.atom .b)) zTheta)
    (hshuffle : quotientClass 9 (lambdaMultiply 2 (sphereProduct h0 zTheta))=
      quotientClass 9 (lambdaMultiply 3 (sphereProduct eta (sphereProduct theta b))))
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hzn : lambdaMultiply 2 (sphereAction h0 z)≠0) :
    ∃ y : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiltrationAtLeast model.syntheticTower 11 y ∧ lambdaMultiply 2 (sphereAction h0 y)≠0 := by
  exact main_strip_preserving_nonzero h0 zTheta hzTheta
    (sphereProduct eta (sphereProduct theta b)) hshuffle
    (theta_b_eta_fifth_mod_nine_zero_from_choice eta heta theta htheta b hb) z hzn

end
end KIP126.Main.SectionSeven.Internal
