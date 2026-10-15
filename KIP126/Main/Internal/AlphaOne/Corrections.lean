module
public import KIP126.Main.SectionSeven.AlphaOne
public import KIP126.Def.ProofTools.Operations
import all KIP126.Main.Internal.AlphaOne.Coherence
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.Internal.Selected.LambdaOperations

/-! Exact correction choices and eta-divisibility, AlphaOne/Existence.lean:
1950–2045,2094–2160, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations KIP126.Main.Internal KIP126.Literature
open KIP126.Main.Internal.Selected (detects_infinity_equal)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
private theorem sphere_zero_weight_label_14_139
    (x : model.classical.sphere.Page 2 (14,139))
    (a : BiHom 125 139 (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (14,139,139)
      (model.comparison.sphereE2 14 139 0 x) a) :
    sphereFirstQuotient model 14 139 (quotientClass 1 a)=x := by
  let y := sphereFirstQuotient model 14 139 (quotientClass 1 a)
  have hd := detects_map .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1) (14,139,139) _ a ha
  have hd' := model.sphereDetectionCompatible.first_quotient 14 139 y
  have hy : (sphereFirstQuotient model 14 139).symm y=quotientClass 1 a :=
    (sphereFirstQuotient model 14 139).symm_apply_apply _
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hy
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := detects_infinity_equal (.quotient 1 .sphere) (14,139,139)
    (quotientClass 1 a) _ _ hd hd'
  let g := XModLambdaN.map model.nu.unitIso.inv 1
  have he' := family_infinity_representative_map g (14,139,139) _ _ he
  have hf' := family_infinity_representative_map g (14,139,139) _ _ hf
  change HasInfinityRepresentative _ 2 (14,139,139)
    (familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 x)) _ at he'
  change HasInfinityRepresentative _ 2 (14,139,139)
    (familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 y)) _ at hf'
  have hlx := sphere_quotient_label_to_nu 1 0 14 139 x
  have hly := sphere_quotient_label_to_nu 1 0 14 139 y
  change familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 x)=_ at hlx
  change familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  have hi (v : model.classical.sphere.Page 2 (14,139)) :=
    KIP126.Literature.Standard.eInfinity_finite_labels .sphere 1 (by decide)
      14 139 139 (by decide) v ((model.family.map g).eInftyMap (14,139,139) e)
  obtain ⟨hx,hxq⟩ := (hi x).mp he'
  obtain ⟨hy,hyq⟩ := (hi y).mp hf'
  let xx : cycles model .sphere 1 (14,139) := ⟨x,hx⟩
  let yy : cycles model .sphere 1 (14,139) := ⟨y,hy⟩
  have heq : subquotientClass _ (boundaries model .sphere 1 (14,139)) xx =
      subquotientClass _ (boundaries model .sphere 1 (14,139)) yy := hxq.symm.trans hyq
  have hz : subquotientClass _ (boundaries model .sphere 1 (14,139)) (xx-yy)=0 := by
    rw [map_sub,heq,sub_self]
  have hm := (subquotientClass_eq_zero_iff _ _ (xx-yy)).mp hz
  change x-y ∈ boundaries model .sphere 1 (14,139) at hm
  rw [boundaries_one model .sphere (14,139),Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm

private theorem eta_correction_lambda_divisible
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum)) (c : BiHom 124 137 (S_0_0 : SyntheticSpectrum))
    (x : model.classical.sphere.Page 2 (13,137))
    (hη : KIP126.Literature.sphereFirstQuotient model 1 2 (quotientClass 1 η)=KIP126.Computation.Standard.h1)
    (hc : KIP126.Literature.sphereFirstQuotient model 13 137 (quotientClass 1 c)=x)
    (hp : KIP126.Computation.Standard.product (r := (14,139)) (KIP126.Computation.Standard.h1) x=0) :
    ∃ b : BiHom 125 140 (S_0_0 : SyntheticSpectrum), lambdaMultiply 1 b=sphereAction η c := by
  classical
  have hη0 : lambdaMultiply 0 η=η := by
    have hc := model.quotients.coherence.right_unit (1,2) (S_0_0 : SyntheticSpectrum)
    have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : SyntheticSpectrum) := by
      change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ η=η
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hc0 : lambdaMultiply 0 c=c := by
    have hc := model.quotients.coherence.right_unit (124,137) (S_0_0 : SyntheticSpectrum)
    have he : (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn 124 137 : SyntheticSpectrum) := by
      change (biShiftAddIso (124,137) (0,0) (124,137) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (124,137) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ c=c
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hηd := model.sphereDetectionCompatible.homotopy_lambda 1 2 0 η
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hη
  rw [hη0,hη] at hηd
  have hcd := model.sphereDetectionCompatible.homotopy_lambda 13 137 0 c
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hc
  rw [hc0,hc] at hcd
  have hd := model.multiplicationCompatible 1 2 13 137 0 0 (KIP126.Computation.Standard.h1) x η c hηd hcd
  change Detects (model.convergence .sphere) (14,139,139-0)
    (model.comparison.sphereE2 14 139 0 (KIP126.Computation.Standard.product (r := (14,139)) (KIP126.Computation.Standard.h1) x))
    (sphereAction η c) at hd
  rw [hp] at hd
  have hfirst := sphere_zero_weight_label_14_139 0 (sphereAction η c) hd
  have hzero : quotientClass 1 (sphereAction η c)=0 := by
    apply (KIP126.Literature.sphereFirstQuotient model 14 139).injective
    exact hfirst.trans (map_zero (KIP126.Literature.sphereFirstQuotient model 14 139)).symm
  exact lambda_one_division_of_quotient_zero 125 140 (sphereAction η c) hzero



private theorem alpha_h0_rho_zero
    (hzero : ∀ a : BiHom 123 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiltrationAtLeast model.syntheticTower 16 a → a=0)
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (ha : FiltrationAtLeast model.syntheticTower 17
      (lambdaMultiply 3 (sphereAction h0 a))) :
    lambdaMultiply 3 (sphereAction h0 (a≫(model.quotients.tower S_0_0).rho 9 11 (by decide)))=0 := by
  classical
  apply hzero
  have h := Selected.map_filtration (.quotient 11 .sphere) (.quotient 9 .sphere) ((model.quotients.tower S_0_0).rho 9 11 (by decide)) (lambdaMultiply 3 (sphereAction h0 a)) ha
  have h16 : FiltrationAtLeast model.syntheticTower 16
      (lambdaMultiply 3 (sphereAction h0 a)≫(model.quotients.tower S_0_0).rho 9 11 (by decide)) :=
    model.syntheticTower.filtrationSubmodule_antitone _ _ (by decide : (16:ℤ)≤17) h
  simpa only [lambdaMultiply,sphereAction,Category.assoc] using h16


private theorem alpha_correction_sum
    (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    (c13 : BiHom 124 137 (S_0_0 : SyntheticSpectrum))
    (c14 : BiHom 124 138 (S_0_0 : SyntheticSpectrum))
    (c15 : BiHom 124 139 (S_0_0 : SyntheticSpectrum))
    (b : BiHom 125 140 (S_0_0 : SyntheticSpectrum)) (hb : lambdaMultiply 1 b=sphereAction η c13)
    (b13 b14 b15 : Bool) :
    ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
      (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
      (if b13 then (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 6 (quotientClass 9 c13)) else 0)+
      (if b14 then (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 7 (quotientClass 9 c14)) else 0)+
      (if b15 then (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 8 (quotientClass 9 c15)) else 0)=lambdaMultiply 6 a2 ∧
      sphereAction η a2=lambdaMultiply 1 a3 := by
  classical
  have lam_add {m w : ℤ} {X : SyntheticSpectrum} (n : ℕ) (a b : BiHom m w X) :
      lambdaMultiply n (a+b)=lambdaMultiply n a+lambdaMultiply n b := by
    simp only [lambdaMultiply,Preadditive.comp_add]
  have lam_if {m w : ℤ} {X : SyntheticSpectrum} (n : ℕ) (a : BiHom m w X) (b : Bool) :
      lambdaMultiply n (if b then a else 0)=(if b then lambdaMultiply n a else 0) := by
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,lambdaMultiply,comp_zero]
  have act_add {m w : ℤ} {X : SyntheticSpectrum} (a b : BiHom m w X) :
      sphereAction η (a+b)=sphereAction η a+sphereAction η b := by
    simp only [sphereAction,Preadditive.comp_add]
  have act_if {m w : ℤ} {X : SyntheticSpectrum} (a : BiHom m w X) (b : Bool) :
      sphereAction η (if b then a else 0)=(if b then sphereAction η a else 0) := by
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,sphereAction,comp_zero]
  let c : BiHom 124 137 (S_0_0 : SyntheticSpectrum) := (if b13 then c13 else 0)+
    (if b14 then (show BiHom 124 137 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 c14) else 0)+
    (if b15 then (show BiHom 124 137 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 2 c15) else 0)
  let d : BiHom 125 140 (S_0_0 : SyntheticSpectrum) := (if b13 then b else 0)+
    (if b14 then (show BiHom 125 140 (S_0_0 : SyntheticSpectrum) from sphereAction η c14) else 0)+
    (if b15 then (show BiHom 125 140 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 (sphereAction η c15)) else 0)
  have hlam : lambdaMultiply 6 c=
      (if b13 then (show BiHom 124 131 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 6 c13) else 0)+
      (if b14 then (show BiHom 124 131 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 7 c14) else 0)+
      (if b15 then (show BiHom 124 131 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 8 c15) else 0) := by
    dsimp only [c]
    rw [lam_add,lam_add,lam_if,lam_if,lam_if,lambda_six_one,lambda_six_two]
  have heta : sphereAction η c=lambdaMultiply 1 d := by
    dsimp only [c,d]
    rw [act_add,act_add,act_if,act_if,act_if,lam_add,lam_add,lam_if,lam_if,lam_if,
      hb,sphere_action_right_one,sphere_action_right_two_as_ones]
  refine ⟨quotientClass 9 c,quotientClass 9 d,?_,?_⟩
  · have hh := congrArg (fun a=>a≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 9) hlam
    simp only [Preadditive.add_comp,ite_comp,zero_comp] at hh
    simpa only [lambdaMultiply,quotientClass,Category.assoc] using hh.symm
  · have hh := congrArg (fun a=>a≫XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 9) heta
    simpa only [lambdaMultiply,sphereAction,quotientClass,Category.assoc] using hh



end
end KIP126.Main.Internal.AlphaOne
end
