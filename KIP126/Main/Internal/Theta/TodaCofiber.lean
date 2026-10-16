module
public import KIP126.Main.Conditions
public import KIP126.Literature.Standard.QuotientAlgebra
public import KIP126.Literature.Standard.Filtration
public import KIP126.Computation.Table.Values
import all KIP126.Main.Internal.NuThree.Shift
import all KIP126.Main.Internal.Choice.OrderTwo
import all KIP126.Main.Internal.Theta.Products

/-! Original lambda-cofiber construction, ThetaToda.lean:79–229,250–390,
526–564, bbac1fc05843 (MIT). The entire cofiber argument is retained. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Toda
open KIP126.Core.SpectralSequence KIP126.Core.Algebra
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
open KIP126.Literature.Standard (quotientSyntheticSymmetric quotientAlgebra quotientAlgebraProduct quotientAlgebra_commutative quotientAlgebra_unit quotientAlgebra_sphere_action quotientAlgebra_first_quotient)
open KIP126.Computation.Standard (product h0 h6 h5Square atom_h0 atom_h5 atom_h6)
open KIP126.Computation.Table
noncomputable section
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive := model.exactness.shiftAdditive p
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem relation_from_middle_cofiber
    {X Y Z W Q : SyntheticSpectrum} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    {i : Z ⟶ Q} {p : Q ⟶ Y⟦(1:ℤ)⟧}
    (hT : Triangle.mk g i p ∈ distTriang SyntheticSpectrum)
    (hfg : f≫g=0)
    (a : X⟦(1:ℤ)⟧ ⟶ Q) (ha : a≫p = -f⟦(1:ℤ)⟧')
    (b : Q ⟶ W) (hb : i≫b=h) :
    Relation (a≫b) f g h := by
  obtain ⟨Qf,j,q,hTf⟩ := distinguished_cocone_triangle f
  let Tf := Triangle.mk f j q
  let Tg := Triangle.mk g i p
  obtain ⟨gbar,hgbar⟩ := Tf.yoneda_exact₂ hTf g hfg
  dsimp only [Tf,Triangle.mk] at gbar hgbar
  have hTfr : Tf.rotate ∈ distTriang SyntheticSpectrum := rot_of_distTriang Tf hTf
  obtain ⟨a0,ha0i,ha0p⟩ := complete_distinguished_triangle_morphism
    Tf.rotate Tg hTfr hT (𝟙 Y) gbar (by
      change j≫gbar=𝟙 Y≫g
      simpa only [Category.id_comp] using hgbar.symm)
  dsimp only [Tf,Tg,Triangle.mk,Triangle.rotate] at a0 ha0i ha0p
  have hai : q≫a0=gbar≫i := ha0i
  have hap : a0≫p = -f⟦(1:ℤ)⟧' := by
    simpa only [CategoryTheory.Functor.map_id,Category.comp_id] using ha0p.symm
  have hdiff : (a-a0)≫p=0 := by
    rw [Preadditive.sub_comp,ha,hap,sub_self]
  obtain ⟨c,hc⟩ := Tg.coyoneda_exact₃ hT (a-a0) hdiff
  dsimp only [Tg,Triangle.mk] at c hc
  have h0 : Relation (a0≫b) f g h := by
    refine ⟨Qf,j,q,hTf,gbar,hgbar.symm,?_⟩
    rw [←Category.assoc,hai,Category.assoc,hb]
  have hsum : a≫b=a0≫b+c≫h := by
    have hh := congrArg (fun z => z≫b) hc
    rw [Preadditive.sub_comp,Category.assoc,hb] at hh
    exact (sub_eq_iff_eq_add'.mp hh)
  rw [hsum]
  apply (relation_iff_indeterminacy h0).mpr
  refine ⟨0,c,?_⟩
  simp only [comp_zero,zero_add,add_sub_cancel_left]
private theorem sphere_two_factors_lambda_nonzero
    (coh:BiShiftCoherence SyntheticSpectrum) (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (hlambda:lambdaMultiply 1 h0=syntheticTwo) :
    ∃ k:Smn (Syn:=SyntheticSpectrum) 62 70⟶(SyntheticCategory.biShift (0,-1)).obj (Smn 62 70),
      k≫lambdaPow 1 (Smn 62 70)=2 • 𝟙 (Smn 62 70) ∧
      ∀theta:BiHom 62 64 (S_0_0:SyntheticSpectrum),sphereProduct theta h0≠0 →
        (SyntheticCategory.biShift (62,70)).map theta≫k≠0 := by
  let S := (S_0_0:SyntheticSpectrum)
  let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let E:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (62,70)
  let k0:S⟶F.obj S := SyntheticCategory.biShift_zero.inv.app S≫
    (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S≫F.map h0
  have hk0:k0≫SyntheticCategory.lam.app S=2 • 𝟙 S := by
    have hn:=SyntheticCategory.lam.naturality h0
    dsimp only [Functor.id_map] at hn
    have hh:=congrArg (fun f=>SyntheticCategory.biShift_zero.inv.app S≫f) hlambda
    dsimp only [lambdaMultiply,syntheticTwo] at hh
    rw [lambdaPow_one coh] at hh
    simp only [eqToHom_refl,Category.id_comp] at hh
    change SyntheticCategory.biShift_zero.inv.app S ≫
      (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S ≫ SyntheticCategory.lam.app (Smn 0 1)≫h0 =
      SyntheticCategory.biShift_zero.inv.app S≫SyntheticCategory.biShift_zero.hom.app S≫(2 • 𝟙 S) at hh
    dsimp only [k0]
    simp only [Category.assoc]
    rw [hn]
    simpa only [S,Functor.id_obj,Category.assoc,Iso.inv_hom_id_app_assoc] using hh
  let e : F.obj (E.obj S) ≅ E.obj (F.obj S) :=
    (biShiftAddIso (62,70) (0,-1) ((62,70)+(0,-1)) rfl).app S ≪≫
      ((biShiftAddIso (0,-1) (62,70) ((62,70)+(0,-1)) (add_comm _ _)).app S).symm
  have he : SyntheticCategory.lam.app (E.obj S)=e.hom≫E.map (SyntheticCategory.lam.app S) := by
    have hh:=coh.lambda_comm (62,70) S
    simpa only [E,e,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc] using hh
  refine ⟨E.map k0≫e.inv,?_,?_⟩
  · change (E.map k0≫e.inv)≫lambdaPow 1 (E.obj S)=2 • 𝟙 (E.obj S)
    rw [lambdaPow_one coh,he]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    rw [←Functor.map_comp,hk0]
    simp [two_smul]
  · intro theta hprod hz
    have hmap:E.map (theta≫k0)≫e.inv=0 := by
      simpa only [Functor.map_comp,Category.assoc] using hz
    have hmap':E.map (theta≫k0)=0 := by
      apply (cancel_mono e.inv).mp
      simpa only [zero_comp] using hmap
    have hk:theta≫k0=0 := by
      apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (62,70)).map_injective
      simpa only [Functor.map_zero] using hmap'
    have hn:=(SyntheticCategory.biShift_zero (Syn:=SyntheticSpectrum)).inv.naturality theta
    have hn':=(SyntheticCategory.biShift_comp (Syn:=SyntheticSpectrum) (0,1) (0,-1)).inv.naturality theta
    dsimp only [Functor.id_map] at hn
    have hn0:theta≫SyntheticCategory.biShift_zero.inv.app S =
        SyntheticCategory.biShift_zero.inv.app (Smn 62 64)≫
          (SyntheticCategory.biShift (0,0)).map theta := hn
    have hn1:(SyntheticCategory.biShift (0,0)).map theta≫
        (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S =
        (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app (Smn 62 64)≫
          F.map ((SyntheticCategory.biShift (0,1)).map theta) := hn'
    dsimp only [k0] at hk
    have hh :
        SyntheticCategory.biShift_zero.inv.app (Smn 62 64)≫
        (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app (Smn 62 64)≫
        F.map ((SyntheticCategory.biShift (0,1)).map theta≫h0)=0 := by
      rw [Functor.map_comp]
      have hN0:=congrArg (fun q => q≫(SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S≫F.map h0) hn0
      have hN1:=congrArg (fun q => SyntheticCategory.biShift_zero.inv.app (Smn 62 64)≫q≫F.map h0) hn1
      simp only [Category.assoc] at hN0 hN1
      rw [←hN1,←hN0]
      exact hk
    have hF:F.map ((SyntheticCategory.biShift (0,1)).map theta≫h0)=0 := by
      simpa only [comp_eq_zero_iff_of_epi] using hh
    have hraw:(SyntheticCategory.biShift (0,1)).map theta≫h0=0 := by
      apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-1)).map_injective
      simpa only [Functor.map_zero] using hF
    apply hprod
    unfold sphereProduct
    rw [hraw,comp_zero]
private theorem theta_b_actual_lambda_cofiber_candidate_universal
    (coh:BiShiftCoherence SyntheticSpectrum) (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (hlambda:lambdaMultiply 1 h0=syntheticTwo)
    (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum)) (htheta:theta+theta=0)
    (hprod:sphereProduct theta h0≠0) (b:BiHom 62 70 (S_0_0:SyntheticSpectrum)) :
    ∃ a:((SyntheticCategory.biShift (62,70)).obj (Smn (Syn:=SyntheticSpectrum) 62 64))⟦(1:ℤ)⟧⟶
        XModLambdaN (Smn (Syn:=SyntheticSpectrum) 62 70) 1,
      a≠0 ∧ ∀ r:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 62 70) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 62 70) 1≫r=quotientClass 1 b →
        Toda.Relation (a≫r)
        ((SyntheticCategory.biShift (62,70)).map theta)
        (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b) := by
  obtain ⟨k,hk,hkn⟩:=sphere_two_factors_lambda_nonzero coh h0 hlambda
  let f:=(SyntheticCategory.biShift (62,70)).map theta
  let Y:=(Smn (Syn:=SyntheticSpectrum) 62 70)
  let T:=XModLambdaN.cofiberTriangle Y 1
  have hT:T∈distTriang SyntheticSpectrum:=HasFunctorialCofiber.cofib_distinguished _
  have hfg:(f≫k)≫lambdaPow 1 Y=0 := by
    rw [Category.assoc,hk]
    have hf:f+f=0 := by
      dsimp only [f]
      rw [←Functor.map_add,htheta,Functor.map_zero]
    simpa [Y,f,Smn,two_smul,Preadditive.comp_add] using hf
  have hm:(-(f≫k)⟦(1:ℤ)⟧')≫(lambdaPow 1 Y)⟦(1:ℤ)⟧'=0 := by
    rw [Preadditive.neg_comp,←Functor.map_comp,hfg,Functor.map_zero,neg_zero]
  obtain ⟨a,ha⟩:=T.coyoneda_exact₁ hT (-(f≫k)⟦(1:ℤ)⟧') hm
  dsimp only [T,XModLambdaN.cofiberTriangle,Triangle.mk] at a ha
  refine ⟨a,?_,?_⟩
  · intro ha0
    apply hkn theta hprod
    apply (shiftFunctor SyntheticSpectrum (1:ℤ)).map_injective
    rw [ha0,zero_comp] at ha
    simpa only [Functor.map_zero] using neg_eq_zero.mp ha
  intro r hr
  have hrel:=relation_from_middle_cofiber hT hfg a ha.symm r hr
  have hr':Toda.Relation (a≫r) (f≫k)
      (lambdaPow 1 Y) (quotientClass 1 b) := hrel
  have hh:=Toda.absorb_first hr'
  rw [hk] at hh
  exact hh
private theorem quotient_algebra_product_zero_swap
     (m n k l:ℤ) :
    letI:=quotientSyntheticSymmetric
    ∀ (x:BiHom m n (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (y:BiHom k l (XModLambdaN (S_0_0:SyntheticSpectrum) 1)),
      quotientAlgebraProduct (quotientAlgebra 1 (by decide)) x y=0 →
      quotientAlgebraProduct (quotientAlgebra 1 (by decide)) y x=0 := by
  letI:=quotientSyntheticSymmetric
  intro x y h
  let Q:=quotientAlgebra 1 (by decide)
  letI:=Q
  letI:=quotientAlgebra_commutative 1 (by decide)
  have hh:(y⊗ₘx)≫Q.mul=0 := by
    simpa only [quotientAlgebraProduct,Category.assoc,comp_eq_zero_iff_of_epi] using h
  have hz:(x⊗ₘy)≫Q.mul=0 := by
    have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
    change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫Q.mul=Q.mul at hc
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc,hh,comp_zero]
  dsimp only [quotientAlgebraProduct]
  rw [hz,comp_zero,comp_zero]

private theorem theta_h0_first_nonzero
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (h0label : (KIP126.Literature.sphereFirstQuotient model) 1 1 (quotientClass 1 h0)=KIP126.Computation.Standard.h0)
    (htheta : ThetaChoice theta) :
    (KIP126.Literature.sphereFirstQuotient model) 3 65 (quotientClass 1 (sphereProduct h0 theta))≠0 := by
  have hm := KIP126.Literature.Standard.first_quotient_action 1 1 2 64 h0 (quotientClass 1 theta)
  change (KIP126.Literature.sphereFirstQuotient model) 3 65 (sphereAction h0 (quotientClass 1 theta)) =
    product ((KIP126.Literature.sphereFirstQuotient model) 1 1 (quotientClass 1 h0))
      ((KIP126.Literature.sphereFirstQuotient model) 2 64 (quotientClass 1 theta)) at hm
  have ht : (KIP126.Literature.sphereFirstQuotient model) 2 64 (quotientClass 1 theta)=h5Square := htheta
  rw [h0label,ht] at hm
  have hp : product (r := (3,65)) KIP126.Computation.Standard.h0 h5Square ≠ 0 := by
    obtain ⟨z,hz,hzne⟩ := KIP126.Computation.Standard.d2_h6.target_survives
    intro hh
    exact hzne (hz.eq_on_page_two.symm.trans hh)
  intro hz
  apply hp
  exact hm.symm.trans (by simpa only [sphereAction,sphereProduct,quotientClass,Category.assoc] using hz)

private theorem theta_h0_right_nonzero


 (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum)) (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum))
 (h0label:(KIP126.Literature.sphereFirstQuotient model) 1 1 (quotientClass 1 h0)=KIP126.Computation.Standard.h0)
 (htheta:ThetaChoice theta) : sphereProduct theta h0≠0 := by
 letI:=quotientSyntheticSymmetric
 intro hz
 have hq:quotientAlgebraProduct (quotientAlgebra 1 (by decide))
     (quotientClass 1 theta) (quotientClass 1 h0)=0 := by
   have hact:=quotientAlgebra_sphere_action 1 (by decide) 62 64 0 1 theta (quotientClass 1 h0)
   change quotientAlgebraProduct (quotientAlgebra 1 (by decide))
     (quotientClass 1 theta) (quotientClass 1 h0)=sphereAction theta (quotientClass 1 h0) at hact
   rw [hact]
   have hh:=congrArg (quotientClass 1) hz
   simpa only [quotientClass,sphereProduct,sphereAction,Category.assoc,zero_comp] using hh
 have hq':=quotient_algebra_product_zero_swap 62 64 0 1
   (quotientClass 1 theta) (quotientClass 1 h0) hq
 have hact:=quotientAlgebra_sphere_action 1 (by decide) 0 1 62 64 h0 (quotientClass 1 theta)
 change quotientAlgebraProduct (quotientAlgebra 1 (by decide))
   (quotientClass 1 h0) (quotientClass 1 theta)=sphereAction h0 (quotientClass 1 theta) at hact
 rw [hact] at hq'
 apply theta_h0_first_nonzero h0 theta h0label htheta
 have heq:quotientClass 1 (sphereProduct h0 theta)=0 := by
   simpa only [quotientClass,sphereProduct,sphereAction,Category.assoc] using hq'
 rw [heq,map_zero]

private theorem q1_nonzero_is_h6
    (u : BiHom 63 64 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) (hune : u≠0) :
    (KIP126.Literature.sphereFirstQuotient model) 1 64 u=h6 := by
  classical
  have hs := basis_value ⟨.named .h6,0⟩ (by decide)
  change basis .sphere 1 64 0=KIP126.Computation.Standard.atom .h6 at hs
  rw [atom_h6] at hs
  let x := (KIP126.Literature.sphereFirstQuotient model) 1 64 u
  have hxne : x≠0 := by
    intro h
    apply hune
    apply (KIP126.Literature.sphereFirstQuotient model 1 64).injective
    exact h.trans (map_zero _).symm
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,1,64,["69,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 85) rfl)
  change model.classical.sphere.Page 2 (1,64) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀i:Fin 1,e.symm (Finsupp.single i 1)=basis .sphere 1 64 i.val at he
  have heq : e x=Finsupp.single 0 (e x 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc:e x 0=c at hxe
  fin_cases c
  · simp only [show (⟨0,by decide⟩:F2)=0 from rfl,Finsupp.single_zero,map_zero] at hxe
    exact (hxne hxe).elim
  · change x=e.symm (Finsupp.single 0 1) at hxe
    exact hxe.trans ((he 0).trans hs)

private theorem theta_b_actual_h6_cofiber_candidate_universal


 (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum)) (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum))
 (h0label:(KIP126.Literature.sphereFirstQuotient model) 1 1 (quotientClass 1 h0)=KIP126.Computation.Standard.h0)
 (htheta:ThetaChoice theta)
 (hlambda:lambdaMultiply 1 h0=syntheticTwo) (horder:theta+theta=0)
 (b:BiHom 62 70 (S_0_0:SyntheticSpectrum)) :
 ∃ (e:(SyntheticCategory.biShift (62,70)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
       XModLambdaN (Smn (Syn:=SyntheticSpectrum) 62 70) 1)
   (a:((SyntheticCategory.biShift (62,70)).obj (Smn (Syn:=SyntheticSpectrum) 62 64))⟦(1:ℤ)⟧⟶
       XModLambdaN (Smn (Syn:=SyntheticSpectrum) 62 70) 1)
   (u:BiHom 63 64 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)),
   (SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
       XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 62 70) 1 ∧
   susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) u=
     (tripleTodaSource (Syn:=SyntheticSpectrum) 62 64 0 0 62 70).hom≫a≫e.inv ∧
   u≠0 ∧ (KIP126.Literature.sphereFirstQuotient model) 1 64 u=h6 ∧
   (∀ r:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 62 70) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1,
     XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 62 70) 1≫r=quotientClass 1 b →
     Toda.Relation (a≫r) ((SyntheticCategory.biShift (62,70)).map theta)
     (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b)) := by
 letI:=model.exactness.shiftAdditive
 obtain ⟨a,ha,hrel⟩:=theta_b_actual_lambda_cofiber_candidate_universal model.quotients.coherence h0 hlambda
   theta horder (theta_h0_right_nonzero h0 theta h0label htheta) b
 obtain ⟨e,he⟩:=NuThree.quotient_shift_iso (62,70) (S_0_0:SyntheticSpectrum) 1
 let src:=tripleTodaSource (Syn:=SyntheticSpectrum) 62 64 0 0 62 70
 let u:BiHom 63 64 (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=
   (susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).symm (src.hom≫a≫e.inv)
 have hu:susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) u=src.hom≫a≫e.inv :=
   Equiv.apply_symm_apply _ _
 have hun:u≠0 := by
   intro hz
   apply ha
   apply (cancel_mono e.inv).mp
   apply (cancel_epi src.hom).mp
   rw [hz] at hu
   simpa [susp_invariance] using hu.symm
 exact ⟨e,a,u,he,hu,hun,q1_nonzero_is_h6 u hun,hrel⟩


end
end KIP126.Main.Internal.Theta
