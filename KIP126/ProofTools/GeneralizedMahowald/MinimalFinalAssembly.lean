module
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.FSourceTransport

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option Elab.async false


private theorem quotient_zero_unshift_up_to_sphere
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,0)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q≫ε.hom=
      (SyntheticCategory.biShift (0,0)).map (XModLambdaN.incl _ q))
    (a : BiHom (t-s) t (XModLambdaN
      ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    ∃ u : Smn (Syn:=SyntheticSpectrum) (t-s) t ≅ Smn (t-s) t,
      quotientUnshift X (0,0) (t-s,t) q ε (homotopyRegrade (by simp) (by simp) a) =
        u.hom≫a≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let Q := model.quotients.functoriality.functor q
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,0)
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,0)
  let εstd : XModLambdaN (F.obj A) q ≅ F.obj (XModLambdaN A q) :=
    Q.mapIso (SyntheticCategory.biShift_zero.app A) ≪≫
      (SyntheticCategory.biShift_zero.app (XModLambdaN A q)).symm
  have hstd : XModLambdaN.incl (F.obj A) q≫εstd.hom=F.map (XModLambdaN.incl A q) := by
    change XModLambdaN.incl (F.obj A) q≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q≫
        SyntheticCategory.biShift_zero.inv.app (XModLambdaN A q)=_
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc]
    have hn := SyntheticCategory.biShift_zero.hom.naturality (XModLambdaN.incl A q)
    change F.map (XModLambdaN.incl A q)≫SyntheticCategory.biShift_zero.hom.app _ =
      SyntheticCategory.biShift_zero.hom.app A≫XModLambdaN.incl A q at hn
    change SyntheticCategory.biShift_zero.hom.app A≫XModLambdaN.incl A q≫
      SyntheticCategory.biShift_zero.inv.app (XModLambdaN A q)=F.map (XModLambdaN.incl A q)
    rw [←Category.assoc,←hn]
    simp only [Category.assoc,Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hc := shifted_quotient_sphere_congruence X X (0,0) q q hq le_rfl ε hε
    ε.hom εstd.hom (hε.trans hstd.symm) (t-s+0) (t+0)
    (homotopyRegrade (by simp) (by simp) a)
  let D := (biShiftAddIso (Syn:=SyntheticSpectrum) (t-s,t) (0,0) (t-s,t)
    (add_zero _)).app S_0_0
  let u : Smn (Syn:=SyntheticSpectrum) (t-s) t ≅ Smn (t-s) t :=
    ff.preimageIso (D≪≫(SyntheticCategory.biShift_zero.app (Smn (t-s) t)).symm)
  have hu : F.map u.hom=D.hom≫SyntheticCategory.biShift_zero.inv.app (Smn (t-s) t) :=
    ff.map_preimage _
  dsimp only [F] at hu
  refine ⟨u,?_⟩
  apply ff.map_injective
  simp only [quotientUnshift,Functor.FullyFaithful.map_preimage]
  rw [hc]
  simp only [Functor.map_comp,hu,Category.assoc]
  rw [←Functor.map_comp]
  change _ = D.hom≫SyntheticCategory.biShift_zero.inv.app (Smn (t-s) t)≫
    F.map (a≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q)
  rw [←SyntheticCategory.biShift_zero.inv.naturality]
  simp only [εstd,Q,Functor.mapIso_hom,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,
    regrade_precomp,D,biShiftAddIso,eqToIso.hom,eqToHom_app,NatTrans.comp_app,
    Functor.id_map,Functor.id_obj,LambdaQuotientFunctoriality.functor,Category.assoc]

private theorem shifted_finite_bottom_detects_exists
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (e s t : ℤ)
    (x : Ambient model X (s,t)) (hx : x∈cycles model X q (s,t)) :
    ∃ b : BiHom (t-s) (t+e) (XModLambdaN
      ((SyntheticCategory.biShift (0,e)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q),
      Detects (model.convergence (.quotient q (.shift (0,e) (.nu X)))) (s,t,t+e)
        (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) b := by
  have hex : ∃ z : ((model.family.obj (XModLambdaN
      ((SyntheticCategory.biShift (0,e)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q)).sequence.ssData
        (s,t,t+e)).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t+e)
        (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) z := by
    have transport {B : SyntheticAdamsSS} {i j : Tridegree} (h : i=j) (v : B.E₂ i)
        (hv : ∃ z : (B.sequence.ssData i).eInfty, HasInfinityRepresentative B 2 i v z) :
        ∃ z : (B.sequence.ssData j).eInfty, HasInfinityRepresentative B 2 j (regradeE2 h v) z := by
      subst j
      exact hv
    exact transport (by simp) _ (shifted_finite_source_exists X q hq e s t x hx)
  obtain ⟨z,hz⟩ := hex
  let F := model.syntheticTower.filtration (XModLambdaN
    ((SyntheticCategory.biShift (0,e)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q)
  let c := model.convergence (.quotient q (.shift (0,e) (.nu X)))
  haveI : Epi (F.toAssociatedGraded s (t-s,t+e)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t+e))).mp
    inferInstance ((c.identification (s,t,t+e)).hom z)
  refine ⟨(F.F s (t-s,t+e)).arrow b,z,hz,b,rfl,hb.symm⟩

private theorem native_bottom_detected_cycles
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a) :
    x∈cycles model X q (s,t) := by
  have hfirst := finite_detected_bottom_first X q hq s t x a
    (by rw [zero_weight_label X q s t x]; exact ha)
  exact first_label_lift_cycles X q hq s t x a hfirst


private theorem native_bottom_detected_first_lift
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a) :
    ∃ c : BiHom (t-s) t (XModLambdaN (nuZero model X) q),
      c≫(model.quotients.tower (nuZero model X)).rho 1 q hq=firstLabel model X s t x := by
  have hfirst := finite_detected_bottom_first X q hq s t x a
    (by rw [zero_weight_label X q s t x]; exact ha)
  let v := SyntheticCategory.biShift_zero.inv.app (model.nu.functor.obj (X.obj model.auxiliary))
  refine ⟨a≫XModLambdaN.map v q,?_⟩
  rw [Category.assoc,←(model.quotients.natural v).rho_naturality hq,←Category.assoc]
  change (a≫(model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho 1 q hq)≫
    XModLambdaN.map v 1=firstLabel model X s t x
  rw [hfirst,Category.assoc,←model.quotients.functoriality.map_comp]
  simp only [v,Iso.hom_inv_id_app,model.quotients.functoriality.map_id,Category.comp_id]

private theorem positive_finite_source_refold
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε₁ : XModLambdaN.incl _ 1≫ε₁.hom=
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ 1))
    (hεq : XModLambdaN.incl _ q≫εq.hom=
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ q))
    (a : BiHom (t-s) (t+1) (XModLambdaN
      ((SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
      (quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl a))) :
    Detects (model.convergence (.quotient q (.shift (0,1) (.nu X)))) (s,t,t+1)
      (regradeE2 (by simp) (finiteNuLabel model X q 1 s t 0 x)) a := by
  have hx := native_bottom_detected_cycles X q hq s t x _ ha
  obtain ⟨b,hb⟩ := shifted_finite_bottom_detects_exists X q hq 1 s t x hx
  have hb0 := (positive_finite_source_desuspend X q hq s t x ε₁ εq hε₁ hεq b hb).2
  let a0 := quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl a)
  let b0 := quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl b)
  have hdiff : FiltrationAtLeast model.syntheticTower (s+1) (a0-b0) :=
    detects_sub_filtration (model.convergence (.quotient q (.nu X))) (s,t,t) ha hb0
  have hs := (shift_filtration_iff (.quotient q (.nu X)) (0,1) (t-s,t) (s+1) (a0-b0)).mpr hdiff
  have hm := map_preserves_filtration
    (model.convergentMap (.shift (0,1) (.quotient q (.nu X)))
      (.quotient q (.shift (0,1) (.nu X))) εq.inv) ((t-s,t)+(0,1)) (s+1)
      (shiftHomotopyClass (0,1) (t-s,t) (a0-b0)) hs
  have hback := shift_quotient_unshift X (0,1) (t-s,t) q εq
    (homotopyRegrade (by simp) rfl a-homotopyRegrade (by simp) rfl b)
  rw [quotient_unshift_sub] at hback
  change FiltrationAtLeast model.syntheticTower (s+1)
    (shiftHomotopyClass (0,1) (t-s,t)
      (quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl a)-
        quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl b))≫εq.inv) at hm
  rw [hback] at hm
  have hd : FiltrationAtLeast model.syntheticTower (s+1) (a-b) := by
    have hr := (regrade_filtration_iff (show (t-s)+0=t-s by simp) rfl (s+1) _).mpr hm
    simpa only [regrade_precomp,Preadditive.comp_sub,←Category.assoc,eqToHom_trans,
      eqToHom_refl,Category.id_comp] using hr
  exact detects_of_high_difference (.quotient q (.shift (0,1) (.nu X))) (s,t,t+1) _ b a hb hd


private theorem zero_finite_source_refold
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,0)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεq : XModLambdaN.incl _ q≫εq.hom=
      (SyntheticCategory.biShift (0,0)).map (XModLambdaN.incl _ q))
    (a : BiHom (t-s) t (XModLambdaN
      ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
      (quotientUnshift X (0,0) (t-s,t) q εq (homotopyRegrade (by simp) (by simp) a))) :
    Detects (model.convergence (.quotient q (.shift (0,0) (.nu X)))) (s,t,t)
      (regradeE2 (by simp) (finiteNuLabel model X q 0 s t 0 x)) a := by
  have hx := native_bottom_detected_cycles X q hq s t x _ ha
  obtain ⟨u,hu⟩ := quotient_zero_unshift_up_to_sphere X q hq s t εq hεq a
  have hau : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
      (u.hom≫(a≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q)) := by
    simpa only [hu,Category.assoc] using ha
  have han := sphere_automorphism_finite_bottom_detects X q hq s t _ u.symm _ hau
  simp only [Iso.symm_hom,←Category.assoc,Iso.inv_hom_id,Category.id_comp] at han
  obtain ⟨bRaw,hbRaw⟩ := shifted_finite_bottom_detects_exists X q hq 0 s t x hx
  let b := homotopyRegrade rfl (show t+0=t by simp) bRaw
  have hregrade {E : SyntheticAdamsSS} {i j k : Tridegree}
      (hij : i=j) (hjk : j=k) (z : E.E₂ i) :
      regradeE2 hjk (regradeE2 hij z)=regradeE2 (hij.trans hjk) z := by
    subst j; subst k; rfl
  have hbT := detects_transport (show (s,t,t+0)=(s,t,t) by simp) _ _ hbRaw
  rw [hregrade] at hbT
  have hb' : Detects (model.convergence (.quotient q (.shift (0,0) (.nu X)))) (s,t,t)
      (regradeE2 (by simp) (finiteNuLabel model X q 0 s t 0 x)) b := hbT
  have hbn' := (zero_finite_source_desuspend X q hq s t x bRaw hbRaw).2
  change Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
      (b≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) at hbn'
  have hd := detects_sub_filtration (model.convergence (.quotient q (.nu X))) (s,t,t) han hbn'
  have hm := map_preserves_filtration
    (model.convergentMap (.quotient q (.nu X)) (.quotient q (.shift (0,0) (.nu X)))
      (XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) q)) (t-s,t) (s+1) _ hd
  have hcancel (c : BiHom (t-s) t (XModLambdaN
        ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
      (c≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q)≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) q=c := by
    rw [Category.assoc,←model.quotients.functoriality.map_comp,Iso.hom_inv_id_app,
      model.quotients.functoriality.map_id,Category.comp_id]
  rw [Preadditive.sub_comp,hcancel,hcancel] at hm
  exact detects_of_high_difference (.quotient q (.shift (0,0) (.nu X))) (s,t,t) _ b a hb' hm


private theorem normalized_finite_source_bottom_refold
    (X : ClassicalObject) (e : ℕ) (he : e≤1) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,(e:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεq : XModLambdaN.incl _ q≫εq.hom=
      (SyntheticCategory.biShift (0,(e:ℤ))).map (XModLambdaN.incl _ q))
    (a : BiHom (t-s) (t+e) (XModLambdaN
      ((SyntheticCategory.biShift (0,(e:ℤ))).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
      (quotientUnshift X (0,(e:ℤ)) (t-s,t) q εq (homotopyRegrade (by simp) rfl a))) :
    Detects (model.convergence (.quotient q (.shift (0,(e:ℤ)) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a := by
  by_cases he0 : e=0
  · subst e
    let a0 := homotopyRegrade rfl (show t+(0:ℕ)=t by simp) a
    have ha0 : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
        (quotientUnshift X (0,0) (t-s,t) q εq (homotopyRegrade (by simp) (by simp) a0)) := by
      convert ha using 1
      all_goals first | rfl | (simp only [a0,regrade_precomp,←Category.assoc,eqToHom_trans]; rfl)
    have hz := zero_finite_source_refold X q hq s t x εq hεq a0 ha0
    have hp : (s,t,t)=(s,t,t+(0:ℕ)) := by simp
    have ht := detects_transport hp _ _ hz
    have hregrade {E : SyntheticAdamsSS} {i j k : Tridegree}
        (hij : i=j) (hjk : j=k) (z : E.E₂ i) :
        regradeE2 hjk (regradeE2 hij z)=regradeE2 (hij.trans hjk) z := by
      subst j; subst k; rfl
    rw [hregrade] at ht
    convert ht using 1
    all_goals first | rfl | (simp only [a0,regrade_precomp,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp])
  · have he1 : e=1 := by omega
    subst e
    letI := model.exactness.shiftCommShift (0,1)
    letI := model.exactness.shiftExact (0,1)
    obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1
      (model.nu.functor.obj (X.obj model.auxiliary))
    exact positive_finite_source_refold X q hq s t x ε₁ εq hε₁ hεq a ha

private theorem minimal_final_extension_of_detected_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q d : ℕ) (n s t b : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ)≤n)
    (hd : (d:ℤ)=n-normalizedExponent model.classicalTower f)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (af : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
    (haf : Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f q s t x)
      (homotopyRegrade (by dsimp; omega) rfl af))
    (hMay : Detects (model.convergence (.quotient q (.nu Y))) (s+n,t+n,t+n-d)
      (finiteTargetLabel model Y q (s+n) (t+n) d y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (af≫finiteExtensionMap model X Y f q))) :
    ∃ y' : Ambient model Y (s+n,t+n),
      y'-y∈boundaries model Y b (s+n,t+n) ∧
      ∃ (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
        (bf : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)),
        Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
          (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
          (finiteSourceForExtension model X Y f q s t x)
          (homotopyRegrade (by dsimp; omega) rfl a) ∧
        Detects (model.convergence (.quotient q (.nu Y)))
          (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
          (finiteTargetForExtension model X Y f q n s t hn y')
          (homotopyRegrade (by dsimp; omega) rfl bf) ∧
        a≫finiteExtensionMap model X Y f q=bf := by
  refine ⟨y,by simpa only [sub_self] using (boundaries model Y b (s+n,t+n)).zero_mem,
    af,af≫finiteExtensionMap model X Y f q,haf,?_,rfl⟩
  have hp : (s+n,t+n,t+n-d)=
      (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f) := by
    ext <;> dsimp <;> omega
  have ht := detects_transport hp _ _ hMay
  have hdN : d=(n-normalizedExponent model.classicalTower f).toNat := by omega
  have hl : regradeE2 hp (finiteTargetLabel model Y q (s+n) (t+n) d y)=
      finiteTargetForExtension model X Y f q n s t hn y := by
    subst d
    rfl
  rw [hl] at ht
  convert ht using 1
  simp only [regrade_precomp,←Category.assoc,eqToHom_trans]


private theorem minimal_final_extension_of_native_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0<q) (d : ℕ) (n s t b : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ)≤n)
    (hd : (d:ℤ)=n-normalizedExponent model.classicalTower f)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (af : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f : ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f : ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεq : XModLambdaN.incl _ q≫εq.hom=
      (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f : ℤ))).map
        (XModLambdaN.incl _ q))
    (hafNative : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
      (quotientUnshift X (0,(normalizedExponent model.classicalTower f : ℤ)) (t-s,t) q εq
        (homotopyRegrade (by simp) rfl af)))
    (hMay : Detects (model.convergence (.quotient q (.nu Y))) (s+n,t+n,t+n-d)
      (finiteTargetLabel model Y q (s+n) (t+n) d y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (af≫finiteExtensionMap model X Y f q))) :
    ∃ y' : Ambient model Y (s+n,t+n),
      y'-y∈boundaries model Y b (s+n,t+n) ∧
      ∃ (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
        (bf : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)),
        Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
          (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
          (finiteSourceForExtension model X Y f q s t x)
          (homotopyRegrade (by dsimp; omega) rfl a) ∧
        Detects (model.convergence (.quotient q (.nu Y)))
          (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
          (finiteTargetForExtension model X Y f q n s t hn y')
          (homotopyRegrade (by dsimp; omega) rfl bf) ∧
        a≫finiteExtensionMap model X Y f q=bf := by
  have hs := normalized_finite_source_bottom_refold X (normalizedExponent model.classicalTower f)
    (normalizedExponent_le_one model.classicalTower f) q hq s t x εq hεq af hafNative
  have hp : (s,t,t+normalizedExponent model.classicalTower f)=
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f) := by simp
  have ht := detects_transport hp _ _ hs
  have hregrade {E : SyntheticAdamsSS} {i j k : Tridegree}
      (hij : i=j) (hjk : j=k) (z : E.E₂ i) :
      regradeE2 hjk (regradeE2 hij z)=regradeE2 (hij.trans hjk) z := by
    subst j; subst k; rfl
  rw [hregrade] at ht
  have haf : Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f q s t x)
      (homotopyRegrade (by dsimp; omega) rfl af) := ht
  exact minimal_final_extension_of_detected_source X Y f q d n s t b hn hd x y af haf hMay

end
end KIP126.ProofTools.Internal.Mahowald
