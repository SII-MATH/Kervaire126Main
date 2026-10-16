module
import all KIP126.ProofTools.GeneralizedMahowald.HSourceSelection
import all KIP126.ProofTools.GeneralizedMahowald.HMapCoherence
/-! Identify the actual h-extension target with the prescribed unshifted
cofiber representative. The finite quotient comparison uses no-return on
sphere representatives; both inverse shifts are then equal strictly. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

private theorem finite_source_unshifts_uniform
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (s t : ℤ)
    (a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
    (hu : FiniteSourceUnshifts X Y f q s t a₀ ah) :
    ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
      XModLambdaN.incl _ q ≫ ε.hom =
        (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).map (XModLambdaN.incl _ q) ∧
      homotopyRegrade (by simp) rfl
        (shiftHomotopyClass (0,(normalizedExponent model.classicalTower f:ℤ)) (t-s,t) a₀) ≫ ε.inv = ah := by
  change BiHom (t-s) (t+normalizedExponent model.classicalTower f)
    (XModLambdaN ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q) at ah
  unfold FiniteSourceUnshifts at hu
  have transport (e e' : ℤ) (hee' : e=e')
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q))
      (h : ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,e')).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
          (SyntheticCategory.biShift (0,e')).obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
        XModLambdaN.incl _ q ≫ ε.hom = (SyntheticCategory.biShift (0,e')).map (XModLambdaN.incl _ q) ∧
        homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,e') (t-s,t) a₀) ≫ ε.inv =
          ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
            (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
              (model.nu.functor.obj (X.obj model.auxiliary))) q)) hee').mp a)) :
      ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
          (SyntheticCategory.biShift (0,e)).obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
        XModLambdaN.incl _ q ≫ ε.hom = (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ q) ∧
        homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,e) (t-s,t) a₀) ≫ ε.inv = a := by
    subst e'
    exact h
  rcases hu with ⟨he,hu⟩ | ⟨he,ε,hε,hu⟩
  · apply transport _ 0 (by omega) ah

    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let ε : XModLambdaN ((SyntheticCategory.biShift (0,0)).obj A) q ≅
        (SyntheticCategory.biShift (0,0)).obj (XModLambdaN A q) :=
      (model.quotients.functoriality.functor q).mapIso (SyntheticCategory.biShift_zero.app A) ≪≫
        (SyntheticCategory.biShift_zero.app (XModLambdaN A q)).symm
    refine ⟨ε,?_,?_⟩
    · change XModLambdaN.incl _ q ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q ≫
          SyntheticCategory.biShift_zero.inv.app (XModLambdaN A q) = _
      rw [←Category.assoc,←XModLambdaN.incl_naturality]
      have hn := SyntheticCategory.biShift_zero.hom.naturality (XModLambdaN.incl A q)
      dsimp only [Functor.id_obj,Functor.id_map] at hn
      erw [←hn]
      simp only [Category.assoc,Iso.hom_inv_id_app,Category.comp_id]
      rfl
    · have hz : homotopyRegrade (by simp) (by simp) (shiftHomotopyClass (0,0) (t-s,t) a₀) ≫
          SyntheticCategory.biShift_zero.hom.app (XModLambdaN A q) = a₀ := by
        rw [regrade_precomp]
        simp only [shiftHomotopyClass,Category.assoc]
        rw [←Category.assoc,←Category.assoc]
        have hu := model.quotients.coherence.right_unit (t-s,t) (S_0_0 : SyntheticSpectrum)
        simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,NatTrans.comp_app] at hu
        have hn := SyntheticCategory.biShift_zero.hom.naturality a₀
        dsimp only [Functor.id_map,Functor.id_obj] at hn
        rw [Category.assoc,Category.assoc,hn,←Category.assoc]
        erw [←hu]
        simp only [Category.assoc]
        erw [Iso.inv_hom_id_app_assoc]
        simp only [eqToHom_app,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]
      have hh := congrArg (fun z => z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q) hz
      change homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,0) (t-s,t) a₀) ≫
        (SyntheticCategory.biShift_zero.hom.app (XModLambdaN A q) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q) = _
      have hh' := congrArg (fun z => homotopyRegrade rfl (show t=t+0 by simp) z) hh
      have hcomp {m m' m'' w w' w'' : ℤ} {B : SyntheticSpectrum}
          (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
          (b : BiHom m w B) :
          homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
            homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
        subst m'; subst m''; subst w'; subst w''; rfl
      simp only [regrade_comp,hcomp] at hh'
      simpa only [Category.assoc] using hh'.trans hu
  · exact transport _ 1 (by omega) ah ⟨ε,hε,hu⟩


private theorem quotient_h_target_maps (X Z : ClassicalObject) (k q : ℕ)
    (hk : k≤1) (hq : 0<q) (δ : ℤ×ℤ) (hδ : δ+(0,(k:ℤ))=(1,1))
    (H : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (Z.obj model.auxiliary)) ⟶
      model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary))
    (R : model.nu.functor.obj (Z.obj model.auxiliary) ⟶
      (SyntheticCategory.biShift δ).obj (model.nu.functor.obj (X.obj model.auxiliary)))
    (hR : (SyntheticCategory.biShift (0,(k:ℤ))).map R ≫
      (biShiftAddIso δ (0,(k:ℤ)) (1,1) hδ).hom.app _ =
        H≫(model.nu.suspensionIso (X.obj model.auxiliary)).hom)
    (εh : XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (Z.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) q))
    (εδ : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εσ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεh : XModLambdaN.incl _ q≫εh.hom =
      (SyntheticCategory.biShift (0,(k:ℤ))).map (XModLambdaN.incl _ q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (hεσ : XModLambdaN.incl _ q≫εσ.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
      (model.nu.functor.obj (Z.obj model.auxiliary))) q)) :
    a≫XModLambdaN.map H q≫XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q≫εσ.hom =
      a≫εh.hom≫(SyntheticCategory.biShift (0,(k:ℤ))).map
        (XModLambdaN.map R q≫εδ.hom)≫
        (biShiftAddIso δ (0,(k:ℤ)) (1,1) hδ).hom.app _ := by
  let E := (model.quotients.functoriality.functor q).mapIso
    (model.nu.suspensionIso (X.obj model.auxiliary)) ≪≫ εσ
  let f := XModLambdaN.map H q ≫ E.hom
  let g := εh.hom≫(SyntheticCategory.biShift (0,(k:ℤ))).map
    (XModLambdaN.map R q≫εδ.hom)≫
    (biShiftAddIso δ (0,(k:ℤ)) (1,1) hδ).hom.app
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)
  have hf : XModLambdaN.incl _ q≫f =
      H≫(model.nu.suspensionIso (X.obj model.auxiliary)).hom≫
        (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q) := by
    change XModLambdaN.incl _ q≫XModLambdaN.map H q≫
      XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q≫εσ.hom = _
    simp only [←Category.assoc,←XModLambdaN.incl_naturality]
    simp only [Category.assoc]
    erw [←Category.assoc (XModLambdaN.incl _ q),←XModLambdaN.incl_naturality]
    simp only [Category.assoc,hεσ]
  have hg : XModLambdaN.incl _ q≫g =
      H≫(model.nu.suspensionIso (X.obj model.auxiliary)).hom≫
        (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q) := by
    dsimp only [g]
    rw [←Category.assoc (XModLambdaN.incl _ q),hεh]
    rw [←Category.assoc,←Functor.map_comp]
    rw [←Category.assoc (XModLambdaN.incl _ q),←XModLambdaN.incl_naturality,Category.assoc,hεδ]
    rw [Functor.map_comp,Category.assoc]
    erw [(biShiftAddIso δ (0,(k:ℤ)) (1,1) hδ).hom.naturality]
    rw [←Category.assoc,hR,Category.assoc]
  have hfg : XModLambdaN.incl _ q≫(f≫E.inv) =
      XModLambdaN.incl _ q≫(g≫E.inv) := by
    simpa only [Category.assoc] using congrArg (fun z => z≫E.inv) (hf.trans hg.symm)
  have hh := normalized_quotient_maps_equal_on_spheres Z (.shift 1 X) k hk q hq
    (f≫E.inv) (g≫E.inv) hfg m w a
  have hh' := congrArg (fun z => z≫E.hom) hh
  have hh'' : a≫f=a≫g := by
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hh'
  change a≫(XModLambdaN.map H q≫
    (XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q≫εσ.hom)) = _ at hh''
  simpa only [Category.assoc] using hh''

private theorem quotient_h_target_representative (X Z : ClassicalObject) (k q : ℕ)
    (hk : k≤1) (hq : 0<q) (δ : ℤ×ℤ) (hδ : δ+(0,(k:ℤ))=(1,1))
    (H : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (Z.obj model.auxiliary)) ⟶
      model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary))
    (R : model.nu.functor.obj (Z.obj model.auxiliary) ⟶
      (SyntheticCategory.biShift δ).obj (model.nu.functor.obj (X.obj model.auxiliary)))
    (hR : (SyntheticCategory.biShift (0,(k:ℤ))).map R ≫
      (biShiftAddIso δ (0,(k:ℤ)) (1,1) hδ).hom.app _ =
        H≫(model.nu.suspensionIso (X.obj model.auxiliary)).hom)
    (εh : XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (Z.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) q))
    (εδ : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εσ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεh : XModLambdaN.incl _ q≫εh.hom =
      (SyntheticCategory.biShift (0,(k:ℤ))).map (XModLambdaN.incl _ q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (hεσ : XModLambdaN.incl _ q≫εσ.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (m w : ℤ)
    (a₀ : BiHom m w (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) q))
    (ah : BiHom ((m,w)+(0,(k:ℤ))).1 ((m,w)+(0,(k:ℤ))).2
      (XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (Z.obj model.auxiliary))) q))
    (hback : shiftHomotopyClass (0,(k:ℤ)) (m,w) a₀≫εh.inv = ah) :
    quotientUnshift X (1,1) (m-δ.1,w-δ.2) q εσ
      (homotopyRegrade
        (by have h := congrArg Prod.fst hδ; dsimp at h ⊢; omega)
        (by have h := congrArg Prod.snd hδ; dsimp at h ⊢; omega)
        (ah≫XModLambdaN.map H q≫
          XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q)) =
      quotientShiftDesuspend X δ q εδ m w (a₀≫XModLambdaN.map R q) := by
  let p : ℤ×ℤ := (m-δ.1,w-δ.2)
  let b : ℤ×ℤ := (m,w)
  let h : ℤ×ℤ := (0,(k:ℤ))
  have hpb : p+δ=b := by ext <;> simp [p,b]
  have htotal : p+(1,1)=b+h := by
    rw [←hδ,←add_assoc,hpb]
  let aNu := quotientShiftDesuspend X δ q εδ m w (a₀≫XModLambdaN.map R q)
  have hNu : (biShiftAddIso p δ b hpb).inv.app S_0_0≫
      (SyntheticCategory.biShift δ).map aNu = a₀≫XModLambdaN.map R q≫εδ.hom := by
    simp only [aNu,quotientShiftDesuspend,Functor.FullyFaithful.map_preimage]
    simp only [Category.assoc]
    change (biShiftAddIso p δ b hpb).inv.app S_0_0≫
      (biShiftAddIso p δ b hpb).hom.app S_0_0≫_ = _
    simp
  have hass := shift_hom_associativity model.quotients.coherence
    p δ h b (1,1) (b+h) hpb hδ rfl htotal aNu
  rw [hNu] at hass
  have hass' := congrArg (fun z => z≫(biShiftAddIso δ h (1,1) hδ).hom.app
    (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) hass
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id] at hass'
  have hmaps := quotient_h_target_maps X Z k q hk hq δ hδ H R hR εh εδ εσ
    hεh hεδ hεσ ((m,w)+h).1 ((m,w)+h).2 ah
  have hsource : ah≫εh.hom = shiftHomotopyClass h b a₀ := by
    rw [←hback]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rfl
  rw [←Category.assoc ah εh.hom,hsource] at hmaps
  have htarg : (biShiftAddIso p (1,1) (b+h) htotal).inv.app S_0_0≫
      (SyntheticCategory.biShift (1,1)).map aNu =
      (ah≫XModLambdaN.map H q≫
        XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q)≫εσ.hom := by
    calc
      _ = (SyntheticCategory.biShift_comp b h).inv.app S_0_0≫
          (SyntheticCategory.biShift h).map (a₀≫XModLambdaN.map R q≫εδ.hom)≫
          (biShiftAddIso δ h (1,1) hδ).hom.app _ := by
            simpa only [biShiftAddIso,eqToIso_refl,Iso.trans_refl] using hass'
      _ = _ := by
        simpa only [shiftHomotopyClass,Functor.map_comp,Category.assoc] using hmaps.symm
  have hregrade : homotopyRegrade (congrArg Prod.fst htotal) (congrArg Prod.snd htotal)
      (shiftHomotopyClass (1,1) p aNu) =
      (biShiftAddIso p (1,1) (b+h) htotal).inv.app S_0_0≫
        (SyntheticCategory.biShift (1,1)).map aNu := by
    have transport (p δ v : ℤ×ℤ) (hp : p+δ=v) {A : SyntheticSpectrum}
        (a : BiHom p.1 p.2 A) :
        homotopyRegrade (congrArg Prod.fst hp) (congrArg Prod.snd hp)
          (shiftHomotopyClass δ p a) =
          (biShiftAddIso p δ v hp).inv.app S_0_0≫(SyntheticCategory.biShift δ).map a := by
      subst v
      simp [homotopyRegrade,shiftHomotopyClass,biShiftAddIso]
    exact transport p (1,1) (b+h) htotal aNu
  rw [←hregrade] at htarg
  have htarg' := congrArg
    (homotopyRegrade (congrArg Prod.fst htotal).symm (congrArg Prod.snd htotal).symm) htarg
  rw [homotopy_regrade_inverse,regrade_comp] at htarg'
  have hback' := congrArg (fun z => z≫εσ.inv) htarg'
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id] at hback'
  change quotientUnshift X (1,1) p q εσ _ = aNu
  rw [←hback',quotient_unshift_shift]

private theorem normalized_h_target_representative (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (T.Z.obj model.auxiliary)) q))
    (ah : BiHom (t-s) (t+normalizedExponent model.classicalTower T.h)
      ((SyntheticObject.quotient q (extensionSourceObject model T.Z (.shift 1 T.X) T.h)).obj
        model.nu model.auxiliary))
    (hu : FiniteSourceUnshifts T.Z (.shift 1 T.X) T.h q s t a₀ ah)
    (εδ : XModLambdaN ((SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).map
          (XModLambdaN.incl _ q))
    (εσ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (hεσ : XModLambdaN.incl _ q≫εσ.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q)) :
    quotientUnshift T.X (1,1)
      (t-s-1,t-((normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g))
      q εσ (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (ah≫finiteExtensionMap model T.Z (.shift 1 T.X) T.h q≫
          XModLambdaN.map (model.nu.suspensionIso (T.X.obj model.auxiliary)).hom q)) =
      quotientShiftDesuspend T.X
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
        q εδ (t-s) t
        (a₀≫XModLambdaN.map (HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map≫
          (normalized_g_cofiber_iso T he hT).hom) q) := by
  obtain ⟨εh,hεh,hback⟩ := finite_source_unshifts_uniform T.Z (.shift 1 T.X) T.h q s t a₀ ah hu
  let k := normalizedExponent model.classicalTower T.h
  let δ : ℤ×ℤ := (1,(normalizedExponent model.classicalTower T.f : ℤ)+
    normalizedExponent model.classicalTower T.g)
  let ah' := homotopyRegrade (show t-s=((t-s,t)+(0,(k:ℤ))).1 by simp) rfl ah
  have hback' : shiftHomotopyClass (0,(k:ℤ)) (t-s,t) a₀≫εh.inv=ah' := by
    have hb := congrArg
      (homotopyRegrade (show t-s=((t-s,t)+(0,(k:ℤ))).1 by simp) rfl) hback
    rw [regrade_comp,homotopy_regrade_inverse] at hb
    exact hb
  have hδ : δ+(0,(k:ℤ))=(1,1) := by ext <;> simp only [δ,k,Prod.fst_add,Prod.snd_add] <;> omega
  have hh := quotient_h_target_representative T.X T.Z k q
    (normalizedExponent_le_one model.classicalTower T.h) hq δ hδ
    (model.normalizedMap T.Z (.shift 1 T.X) T.h).map
    (HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map≫
      (normalized_g_cofiber_iso T he hT).hom)
    (normalized_g_cofiber_inclusion_shifted T he hT)
    εh εδ εσ hεh hεδ hεσ (t-s) t a₀ ah' hback'
  have transport {m m' m'' w w' w'' : ℤ} {A : SyntheticSpectrum}
      (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'') (a : BiHom m w A) :
      homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
        homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
    subst m'; subst m''; subst w'; subst w''; rfl
  dsimp only [ah'] at hh
  rw [←regrade_comp,transport] at hh
  exact hh

end
end KIP126.ProofTools.Internal.Mahowald
