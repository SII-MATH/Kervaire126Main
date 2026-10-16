module
import all KIP126.Def.ProofTools.GeneralizedMahowald.CommonEdgeNativeTarget
import all KIP126.Def.ProofTools.GeneralizedMahowald.FSourceTransport
import all KIP126.Def.ProofTools.GeneralizedMahowald.CommonTotalTarget
import all KIP126.Def.ProofTools.GeneralizedMahowald.CorrectedTotalTarget
import all KIP126.Def.ProofTools.GeneralizedMahowald.TotalFTransport
import all KIP126.Def.ProofTools.GeneralizedMahowald.FSourceRegrade
import all KIP126.Def.ProofTools.GeneralizedMahowald.CorrectedCoordinates
import all KIP126.Def.ProofTools.GeneralizedMahowald.MinimalFinalAssembly

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Functor
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option Elab.async false

private theorem quotient_shift_desuspend_as_unshift
    (X : ClassicalObject) (δ p : ℤ×ℤ) (r : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (M W : ℤ) (hM : M=(p+δ).1) (hW : W=(p+δ).2)
    (a : BiHom M W (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) r)) :
    quotientUnshift X δ p r ε (homotopyRegrade hM hW a) =
      homotopyRegrade (show M-δ.1=p.1 by dsimp at hM; omega)
        (show W-δ.2=p.2 by dsimp at hW; omega)
        (quotientShiftDesuspend X δ r ε M W a) := by
  exact (quotient_shift_desuspend_as_native_unshift X δ p r M W
    (by dsimp at hM; omega) (by dsimp at hW; omega) ε a).symm

private theorem native_bottom_detects_of_same_restriction
    (X : ClassicalObject) (i r : ℕ) (hi : 0 < i) (hir : i≤r) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a c : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (ha : Detects (model.convergence (.quotient r (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X r s t 0 x)) a)
    (hc : c≫(model.quotients.tower _).rho i r hir =
      a≫(model.quotients.tower _).rho i r hir) :
    Detects (model.convergence (.quotient r (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X r s t 0 x)) c := by
  have ha1 := finite_detected_bottom_first X r (by omega) s t x a
    (by rw [zero_weight_label X r s t x]; exact ha)
  apply first_label_detects_unshifted X r (by omega) s t x c
  rw [←(model.quotients.tower _).rho_comp hi hir,←Category.assoc,hc,
    Category.assoc,(model.quotients.tower _).rho_comp hi hir,ha1]

private theorem corrected_native_bottom_detects
    (X : ClassicalObject) {C : SyntheticSpectrum} (e : ℤ)
    (e₀ : C ≅ (SyntheticCategory.biShift (1,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (i r : ℕ) (hi : 0 < i) (hir : i≤r)
    (eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift (1,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (M W s t : ℤ) (hM : M-1=t-s) (hW : W-e=t)
    (x : Ambient model X (s,t)) (c : BiHom M W (XModLambdaN C r))
    (c' : BiHom (M-1) (W+i) ((SyntheticCategory.biShift (0,(i:ℤ)+e)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)))
    (hρ : c'≫(SyntheticCategory.biShift (0,(i:ℤ)+e)).map
        ((model.quotients.tower _).rho i r hir) =
      (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
        ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
          (by ext <;> dsimp; all_goals omega)).hom.app S_0_0 ≫ c ≫
          (commonCofiberTargetIso e e₀ i r eQ).hom) ≫
        (SyntheticCategory.biShift (0,(i:ℤ)+e)).map ((model.quotients.tower _).rho i r hir))
    (hc : Detects (model.convergence (.quotient r (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X r s t 0 x))
      (homotopyRegrade hM hW (quotientShiftDesuspend X (1,e) r eQ M W
        (c≫XModLambdaN.map e₀.hom r)))) :
    Detects (model.convergence (.quotient r (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X r s t 0 x))
      (quotientUnshift X (1,e) (t-s,t) r eQ
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (commonCorrectedGeometry i M W (commonCofiberTargetIso e e₀ i r eQ) c'≫
            XModLambdaN.map e₀.hom r))) := by
  let cnew := commonCorrectedGeometry i M W (commonCofiberTargetIso e e₀ i r eQ) c'
  have hsame := common_correction_preserves_native_rho X e e₀ i r hir eQ M W c c' hρ
  have hn := native_bottom_detects_of_same_restriction X i r hi hir s t x
    (homotopyRegrade hM hW (quotientShiftDesuspend X (1,e) r eQ M W
      (c≫XModLambdaN.map e₀.hom r)))
    (homotopyRegrade hM hW (quotientShiftDesuspend X (1,e) r eQ M W
      (cnew≫XModLambdaN.map e₀.hom r))) hc (by
    dsimp only [cnew]
    simpa only [regrade_comp] using congrArg (homotopyRegrade hM hW) hsame)
  rw [quotient_shift_desuspend_as_unshift]
  exact hn

private theorem normalized_f_total_raw_boundary_detects_transport
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (κ : SyntheticCategory.biShift (Syn:=SyntheticSpectrum)
      (0,(normalizedExponent model.classicalTower T.g : ℤ))⋙shiftFunctor SyntheticSpectrum (1:ℤ) ≅
        SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ)))
    (q k : ℕ) (hkq : k<q) (s t : ℤ) (y : Ambient model T.Y (s,t))
    (εA : XModLambdaN ((SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).obj
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary)) q ≅
      (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).obj (XModLambdaN
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary) q))
    (εB : XModLambdaN ((SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).obj
        (model.nu.functor.obj (T.Y.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) q))
    (hεA : XModLambdaN.incl _ q≫εA.hom=
      (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).map (XModLambdaN.incl _ q))
    (hεB : XModLambdaN.incl _ q≫εB.hom=
      (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).map (XModLambdaN.incl _ q))
    (a : BiHom ((t-s,t-k)+(1,(normalizedExponent model.classicalTower T.g : ℤ))).1 ((t-s,t-k)+(1,(normalizedExponent model.classicalTower T.g : ℤ))).2 (XModLambdaN
      (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map) q))
    (ha : Detects (model.convergence (.quotient q (.nu T.Y))) (s,t,t-k)
      (finiteTargetLabel model T.Y q s t k y)
      (quotientUnshift T.Y (1,(normalizedExponent model.classicalTower T.g : ℤ)) (t-s,t-k) q εB
        (a≫XModLambdaN.map
          (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) q ≫
          XModLambdaN.map
            (κ.hom.app _) q))) :
    Detects (model.convergence (.quotient q (.nu T.Y))) (s,t,t-k)
      (finiteTargetLabel model T.Y q s t k y)
      (quotientClassUnshift _ (1,(normalizedExponent model.classicalTower T.g : ℤ)) (t-s,t-k) q εA
        (a≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) q) ≫
          finiteExtensionMap model T.X T.Y T.f q) := by
  rw [normalized_f_total_raw_boundary_equation T he hT q (by omega) (t-s,t-k) εA εB hεA hεB]
  have h := quotient_unshift_two_natural_transports_detects T.Y
    (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.g : ℤ))⋙
      shiftFunctor SyntheticSpectrum (1:ℤ))
    (1,(normalizedExponent model.classicalTower T.g : ℤ))
    (exactTotalSuspensionTransport (normalizedExponent model.classicalTower T.g))
    κ
    q k hkq s t y εB hεB
    (a≫XModLambdaN.map
      (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) q)
    (by simpa only [Category.assoc] using ha)
  simpa only [Category.assoc] using h



private theorem quotient_class_unshift_regrade_source
    (A : SyntheticSpectrum) (δ p p' : ℤ×ℤ) (hp : p=p') (r : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj A) r ≅
      (SyntheticCategory.biShift δ).obj (XModLambdaN A r))
    (M W : ℤ) (a : BiHom M W (XModLambdaN ((SyntheticCategory.biShift δ).obj A) r))
    (hM : M=(p+δ).1) (hW : W=(p+δ).2)
    (hM' : M=(p'+δ).1) (hW' : W=(p'+δ).2) :
    homotopyRegrade (congrArg Prod.fst hp) (congrArg Prod.snd hp)
      (quotientClassUnshift A δ p r ε (homotopyRegrade hM hW a)) =
      quotientClassUnshift A δ p' r ε (homotopyRegrade hM' hW' a) := by
  subst p'
  rfl

private theorem homotopy_regrade_self {m w : ℤ} {A : SyntheticSpectrum}
    (hm : m=m) (hw : w=w) (a : BiHom m w A) : homotopyRegrade hm hw a=a := rfl

private theorem finite_e2_regrade_roundtrip {E : SyntheticAdamsSS} {p q : Tridegree}
    (h : p=q) (x : E.E₂ p) : regradeE2 h.symm (regradeE2 h x)=x := by
  subst q
  rfl

private theorem minimal_corrected_total_extension
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t n b : ℤ)
    (hn : n=(i:ℤ)+normalizedExponent model.classicalTower T.f)
    (M W : ℤ) (hM : M=(t-s)+1)
    (hW : W=t+(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
    (x : Ambient model T.X (s,t)) (y : Ambient model T.Y (s+n,t+n)) :
    let ef : ℤ := normalizedExponent model.classicalTower T.f
    let eg : ℤ := normalizedExponent model.classicalTower T.g
    let e : ℤ := ef+eg
    let r := i+q
    let Xν := model.nu.functor.obj (T.X.obj model.auxiliary)
    let Yν := model.nu.functor.obj (T.Y.obj model.auxiliary)
    let Af := (extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary
    let Ag := (extensionSourceObject model T.Y T.Z T.g).obj model.nu model.auxiliary
    let G := (model.normalizedMap T.Y T.Z T.g).map
    let Cg := HasFunctorialCofiber.cofib G
    let eCg := normalized_g_cofiber_iso T he hT
    let C₀ := (SyntheticCategory.biShift (0,(i:ℤ)+e)).obj (XModLambdaN Xν r)
    ∀ (eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj Xν) r ≅
        (SyntheticCategory.biShift (1,e)).obj (XModLambdaN Xν r))
      (εe : XModLambdaN Af r ≅ (SyntheticCategory.biShift (0,ef)).obj (XModLambdaN Xν r))
      (εA : XModLambdaN ((SyntheticCategory.biShift (1,eg)).obj Af) r ≅
        (SyntheticCategory.biShift (1,eg)).obj (XModLambdaN Af r))
      (eAg : XModLambdaN Ag r ≅ (SyntheticCategory.biShift (0,eg)).obj (XModLambdaN Yν r))
      (esusp : XModLambdaN (Ag⟦(1:ℤ)⟧) r ≅ (XModLambdaN Ag r)⟦(1:ℤ)⟧)
      (_heQ : XModLambdaN.incl _ r≫eQ.hom=(SyntheticCategory.biShift (1,e)).map (XModLambdaN.incl Xν r))
      (_hεe : XModLambdaN.incl _ r≫εe.hom=(SyntheticCategory.biShift (0,ef)).map (XModLambdaN.incl Xν r))
      (_hεA : XModLambdaN.incl _ r≫εA.hom=(SyntheticCategory.biShift (1,eg)).map (XModLambdaN.incl Af r))
      (_heAg : XModLambdaN.incl _ r≫eAg.hom=(SyntheticCategory.biShift (0,eg)).map (XModLambdaN.incl Yν r))
      (_hesusp : XModLambdaN.incl _ r≫esusp.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl Ag r))
      (cGeometry : BiHom M W (XModLambdaN Cg r)),
      let eC := commonCofiberTargetIso e eCg i r eQ
      let eD := commonEdgeTargetFlatIso Yν eg i q esusp eAg
      let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
      let h₀ := ff.preimage (eC.inv≫XModLambdaN.map (HasFunctorialCofiber.cofibδ G) r≫eD.hom)
      let Jq := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN Ag (r-i))).hom≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((model.quotients.tower Ag).triangle hi (show i < r by omega)).lambdaMap≫esusp.inv≫eD.hom)
      ∀ (c' : BiHom (M-1) (W+i) C₀)
        (_hρ : c'≫(SyntheticCategory.biShift (0,(i:ℤ)+e)).map ((model.quotients.tower Xν).rho i r (by omega)) =
          ff.preimage ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
            (by ext <;> dsimp; all_goals omega)).hom.app S_0_0≫cGeometry≫eC.hom)≫
            (SyntheticCategory.biShift (0,(i:ℤ)+e)).map ((model.quotients.tower Xν).rho i r (by omega)))
        (_hc : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel model T.X r s t 0 x))
          (homotopyRegrade (by simp only [Prod.fst,Prod.snd] <;> omega)
            (by simp only [Prod.fst,Prod.snd]; dsimp [e,ef,eg] at * <;> omega)
            (quotientShiftDesuspend T.X (1,e) r eQ M W (cGeometry≫XModLambdaN.map eCg.hom r))))
        (ag : BiHom ((t+n)-(s+n)) (t+n+eg) (XModLambdaN Ag (r-i)))
        (_hag : Detects (model.convergence (.quotient (r-i) (.shift (0,eg) (.nu T.Y))))
          (s+n,t+n,t+n+eg) (regradeE2 (by simp) (finiteNuLabel model T.Y (r-i) eg (s+n) (t+n) 0 y)) ag)
        (_hu : Detects (model.convergence (.shift (0,(i:ℤ)+eg) (.quotient r (.nu T.Y))))
          (s+n,t+n,t+n+eg)
          (familyPageMap model.family Jq 2 (s+n,t+n,t+n+eg)
            (regradeE2 (by simp) (finiteNuLabel model T.Y (r-i) eg (s+n) (t+n) 0 y)))
          (homotopyRegrade (by simp only [Prod.fst,Prod.snd] <;> omega)
            (by simp only [Prod.fst,Prod.snd]; dsimp [e,ef,eg] at * <;> omega) (c'≫h₀))),
      ∃ y' : Ambient model T.Y (s+n,t+n), y'-y∈boundaries model T.Y b (s+n,t+n) ∧
        ∃ (af : BiHom (t-s) (t+ef) (XModLambdaN Af r))
          (bf : BiHom (t-s) (t+ef) (XModLambdaN Yν r)),
          Detects (model.convergence (.quotient r (extensionSourceObject model T.X T.Y T.f)))
            (s,(t-s)+s,t+ef) (finiteSourceForExtension model T.X T.Y T.f r s t x)
            (homotopyRegrade (by simp only [Prod.fst,Prod.snd] <;> omega) rfl af) ∧
          Detects (model.convergence (.quotient r (.nu T.Y)))
            (s+n,(t-s)+(s+n),t+ef)
            (finiteTargetForExtension model T.X T.Y T.f r n s t (by omega) y')
            (homotopyRegrade (by simp only [Prod.fst,Prod.snd] <;> omega) rfl bf) ∧
          af≫finiteExtensionMap model T.X T.Y T.f r=bf := by
  dsimp only
  intro eQ εe εA eAg esusp heQ hεe hεA heAg hesusp cGeometry c' hρ hc ag hag hu
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let e : ℤ := ef+eg
  let r := i+q
  let Xν := model.nu.functor.obj (T.X.obj model.auxiliary)
  let Yν := model.nu.functor.obj (T.Y.obj model.auxiliary)
  let Af := (extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary
  let Ag := (extensionSourceObject model T.Y T.Z T.g).obj model.nu model.auxiliary
  let G := (model.normalizedMap T.Y T.Z T.g).map
  let eCg := normalized_g_cofiber_iso T he hT
  let eC := commonCofiberTargetIso e eCg i r eQ
  let eD := commonEdgeTargetFlatIso Yν eg i q esusp eAg
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  let h₀ := ff.preimage (eC.inv≫XModLambdaN.map (HasFunctorialCofiber.cofibδ G) r≫eD.hom)
  let cnew := commonCorrectedGeometry i M W eC c'
  let εB := commonTotalQuotientIso Yν eg i q esusp eAg
  have hεB := common_total_quotient_inclusion Yν eg i q esusp eAg hesusp heAg
  have heg : eg=0 ∨ eg=1 := by
    have hh := normalizedExponent_le_one model.classicalTower T.g
    change (normalizedExponent model.classicalTower T.g : ℤ)=0 ∨
      (normalizedExponent model.classicalTower T.g : ℤ)=1
    omega
  have hrawCommon := corrected_actual_common_edge_native_detects T.Y eg heg i q hi hq
    (s+n) (t+n) y esusp eAg heAg ag hag
    (homotopyRegrade (by omega) (by dsimp [e,ef,eg,Prod.mk_add_mk,Prod.fst,Prod.snd] at * <;> omega) (c'≫h₀)) hu
  have hrawNative := common_corrected_total_native_detection T.Y eg i q hq
    (s+n) (t+n) M W (by omega) (by dsimp [e,ef,eg,Prod.mk_add_mk,Prod.fst,Prod.snd] at * <;> omega) y
    esusp eAg _ _ eC (XModLambdaN.map (HasFunctorialCofiber.cofibδ G) r) c' (by
      simpa only [common_regrade_trans,h₀,ff,eD,SyntheticObject.obj] using hrawCommon)
  let p : ℤ×ℤ := (t-s,t)
  let py : ℤ×ℤ := ((t+n)-(s+n),t+n-i)
  let aY := homotopyRegrade
    (show M=(py+(1,eg)).1 by dsimp [py,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega)
    (show W=(py+(1,eg)).2 by dsimp [py,e,ef,eg,Prod.mk_add_mk,Prod.fst,Prod.snd] at * <;> omega) cnew
  have hMayY := normalized_f_total_raw_boundary_detects_transport T he hT
    (commonTotalSuspensionTransport eg i) r i (by omega) (s+n) (t+n) y
    εA εB hεA hεB aY (by
      simpa only [aY,cnew,←regrade_comp] using hrawNative)
  let p0 : ℤ×ℤ := (t-s,t-(0:ℕ))
  have hp0 : p=p0 := by ext <;> dsimp [p,p0] <;> omega
  have hgrade : (s,t,t-(0:ℕ))=(s,t,t) := by simp
  let cSource := homotopyRegrade
    (show M=(p0+(1,e)).1 by dsimp [p,p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega)
    (show W=(p0+(1,e)).2 by dsimp [p0] <;> omega) cnew
  have hsourceNative := corrected_native_bottom_detects T.X e eCg i r hi (by omega) eQ
    M W s t (by omega) (by omega) x cGeometry c' hρ hc
  have hsourceBack := detects_transport hgrade.symm _ _ hsourceNative
  rw [finite_e2_regrade_roundtrip hgrade] at hsourceBack
  have hnat0 : homotopyRegrade (congrArg Prod.fst hp0) (congrArg Prod.snd hp0)
      (quotientUnshift T.X (1,e) p r eQ
        (homotopyRegrade (show M=(p+(1,e)).1 by dsimp [p,p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (show W=(p+(1,e)).2 by dsimp [p,p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega)
          (cnew≫XModLambdaN.map eCg.hom r))) =
      quotientUnshift T.X (1,e) p0 r eQ (cSource≫XModLambdaN.map eCg.hom r) := by
    have hh := quotient_class_unshift_regrade_source Xν (1,e) p p0 hp0 r eQ M W
      (cnew≫XModLambdaN.map eCg.hom r)
      (by dsimp [p] <;> omega) (by dsimp [p,e,ef,eg] at * <;> omega)
      (by dsimp [p,p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (by dsimp [p0] <;> omega)
    simpa only [quotientClassUnshift,quotientUnshift,cSource,regrade_comp] using hh
  have hc0 : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-(0:ℕ))
      (finiteTargetLabel model T.X r s t 0 x)
      (quotientUnshift T.X (1,e) p0 r eQ (cSource≫XModLambdaN.map eCg.hom r)) := by
    rw [←hnat0]
    exact hsourceBack
  have hsource := normalized_f_total_actual_source_unshift_detects T he hT r 0 (by omega)
    s t x eQ εe εA heQ hεe hεA cSource hc0
  let a := homotopyRegrade
    (show (p0+(1,e)).1=((p0+(0,ef))+(1,eg)).1 by dsimp [p0,e] <;> omega)
    (show (p0+(1,e)).2=((p0+(0,ef))+(1,eg)).2 by dsimp [p0,e] <;> omega) cSource
  let af := quotientClassUnshift Af (1,eg) (p0+(0,ef)) r εA
    (a≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) r)
  have hsource0 : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-(0:ℕ))
      (finiteTargetLabel model T.X r s t 0 x)
      (quotientUnshift T.X (0,ef) p0 r εe af) := hsource
  have hsourceForward := detects_transport hgrade _ _ hsource0
  have hnat1 := quotient_class_unshift_regrade_source Xν (0,ef) p0 p hp0.symm r εe
    (p0+(0,ef)).1 (p0+(0,ef)).2 af rfl rfl
    (by dsimp [p,p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (by dsimp [p0,p] <;> omega)
  have hafNative : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model T.X r s t 0 x))
      (quotientUnshift T.X (0,ef) (t-s,t) r εe
        (homotopyRegrade (by dsimp [p,p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (by dsimp [p,p0] <;> omega) af)) := by
    have hh : homotopyRegrade (congrArg Prod.fst hp0.symm) (congrArg Prod.snd hp0.symm)
        (quotientUnshift T.X (0,ef) p0 r εe af) =
        quotientUnshift T.X (0,ef) p r εe
          (homotopyRegrade (by dsimp [p,p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (by dsimp [p0,p] <;> omega) af) := by
      simpa only [quotientClassUnshift,quotientUnshift,homotopy_regrade_self,Xν] using hnat1
    exact (congrArg (fun z => Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t)
      (regradeE2 hgrade (finiteTargetLabel model T.X r s t 0 x)) z) hh).mp hsourceForward
  have hMay : Detects (model.convergence (.quotient r (.nu T.Y))) (s+n,t+n,t+n-i)
      (finiteTargetLabel model T.Y r (s+n) (t+n) i y)
      (homotopyRegrade (by dsimp [p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (by dsimp [p0,ef,Prod.mk_add_mk,Prod.fst,Prod.snd] at * <;> omega)
        (af≫finiteExtensionMap model T.X T.Y T.f r)) := by
    have hpy : py=p0+(0,ef) := by ext <;> dsimp [py,p0,ef] at * <;> omega
    have hα : homotopyRegrade (congrArg Prod.fst hpy.symm) (congrArg Prod.snd hpy.symm) af =
        quotientClassUnshift Af (1,eg) py r εA
          (aY≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) r) := by
      have hh := quotient_class_unshift_regrade_source Af (1,eg) (p0+(0,ef)) py hpy.symm r εA
        M W (cnew≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) r)
        (by dsimp [p0,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (by dsimp [p0,e,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega)
        (by dsimp [py,Prod.mk_add_mk,Prod.fst,Prod.snd] <;> omega) (by dsimp [py,e,ef,eg,Prod.mk_add_mk,Prod.fst,Prod.snd] at * <;> omega)
      simpa only [af,a,cSource,aY,regrade_comp,common_regrade_trans] using hh
    rw [regrade_comp,hα]
    exact hMayY
  apply minimal_final_extension_of_native_source T.X T.Y T.f r (by omega) i n s t b
    (by omega) (by omega) x y (homotopyRegrade (by dsimp [p0] <;> omega) (by dsimp [p0] <;> omega) af) εe hεe
  · simpa only [common_regrade_trans] using hafNative
  · simpa only [←regrade_comp,common_regrade_trans] using hMay

end
end KIP126.ProofTools.Internal.Mahowald
