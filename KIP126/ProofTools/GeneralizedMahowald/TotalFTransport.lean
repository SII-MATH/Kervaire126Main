module
import all KIP126.ProofTools.GeneralizedMahowald.FSourceTransport

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

private def cancelBiShiftNatIso (β : ℤ×ℤ) (F G : SyntheticSpectrum ⥤ SyntheticSpectrum)
    (η : F ⋙ SyntheticCategory.biShift β ≅ G ⋙ SyntheticCategory.biShift β) : F ≅ G :=
  NatIso.ofComponents (fun A =>
    (SyntheticCategory.biShift_fullyFaithful β).preimageIso (η.app A)) (by
      intro A B f
      apply (SyntheticCategory.biShift_fullyFaithful β).map_injective
      simp only [Functor.map_comp,Functor.FullyFaithful.preimageIso_hom,
        Functor.FullyFaithful.map_preimage]
      exact η.hom.naturality f)

private theorem cancelBiShiftNatIso_map (β : ℤ×ℤ) (F G : SyntheticSpectrum ⥤ SyntheticSpectrum)
    (η : F ⋙ SyntheticCategory.biShift β ≅ G ⋙ SyntheticCategory.biShift β) (A : SyntheticSpectrum) :
    (SyntheticCategory.biShift β).map ((cancelBiShiftNatIso β F G η).hom.app A)=η.hom.app A := by
  simp only [cancelBiShiftNatIso,NatIso.ofComponents_hom_app,Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage,Iso.app_hom]

private def totalWeightShiftCancellation (a : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,a) ⋙
      SyntheticCategory.biShift (0,-a) ≅ SyntheticCategory.biShift (1,0) :=
  biShiftAddIso (1,a) (0,-a) (1,0) (by ext <;> simp)

private def exactTotalSuspensionTransport (a : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a) ⋙
      shiftFunctor SyntheticSpectrum (1:ℤ) ≅ SyntheticCategory.biShift (1,a) :=
  cancelBiShiftNatIso (0,-a) _ _
    (exactSuspensionTransport a ≪≫ (totalWeightShiftCancellation a).symm)

private def canonicalTotalSuspensionTransport (a : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a) ⋙
      shiftFunctor SyntheticSpectrum (1:ℤ) ≅ SyntheticCategory.biShift (1,a) :=
  Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,a)) (SyntheticCategory.biShift_compat 1).symm ≪≫
    biShiftAddIso (0,a) (1,0) (1,a) (by ext <;> simp)

private def normalized_f_total_source_iso
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he) :
    HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map ≅
      (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).obj
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary) :=
  (SyntheticCategory.biShift_fullyFaithful
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))).preimageIso
      (normalized_f_suspended_source_iso T he hT ≪≫
        (totalWeightShiftCancellation (normalizedExponent model.classicalTower T.g)).symm.app _)

private theorem normalized_g_boundary_total_f
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he) :
    HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map ≫
        (exactTotalSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app
          (model.nu.functor.obj (T.Y.obj model.auxiliary)) =
      (-(normalized_f_total_source_iso T he hT).hom) ≫
        (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).map
          (model.normalizedMap T.X T.Y T.f).map := by
  let β : ℤ×ℤ := (0,-(normalizedExponent model.classicalTower T.g : ℤ))
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) β).map_injective
  dsimp only [β]
  simp only [Functor.map_comp,exactTotalSuspensionTransport,cancelBiShiftNatIso_map,
    Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,Functor.map_neg,
    normalized_f_total_source_iso,Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage,Iso.app_hom]
  change (SyntheticCategory.biShift β).map _ ≫
      (exactSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app _ ≫
        (totalWeightShiftCancellation (normalizedExponent model.classicalTower T.g)).inv.app _ = _
  rw [←Category.assoc,normalized_g_boundary_suspended_f T he hT]
  have hn := (totalWeightShiftCancellation (normalizedExponent model.classicalTower T.g)).inv.naturality
    (model.normalizedMap T.X T.Y T.f).map
  simpa only [Preadditive.neg_comp,Functor.comp_map,Category.assoc] using
    congrArg (fun z => (-(normalized_f_suspended_source_iso T he hT).hom)≫z) hn


private def totalSourceRelabel (ef eg : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,ef) ≅
      SyntheticCategory.biShift (1,ef+eg) ⋙ SyntheticCategory.biShift (0,-eg) :=
  (biShiftAddIso (0,ef) (1,0) (1,ef) (by ext <;> simp)).symm ≪≫
    Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,ef)) (totalWeightShiftCancellation eg).symm ≪≫
    Functor.isoWhiskerRight (biShiftAddIso (0,ef) (1,eg) (1,ef+eg) (by ext <;> simp))
      (SyntheticCategory.biShift (0,-eg))

private def totalSourceSignedTransport (ef eg eh : ℤ) (he : ef+eg+eh=1) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,1) ⋙
      SyntheticCategory.biShift (0,-eh) ≅ SyntheticCategory.biShift (1,ef+eg) :=
  cancelBiShiftNatIso (0,-eg) _ _
    (fSourceSignedChi ef eg eh he ≪≫ totalSourceRelabel ef eg)

private def canonicalTotalSourceTransport (ef eg eh : ℤ) (he : ef+eg+eh=1) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,1) ⋙
      SyntheticCategory.biShift (0,-eh) ≅ SyntheticCategory.biShift (1,ef+eg) :=
  biShiftAddIso (1,1) (0,-eh) (1,ef+eg) (by ext <;> dsimp; all_goals omega)

private theorem normalized_f_total_source_signed
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he) :
    (-(normalized_f_total_source_iso T he hT).hom) ≫
        (biShiftAddIso (0,(normalizedExponent model.classicalTower T.f : ℤ))
          (1,(normalizedExponent model.classicalTower T.g : ℤ))
          (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
          (by ext <;> simp)).hom.app _ =
      (normalized_g_raw_cofiber_iso T he hT).hom ≫
        (totalSourceSignedTransport (normalizedExponent model.classicalTower T.f)
          (normalizedExponent model.classicalTower T.g)
          (normalizedExponent model.classicalTower T.h) he).hom.app
          (model.nu.functor.obj (T.X.obj model.auxiliary)) := by
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum)
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map_injective
  simp only [Functor.map_comp,Functor.map_neg,normalized_f_total_source_iso,
    Functor.FullyFaithful.preimageIso_hom,Functor.FullyFaithful.map_preimage,
    totalSourceSignedTransport,cancelBiShiftNatIso_map,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,NatTrans.comp_app]
  rw [←Category.assoc,
    ←normalized_f_suspended_source_signed_total T he hT]
  simp only [totalSourceRelabel,Iso.trans_hom,Iso.symm_hom,Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,NatTrans.comp_app,whiskerLeft_app,whiskerRight_app,
    Category.assoc,Iso.hom_inv_id_app_assoc,Preadditive.neg_comp]
  rfl

private theorem normalized_total_source_double_unshift_detects
    (X : ClassicalObject) (e gshift : ℤ) (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (εe : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εs : XModLambdaN ((SyntheticCategory.biShift (1,gshift)).obj
      ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))) q ≅
      (SyntheticCategory.biShift (1,gshift)).obj
        (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (εtotal : XModLambdaN ((SyntheticCategory.biShift (1,e+gshift)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,e+gshift)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεe : XModLambdaN.incl _ q≫εe.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ q))
    (hεs : XModLambdaN.incl _ q≫εs.hom =
      (SyntheticCategory.biShift (1,gshift)).map (XModLambdaN.incl _ q))
    (hεtotal : XModLambdaN.incl _ q≫εtotal.hom =
      (SyntheticCategory.biShift (1,e+gshift)).map (XModLambdaN.incl _ q))
    (a : BiHom (((t-s,t-k)+(0,e))+(1,gshift)).1 (((t-s,t-k)+(0,e))+(1,gshift)).2
      (XModLambdaN ((SyntheticCategory.biShift (1,gshift)).obj
        ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X (1,e+gshift) (t-s,t-k) q εtotal
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (a≫XModLambdaN.map
            ((biShiftAddIso (0,e) (1,gshift) (1,e+gshift) (by ext <;> simp)).hom.app _) q)))) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X (0,e) (t-s,t-k) q εe
        (quotientClassUnshift _ (1,gshift) ((t-s,t-k)+(0,e)) q εs a)) := by
  let p : ℤ×ℤ := (t-s,t-k)
  let E := biShiftAddIso (Syn:=SyntheticSpectrum) (0,e) (1,gshift) (1,e+gshift) (by ext <;> simp)
  let C₁ := (SyntheticCategory.biShift_comp p (0,e)).app (S_0_0 : SyntheticSpectrum)
  let C₂ := (SyntheticCategory.biShift_comp (p+(0,e)) (1,gshift)).app (S_0_0 : SyntheticSpectrum)
  let C₀ : (SyntheticCategory.biShift (1,e+gshift)).obj (Smn p.1 p.2) ≅
      Smn ((p+(0,e))+(1,gshift)).1 ((p+(0,e))+(1,gshift)).2 :=
    (SyntheticCategory.biShift_comp p (1,e+gshift)).app S_0_0 ≪≫
      eqToIso (congrArg (fun z : ℤ×ℤ => Smn (Syn:=SyntheticSpectrum) z.1 z.2)
        (by ext <;> dsimp <;> omega : p+(1,e+gshift)=(p+(0,e))+(1,gshift)))
  obtain ⟨u,hu⟩ := double_quotient_unshift_up_to_source_automorphism X
    (0,e) (1,gshift) (1,e+gshift) E q (by omega) εe εs εtotal hεe hεs hεtotal
    p.1 p.2 _ _ C₁ C₂ C₀ a
  let b := quotientUnshift X (1,e+gshift) p q εtotal
    (homotopyRegrade (by dsimp [p]; omega) (by dsimp [p]; omega)
      (a≫XModLambdaN.map (E.hom.app _) q))
  have hdirect : (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,e+gshift)).preimage
      (C₀.hom≫a≫XModLambdaN.map (E.hom.app _) q≫εtotal.hom) = b := by
    simp only [b,quotientUnshift,C₀,Iso.trans_hom,Iso.app_hom,eqToIso.hom,
      regrade_precomp,Category.assoc]
  have hnested : quotientUnshift X (0,e) p q εe
      (quotientClassUnshift _ (1,gshift) (p+(0,e)) q εs a) = u.hom≫b := by
    simpa only [quotientUnshift,quotientClassUnshift,C₁,C₂,hdirect,Iso.app_hom] using hu
  change Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
    (finiteTargetLabel model X q s t k x)
    (quotientUnshift X (0,e) p q εe (quotientClassUnshift _ (1,gshift) (p+(0,e)) q εs a))
  rw [hnested]
  exact sphere_automorphism_finite_detects X q k hkq s t x u b ha


private theorem normalized_f_total_raw_boundary_equation
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (q : ℕ) (hq : 0<q) (p : ℤ×ℤ)
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
    (a : BiHom (p+(1,(normalizedExponent model.classicalTower T.g : ℤ))).1 (p+(1,(normalizedExponent model.classicalTower T.g : ℤ))).2 (XModLambdaN
      (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map) q)) :
    quotientClassUnshift _ (1,(normalizedExponent model.classicalTower T.g : ℤ)) p q εA
        (a≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) q) ≫
        finiteExtensionMap model T.X T.Y T.f q =
      quotientUnshift T.Y (1,(normalizedExponent model.classicalTower T.g : ℤ)) p q εB
        (a≫XModLambdaN.map
          (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) q ≫
          XModLambdaN.map
            ((exactTotalSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app _) q) := by
  have hmap : a≫XModLambdaN.map
        (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) q ≫
        XModLambdaN.map
          ((exactTotalSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app _) q =
      (a≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) q) ≫
        XModLambdaN.map ((SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).map
          (model.normalizedMap T.X T.Y T.f).map) q := by
    rw [←model.quotients.functoriality.map_comp,
      normalized_g_boundary_total_f T he hT]
    exact (congrArg (fun z => a≫z) (model.quotients.functoriality.map_comp
      (-(normalized_f_total_source_iso T he hT).hom)
      ((SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).map (model.normalizedMap T.X T.Y T.f).map) q)).trans
        (Category.assoc _ _ _).symm
  rw [hmap]
  exact (quotient_unshift_normalized_map T.X T.Y
    (normalizedExponent model.classicalTower T.f) (normalizedExponent_le_one model.classicalTower T.f)
    (model.normalizedMap T.X T.Y T.f).map (1,(normalizedExponent model.classicalTower T.g : ℤ)) p q hq εA εB hεA hεB _).symm



private theorem normalized_f_total_actual_source_unshift_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (r k : ℕ) (hkr : k<r) (s t : ℤ) (x : Ambient model T.X (s,t))
    (εmain : XModLambdaN ((SyntheticCategory.biShift
      (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) r))
    (εe : XModLambdaN ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.f : ℤ))).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.f : ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) r))
    (εs : XModLambdaN ((SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).obj
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary)) r ≅
      (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).obj
        (XModLambdaN ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary) r))
    (hεmain : XModLambdaN.incl _ r≫εmain.hom=
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).map
          (XModLambdaN.incl _ r))
    (hεe : XModLambdaN.incl _ r≫εe.hom=
      (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.f : ℤ))).map
        (XModLambdaN.incl _ r))
    (hεs : XModLambdaN.incl _ r≫εs.hom=
      (SyntheticCategory.biShift (1,(normalizedExponent model.classicalTower T.g : ℤ))).map
        (XModLambdaN.incl _ r))
    (c : BiHom
      ((t-s,t-k)+(1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).1
      ((t-s,t-k)+(1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).2
      (XModLambdaN (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map) r))
    (hc : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
      (finiteTargetLabel model T.X r s t k x)
      (quotientUnshift T.X
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
        (t-s,t-k) r εmain (c≫XModLambdaN.map (normalized_g_cofiber_iso T he hT).hom r))) :
    let ef : ℤ := normalizedExponent model.classicalTower T.f
    let eg : ℤ := normalizedExponent model.classicalTower T.g
    let p : ℤ×ℤ := (t-s,t-k)
    let a := homotopyRegrade
      (show (p+(1,ef+eg)).1=((p+(0,ef))+(1,eg)).1 by dsimp; omega)
      (show (p+(1,ef+eg)).2=((p+(0,ef))+(1,eg)).2 by dsimp; omega) c
    let α := quotientClassUnshift _ (1,eg) (p+(0,ef)) r εs
      (a≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) r)
    Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
      (finiteTargetLabel model T.X r s t k x)
      (quotientUnshift T.X (0,ef) p r εe α) := by
  dsimp only
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let eh : ℤ := normalizedExponent model.classicalTower T.h
  let p : ℤ×ℤ := (t-s,t-k)
  let old : ℤ×ℤ := (1,ef+eg)
  let A := model.nu.functor.obj (T.X.obj model.auxiliary)
  let R := normalized_g_raw_cofiber_iso T he hT
  let E := biShiftAddIso (Syn:=SyntheticSpectrum) (0,ef) (1,eg) old (by ext <;> simp [old])
  let raw := c≫XModLambdaN.map R.hom r
  let κ := canonicalTotalSourceTransport ef eg eh he
  let χ := totalSourceSignedTransport ef eg eh he
  have hκ : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
      (finiteTargetLabel model T.X r s t k x)
      (quotientUnshift T.X old p r εmain (raw≫XModLambdaN.map (κ.hom.app A) r)) := by
    simpa only [raw,R,κ,canonicalTotalSourceTransport,normalized_g_cofiber_iso,
      Iso.trans_hom,Iso.app_hom,←model.quotients.functoriality.map_comp,Category.assoc,
      ef,eg,eh,old,p,A] using hc
  have hχ := quotient_unshift_two_natural_transports_detects T.X
    (SyntheticCategory.biShift (1,1)⋙SyntheticCategory.biShift (0,-eh)) old χ κ
    r k hkr s t x εmain hεmain raw hκ
  have hsigned : c≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) r≫
      XModLambdaN.map (E.hom.app A) r = raw≫XModLambdaN.map (χ.hom.app A) r := by
    have hm := congrArg (fun z => c≫XModLambdaN.map z r)
      (normalized_f_total_source_signed T he hT)
    simpa only [E,A,old,ef,eg,eh,raw,R,χ,model.quotients.functoriality.map_comp,
      Category.assoc,SyntheticObject.obj] using hm
  let hp : p+old=(p+(0,ef))+(1,eg) := by ext <;> dsimp [p,old] <;> omega
  let a := homotopyRegrade (congrArg Prod.fst hp) (congrArg Prod.snd hp) c
  let b := a≫XModLambdaN.map (-(normalized_f_total_source_iso T he hT).hom) r
  have hback : homotopyRegrade (congrArg Prod.fst hp.symm) (congrArg Prod.snd hp.symm)
      (b≫XModLambdaN.map (E.hom.app A) r)=raw≫XModLambdaN.map (χ.hom.app A) r := by
    dsimp only [b,a]
    rw [←regrade_comp,←regrade_comp,homotopy_regrade_inverse]
    simpa only [Category.assoc] using hsigned
  have hnested := normalized_total_source_double_unshift_detects T.X ef eg r k hkr s t x
    εe εs εmain hεe hεs hεmain b (by
      change Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
        (finiteTargetLabel model T.X r s t k x)
        (quotientUnshift T.X old p r εmain
          (homotopyRegrade (congrArg Prod.fst hp.symm) (congrArg Prod.snd hp.symm)
            (b≫XModLambdaN.map (E.hom.app A) r)))
      rw [hback]
      exact hχ)
  exact hnested

private theorem normalized_f_total_raw_boundary_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
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
            ((canonicalTotalSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app _) q))) :
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
    (canonicalTotalSuspensionTransport (normalizedExponent model.classicalTower T.g))
    q k hkq s t y εB hεB
    (a≫XModLambdaN.map
      (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) q)
    (by simpa only [Category.assoc] using ha)
  simpa only [Category.assoc] using h


end
end KIP126.ProofTools.Internal.Mahowald
