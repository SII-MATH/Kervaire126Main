module
import all KIP126.Def.ProofTools.GeneralizedMahowald.FTransport

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
set_option maxHeartbeats 800000
set_option Elab.async false

private def fSourceRawFunctor (eg eh : ℤ) : SyntheticSpectrum ⥤ SyntheticSpectrum :=
  SyntheticCategory.biShift (1,1) ⋙ SyntheticCategory.biShift (0,-eh) ⋙
    SyntheticCategory.biShift (0,-eg)

private def fSourceChi (ef eg eh : ℤ) (he : ef+eg+eh=1) :
    fSourceRawFunctor eg eh ≅ SyntheticCategory.biShift (1,ef) :=
  Functor.isoWhiskerRight (SyntheticCategory.biShift_comp (1,1) (0,-eh))
      (SyntheticCategory.biShift (0,-eg)) ≪≫
    SyntheticCategory.biShift_comp ((1,1)+(0,-eh)) (0,-eg) ≪≫
    eqToIso (congrArg SyntheticCategory.biShift
      (show ((1,1)+(0,-eh))+(0,-eg)=(1,ef) by ext; rfl; dsimp; omega))

private def fSourceKappa (ef eg eh : ℤ) (he : ef+eg+eh=1) :
    fSourceRawFunctor eg eh ≅ SyntheticCategory.biShift (1,ef) :=
  Functor.isoWhiskerRight
      (biShiftAddIso (1,1) (0,-eh) (1,ef+eg)
        (by ext; rfl; dsimp; omega))
      (SyntheticCategory.biShift (0,-eg)) ≪≫
    biShiftAddIso (1,ef+eg) (0,-eg) (1,ef) (by ext <;> simp)

private def fSourceDifference (ef eg eh : ℤ) (he : ef+eg+eh=1) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,ef) ≅
      SyntheticCategory.biShift (1,ef) :=
  (fSourceKappa ef eg eh he).symm ≪≫ fSourceChi ef eg eh he

private def negativeFunctorAutomorphism (F : SyntheticSpectrum ⥤ SyntheticSpectrum) : F ≅ F where
  hom := { app := fun X => -(𝟙 (F.obj X))
           naturality := by intro X Y f; simp }
  inv := { app := fun X => -(𝟙 (F.obj X))
           naturality := by intro X Y f; simp }
  hom_inv_id := by ext X; simp
  inv_hom_id := by ext X; simp

private def fSourceSignedChi (ef eg eh : ℤ) (he : ef+eg+eh=1) :
    fSourceRawFunctor eg eh ≅ SyntheticCategory.biShift (1,ef) :=
  fSourceChi ef eg eh he ≪≫ negativeFunctorAutomorphism (SyntheticCategory.biShift (1,ef))

private theorem normalized_f_suspended_source_total
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    (normalized_f_suspended_source_iso T he hT).hom ≫
        (biShiftAddIso (0,(normalizedExponent model.classicalTower T.f : ℤ))
          (1,0) (1,(normalizedExponent model.classicalTower T.f : ℤ))
          (by ext <;> simp)).hom.app _ =
      (SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
          (normalized_g_raw_cofiber_iso T he hT).hom ≫
        (fSourceChi (normalizedExponent model.classicalTower T.f)
          (normalizedExponent model.classicalTower T.g)
          (normalizedExponent model.classicalTower T.h) he).hom.app
            (model.nu.functor.obj (T.X.obj model.auxiliary)) := by
  simp [normalized_f_suspended_source_iso,normalized_connecting_tail_iso,
    fSourceChi,biShiftAddIso,Category.assoc]

private theorem normalized_f_suspended_source_signed_total
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he) :
    (-(normalized_f_suspended_source_iso T he hT).hom) ≫
        (biShiftAddIso (0,(normalizedExponent model.classicalTower T.f : ℤ))
          (1,0) (1,(normalizedExponent model.classicalTower T.f : ℤ))
          (by ext <;> simp)).hom.app _ =
      (SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
          (normalized_g_raw_cofiber_iso T he hT).hom ≫
        (fSourceSignedChi (normalizedExponent model.classicalTower T.f)
          (normalizedExponent model.classicalTower T.g)
          (normalizedExponent model.classicalTower T.h) he).hom.app
            (model.nu.functor.obj (T.X.obj model.auxiliary)) := by
  rw [Preadditive.neg_comp,normalized_f_suspended_source_total T he hT]
  simp [fSourceSignedChi,negativeFunctorAutomorphism,Preadditive.comp_neg]

private theorem quotient_unshift_two_natural_transports_detects
    (X : ClassicalObject) (R : SyntheticSpectrum ⥤ SyntheticSpectrum)
    (δ : ℤ×ℤ) (χ κ : R ≅ SyntheticCategory.biShift δ)
    (q k : ℕ) (hkq : k<q) (s t : ℤ) (x : Ambient model X (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q≫ε.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom ((t-s,t-k)+δ).1 ((t-s,t-k)+δ).2
      (XModLambdaN (R.obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X δ (t-s,t-k) q ε (a≫XModLambdaN.map (κ.hom.app _) q))) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X δ (t-s,t-k) q ε (a≫XModLambdaN.map (χ.hom.app _) q)) := by
  let η := κ.symm ≪≫ χ
  have h := quotient_unshift_natural_automorphism_detects X δ q k hkq s t x η ε hε
    (a≫XModLambdaN.map (κ.hom.app _) q) ha
  have hc : κ.hom.app (model.nu.functor.obj (X.obj model.auxiliary)) ≫ η.hom.app _ =
      χ.hom.app _ := by simp [η]
  simpa only [Category.assoc,←model.quotients.functoriality.map_comp,hc] using h

private theorem quotient_two_shifts_on_spheres
    (X : ClassicalObject) (α β δ : ℤ×ℤ)
    (E : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) α ⋙
      SyntheticCategory.biShift β ≅ SyntheticCategory.biShift δ)
    (q : ℕ) (hq : 0<q)
    (εα : XModLambdaN ((SyntheticCategory.biShift α).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift α).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εβ : XModLambdaN ((SyntheticCategory.biShift β).obj
      ((SyntheticCategory.biShift α).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))) q ≅
      (SyntheticCategory.biShift β).obj
        (XModLambdaN ((SyntheticCategory.biShift α).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (εδ : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεα : XModLambdaN.incl _ q≫εα.hom =
      (SyntheticCategory.biShift α).map (XModLambdaN.incl _ q))
    (hεβ : XModLambdaN.incl _ q≫εβ.hom =
      (SyntheticCategory.biShift β).map (XModLambdaN.incl _ q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift β).obj
      ((SyntheticCategory.biShift α).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))) q)) :
    a≫εβ.hom≫(SyntheticCategory.biShift β).map εα.hom≫E.hom.app _ =
      a≫XModLambdaN.map (E.hom.app _) q≫εδ.hom := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let Q := model.quotients.functoriality.functor q
  let b := a≫XModLambdaN.map (E.hom.app A) q
  let f := XModLambdaN.map (E.inv.app A) q≫εβ.hom≫
    (SyntheticCategory.biShift β).map εα.hom≫E.hom.app (XModLambdaN A q)
  have hf : XModLambdaN.incl _ q≫f = XModLambdaN.incl _ q≫εδ.hom := by
    dsimp only [f]
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
      ←Category.assoc (XModLambdaN.incl _ q)]
    erw [hεβ]
    rw [←Category.assoc ((SyntheticCategory.biShift β).map _),←Functor.map_comp,hεα]
    have hn := E.hom.naturality (XModLambdaN.incl A q)
    change (SyntheticCategory.biShift β).map ((SyntheticCategory.biShift α).map
      (XModLambdaN.incl A q)) ≫ E.hom.app (XModLambdaN A q) =
        E.hom.app A≫(SyntheticCategory.biShift δ).map (XModLambdaN.incl A q) at hn
    rw [hn,Iso.inv_hom_id_app_assoc]
    exact hεδ.symm
  have hh := shifted_quotient_sphere_congruence X X δ q q hq le_rfl εδ hεδ
    f εδ.hom hf m w b
  have hc : XModLambdaN.map (E.hom.app A) q≫XModLambdaN.map (E.inv.app A) q=𝟙 _ := by
    rw [←model.quotients.functoriality.map_comp,Iso.hom_inv_id_app,
      model.quotients.functoriality.map_id]
  simpa only [b,f,Category.assoc,←Category.assoc (XModLambdaN.map (E.hom.app A) q),
    hc,Category.id_comp] using hh

private theorem double_quotient_unshift_up_to_source_automorphism
    (X : ClassicalObject) (α β δ : ℤ×ℤ)
    (E : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) α ⋙
      SyntheticCategory.biShift β ≅ SyntheticCategory.biShift δ)
    (q : ℕ) (hq : 0<q)
    (εα : XModLambdaN ((SyntheticCategory.biShift α).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift α).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εβ : XModLambdaN ((SyntheticCategory.biShift β).obj
      ((SyntheticCategory.biShift α).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))) q ≅
      (SyntheticCategory.biShift β).obj
        (XModLambdaN ((SyntheticCategory.biShift α).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (εδ : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεα : XModLambdaN.incl _ q≫εα.hom =
      (SyntheticCategory.biShift α).map (XModLambdaN.incl _ q))
    (hεβ : XModLambdaN.incl _ q≫εβ.hom =
      (SyntheticCategory.biShift β).map (XModLambdaN.incl _ q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (m w : ℤ) (Sα Sβ : SyntheticSpectrum)
    (Cα : (SyntheticCategory.biShift α).obj (Smn m w) ≅ Sα)
    (Cβ : (SyntheticCategory.biShift β).obj Sα ≅ Sβ)
    (Cδ : (SyntheticCategory.biShift δ).obj (Smn m w) ≅ Sβ)
    (a : Sβ ⟶ XModLambdaN ((SyntheticCategory.biShift β).obj
      ((SyntheticCategory.biShift α).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))) q) :
    let ffα := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) α
    let ffβ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) β
    let ffδ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
    ∃ u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w,
      ffα.preimage (Cα.hom≫ffβ.preimage (Cβ.hom≫a≫εβ.hom)≫εα.hom) =
        u.hom≫ffδ.preimage
          (Cδ.hom≫a≫XModLambdaN.map (E.hom.app _) q≫εδ.hom) := by
  dsimp only
  let ffα := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) α
  let ffβ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) β
  let ffδ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let b := ffα.preimage (Cα.hom≫ffβ.preimage (Cβ.hom≫a≫εβ.hom)≫εα.hom)
  let c := ffδ.preimage (Cδ.hom≫a≫XModLambdaN.map (E.hom.app _) q≫εδ.hom)
  let U := (E.app (Smn m w)).symm ≪≫
    (SyntheticCategory.biShift β).mapIso Cα ≪≫ Cβ ≪≫ Cδ.symm
  let u := ffδ.preimageIso U
  refine ⟨u,?_⟩
  change b=u.hom≫c
  apply ffδ.map_injective
  have hb : (SyntheticCategory.biShift δ).map b =
      E.inv.app (Smn m w)≫
        (SyntheticCategory.biShift β).map ((SyntheticCategory.biShift α).map b)≫
          E.hom.app (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) := by
    have hn := E.hom.naturality b
    exact ((Iso.inv_hom_id_app_assoc E (Smn m w)
      ((SyntheticCategory.biShift δ).map b)).symm).trans
        (congrArg (fun z => E.inv.app (Smn m w)≫z) hn.symm)
  rw [hb]
  simp only [b,u,c,U,Functor.map_comp,Functor.FullyFaithful.map_preimage,
    Functor.FullyFaithful.preimageIso_hom,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←Category.assoc a εβ.hom,
    ←Category.assoc (a≫εβ.hom) ((SyntheticCategory.biShift β).map εα.hom)]
  have hqmap := quotient_two_shifts_on_spheres X α β δ E q hq εα εβ εδ
    hεα hεβ hεδ
  -- `Sβ` is a bigraded sphere up to the supplied isomorphism `Cβ`.
  let J : (SyntheticCategory.biShift (α+β)).obj (Smn m w) ≅ Sβ :=
    (SyntheticCategory.biShift_comp α β).symm.app (Smn m w) ≪≫
      (SyntheticCategory.biShift β).mapIso Cα ≪≫ Cβ
  let K : Smn (m+(α+β).1) (w+(α+β).2) ≅ Sβ :=
    (SyntheticCategory.biShift_comp (m,w) (α+β)).symm.app S_0_0 ≪≫ J
  have hqs := hqmap (m+(α+β).1) (w+(α+β).2) (K.hom≫a)
  simp only [Category.assoc] at hqs
  apply (cancel_epi K.hom).mp at hqs
  simpa only [Category.assoc,Iso.app_inv] using congrArg
    (fun z => E.inv.app (Smn m w)≫
      (SyntheticCategory.biShift β).map Cα.hom≫Cβ.hom≫z) hqs

private theorem normalized_source_double_unshift_detects
    (X : ClassicalObject) (e : ℤ) (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (εe : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εs : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))) q ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (εtotal : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεe : XModLambdaN.incl _ q≫εe.hom =
      (SyntheticCategory.biShift (0,e)).map (XModLambdaN.incl _ q))
    (hεs : XModLambdaN.incl _ q≫εs.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ q))
    (hεtotal : XModLambdaN.incl _ q≫εtotal.hom =
      (SyntheticCategory.biShift (1,e)).map (XModLambdaN.incl _ q))
    (a : BiHom (((t-s,t-k)+(0,e))+(1,0)).1 (((t-s,t-k)+(0,e))+(1,0)).2
      (XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X (1,e) (t-s,t-k) q εtotal
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (a≫XModLambdaN.map
            ((biShiftAddIso (0,e) (1,0) (1,e) (by ext <;> simp)).hom.app _) q)))) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X (0,e) (t-s,t-k) q εe
        (quotientClassUnshift _ (1,0) ((t-s,t-k)+(0,e)) q εs a)) := by
  let p : ℤ×ℤ := (t-s,t-k)
  let E := biShiftAddIso (Syn:=SyntheticSpectrum) (0,e) (1,0) (1,e) (by ext <;> simp)
  let C₁ := (SyntheticCategory.biShift_comp p (0,e)).app (S_0_0 : SyntheticSpectrum)
  let C₂ := (SyntheticCategory.biShift_comp (p+(0,e)) (1,0)).app (S_0_0 : SyntheticSpectrum)
  let C₀ : (SyntheticCategory.biShift (1,e)).obj (Smn p.1 p.2) ≅
      Smn ((p+(0,e))+(1,0)).1 ((p+(0,e))+(1,0)).2 :=
    (SyntheticCategory.biShift_comp p (1,e)).app S_0_0 ≪≫
      eqToIso (congrArg (fun z : ℤ×ℤ => Smn (Syn:=SyntheticSpectrum) z.1 z.2)
        (by ext <;> dsimp <;> omega : p+(1,e)=(p+(0,e))+(1,0)))
  obtain ⟨u,hu⟩ := double_quotient_unshift_up_to_source_automorphism X
    (0,e) (1,0) (1,e) E q (by omega) εe εs εtotal hεe hεs hεtotal
    p.1 p.2 _ _ C₁ C₂ C₀ a
  let b := quotientUnshift X (1,e) p q εtotal
    (homotopyRegrade (by dsimp [p]; omega) (by dsimp [p]; omega)
      (a≫XModLambdaN.map (E.hom.app _) q))
  have hdirect : (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,e)).preimage
      (C₀.hom≫a≫XModLambdaN.map (E.hom.app _) q≫εtotal.hom) = b := by
    simp only [b,quotientUnshift,C₀,Iso.trans_hom,Iso.app_hom,eqToIso.hom,
      regrade_precomp,Category.assoc]
  have hnested : quotientUnshift X (0,e) p q εe
      (quotientClassUnshift _ (1,0) (p+(0,e)) q εs a) = u.hom≫b := by
    simpa only [quotientUnshift,quotientClassUnshift,C₁,C₂,hdirect,Iso.app_hom] using hu
  change Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
    (finiteTargetLabel model X q s t k x)
    (quotientUnshift X (0,e) p q εe (quotientClassUnshift _ (1,0) (p+(0,e)) q εs a))
  rw [hnested]
  exact sphere_automorphism_finite_detects X q k hkq s t x u b ha

private theorem quotientClassUnshift_shift
    (A : SyntheticSpectrum) (δ p : ℤ×ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj A) q ≅
      (SyntheticCategory.biShift δ).obj (XModLambdaN A q))
    (a : BiHom p.1 p.2 (XModLambdaN A q)) :
    quotientClassUnshift A δ p q ε (shiftHomotopyClass δ p a≫ε.inv)=a := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  simp [quotientClassUnshift,shiftHomotopyClass,Category.assoc]

private theorem shifted_quotient_total_unshift_detects
    (X : ClassicalObject) (α β δ : ℤ×ℤ) (hαβ : α+β=δ)
    (q k : ℕ) (hkq : k<q) (s t : ℤ) (x : Ambient model X (s,t))
    (εα : XModLambdaN ((SyntheticCategory.biShift α).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift α).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (εβ : XModLambdaN ((SyntheticCategory.biShift β).obj
      ((SyntheticCategory.biShift α).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))) q ≅
      (SyntheticCategory.biShift β).obj
        (XModLambdaN ((SyntheticCategory.biShift α).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (εδ : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεα : XModLambdaN.incl _ q≫εα.hom =
      (SyntheticCategory.biShift α).map (XModLambdaN.incl _ q))
    (hεβ : XModLambdaN.incl _ q≫εβ.hom =
      (SyntheticCategory.biShift β).map (XModLambdaN.incl _ q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (b : BiHom ((t-s,t-k)+α).1 ((t-s,t-k)+α).2
      (XModLambdaN ((SyntheticCategory.biShift α).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (hb : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X α (t-s,t-k) q εα b)) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X δ (t-s,t-k) q εδ
        (homotopyRegrade
          (congrArg Prod.fst (by rw [←hαβ,←add_assoc] : ((t-s,t-k)+α)+β=(t-s,t-k)+δ))
          (congrArg Prod.snd (by rw [←hαβ,←add_assoc] : ((t-s,t-k)+α)+β=(t-s,t-k)+δ))
          ((shiftHomotopyClass β ((t-s,t-k)+α) b≫εβ.inv)≫
            XModLambdaN.map ((biShiftAddIso α β δ hαβ).hom.app _) q))) := by
  let p : ℤ×ℤ := (t-s,t-k)
  let a := shiftHomotopyClass β (p+α) b≫εβ.inv
  let E := biShiftAddIso (Syn:=SyntheticSpectrum) α β δ hαβ
  let C₁ := (SyntheticCategory.biShift_comp p α).app (S_0_0 : SyntheticSpectrum)
  let C₂ := (SyntheticCategory.biShift_comp (p+α) β).app (S_0_0 : SyntheticSpectrum)
  let C₀ : (SyntheticCategory.biShift δ).obj (Smn p.1 p.2) ≅
      Smn ((p+α)+β).1 ((p+α)+β).2 :=
    (SyntheticCategory.biShift_comp p δ).app S_0_0 ≪≫
      eqToIso (congrArg (fun z : ℤ×ℤ => Smn (Syn:=SyntheticSpectrum) z.1 z.2)
        (by rw [←hαβ,←add_assoc] : p+δ=(p+α)+β))
  obtain ⟨u,hu⟩ := double_quotient_unshift_up_to_source_automorphism X α β δ E q (by omega)
    εα εβ εδ hεα hεβ hεδ p.1 p.2 _ _ C₁ C₂ C₀ a
  let c := (SyntheticCategory.biShift_fullyFaithful δ).preimage
    (C₀.hom≫a≫XModLambdaN.map (E.hom.app _) q≫εδ.hom)
  have heq : quotientUnshift X α p q εα b = u.hom≫c := by
    change quotientUnshift X α p q εα
      (quotientClassUnshift _ β (p+α) q εβ a) = u.hom≫c at hu
    dsimp only [a] at hu
    rw [quotientClassUnshift_shift] at hu
    exact hu
  have hc : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) c := by
    have hpre := sphere_automorphism_finite_detects X q k hkq s t x u.symm
      (quotientUnshift X α p q εα b) hb
    rw [heq] at hpre
    simpa only [Iso.symm_hom,←Category.assoc,Iso.inv_hom_id,Category.id_comp] using hpre
  convert hc using 1
  simp only [c,C₀,quotientUnshift,regrade_precomp,Iso.trans_hom,Iso.app_hom,
    eqToIso.hom,Category.assoc,a,p,E]

end
end KIP126.ProofTools.Internal.Mahowald
