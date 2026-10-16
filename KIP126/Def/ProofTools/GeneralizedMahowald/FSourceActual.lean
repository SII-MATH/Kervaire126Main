module
import all KIP126.Def.ProofTools.GeneralizedMahowald.FSourceTransport

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
set_option maxHeartbeats 1600000
set_option Elab.async false

private def quotientShiftAlongIso (β : ℤ×ℤ) (q : ℕ)
    {C A : SyntheticSpectrum} (e : C ≅ A)
    (ε : XModLambdaN ((SyntheticCategory.biShift β).obj A) q ≅
      (SyntheticCategory.biShift β).obj (XModLambdaN A q)) :
    XModLambdaN ((SyntheticCategory.biShift β).obj C) q ≅
      (SyntheticCategory.biShift β).obj (XModLambdaN C q) :=
  (model.quotients.functoriality.functor q).mapIso
      ((SyntheticCategory.biShift β).mapIso e) ≪≫ ε ≪≫
    (SyntheticCategory.biShift β).mapIso
      ((model.quotients.functoriality.functor q).mapIso e.symm)

private theorem quotientShiftAlongIso_inclusion (β : ℤ×ℤ) (q : ℕ)
    {C A : SyntheticSpectrum} (e : C ≅ A)
    (ε : XModLambdaN ((SyntheticCategory.biShift β).obj A) q ≅
      (SyntheticCategory.biShift β).obj (XModLambdaN A q))
    (hε : XModLambdaN.incl _ q≫ε.hom =
      (SyntheticCategory.biShift β).map (XModLambdaN.incl _ q)) :
    XModLambdaN.incl _ q≫(quotientShiftAlongIso β q e ε).hom =
      (SyntheticCategory.biShift β).map (XModLambdaN.incl _ q) := by
  simp only [quotientShiftAlongIso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,
    LambdaQuotientFunctoriality.functor]
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
    ←Category.assoc (XModLambdaN.incl _ q),hε]
  rw [←Functor.map_comp,←XModLambdaN.incl_naturality,Functor.map_comp,
    ←Category.assoc,←Functor.map_comp,Iso.hom_inv_id,CategoryTheory.Functor.map_id,Category.id_comp]

private theorem quotientShiftAlongIso_evaluation (β p : ℤ×ℤ) (q : ℕ)
    {C A : SyntheticSpectrum} (e : C ≅ A)
    (ε : XModLambdaN ((SyntheticCategory.biShift β).obj A) q ≅
      (SyntheticCategory.biShift β).obj (XModLambdaN A q))
    (c : BiHom p.1 p.2 (XModLambdaN C q)) :
    (shiftHomotopyClass β p c≫(quotientShiftAlongIso β q e ε).inv)≫
        XModLambdaN.map ((SyntheticCategory.biShift β).map e.hom) q =
      shiftHomotopyClass β p (c≫XModLambdaN.map e.hom q)≫ε.inv := by
  simp only [quotientShiftAlongIso,Iso.trans_inv,Functor.mapIso_inv,Iso.symm_inv,
    LambdaQuotientFunctoriality.functor,shiftHomotopyClass,Functor.map_comp,Category.assoc]
  rw [←model.quotients.functoriality.map_comp,
    ←Functor.map_comp,Iso.inv_hom_id,CategoryTheory.Functor.map_id,model.quotients.functoriality.map_id,
    Category.comp_id]

private theorem normalized_f_actual_source_unshift_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (r k : ℕ) (hkr : k<r) (s t : ℤ) (x : Ambient model T.X (s,t))
    (εmain : XModLambdaN ((SyntheticCategory.biShift
      (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) r))
    (hεmain : XModLambdaN.incl _ r≫εmain.hom =
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).map
          (XModLambdaN.incl _ r))
    (cGeometry : BiHom
      ((t-s,t-k)+(1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).1
      ((t-s,t-k)+(1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).2
      (XModLambdaN (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map) r))
    (hc : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
      (finiteTargetLabel model T.X r s t k x)
      (quotientUnshift T.X
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
        (t-s,t-k) r εmain
        (cGeometry≫XModLambdaN.map (normalized_g_cofiber_iso T he hT).hom r))) :
    let ef : ℤ := normalizedExponent model.classicalTower T.f
    let eg : ℤ := normalizedExponent model.classicalTower T.g
    let p : ℤ×ℤ := (t-s,t-k)
    let Cg := HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map
    ∃ (εRaw : XModLambdaN ((SyntheticCategory.biShift (0,-eg)).obj Cg) r ≅
        (SyntheticCategory.biShift (0,-eg)).obj (XModLambdaN Cg r))
      (εe : XModLambdaN ((SyntheticCategory.biShift (0,ef)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) r ≅
        (SyntheticCategory.biShift (0,ef)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) r))
      (εs : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
          ((SyntheticCategory.biShift (0,ef)).obj
            (model.nu.functor.obj (T.X.obj model.auxiliary)))) r ≅
        (SyntheticCategory.biShift (1,0)).obj
          (XModLambdaN ((SyntheticCategory.biShift (0,ef)).obj
            (model.nu.functor.obj (T.X.obj model.auxiliary))) r)),
      XModLambdaN.incl _ r≫εRaw.hom=(SyntheticCategory.biShift (0,-eg)).map (XModLambdaN.incl _ r) ∧
      XModLambdaN.incl _ r≫εe.hom=(SyntheticCategory.biShift (0,ef)).map (XModLambdaN.incl _ r) ∧
      XModLambdaN.incl _ r≫εs.hom=(SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ r) ∧
      let aRaw := homotopyRegrade
        (show (((p+(1,ef+eg))+(0,-eg)).1)=(((p+(0,ef))+(1,0)).1) by dsimp; omega)
        (show (((p+(1,ef+eg))+(0,-eg)).2)=(((p+(0,ef))+(1,0)).2) by dsimp; omega)
        (shiftHomotopyClass (0,-eg) (p+(1,ef+eg)) cGeometry≫εRaw.inv)
      let α := quotientClassUnshift _ (1,0) (p+(0,ef)) r εs
        (aRaw≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) r)
      Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
        (finiteTargetLabel model T.X r s t k x)
        (quotientUnshift T.X (0,ef) p r εe α) := by
  dsimp only
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let eh : ℤ := normalizedExponent model.classicalTower T.h
  let p : ℤ×ℤ := (t-s,t-k)
  let old : ℤ×ℤ := (1,ef+eg)
  let β : ℤ×ℤ := (0,-eg)
  let total : ℤ×ℤ := (1,ef)
  let A := model.nu.functor.obj (T.X.obj model.auxiliary)
  let Cg := HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map
  let eCg := normalized_g_cofiber_iso T he hT
  letI := model.exactness.shiftCommShift β
  letI := model.exactness.shiftExact β
  obtain ⟨εβ,hεβ,_⟩ := quotient_shift_exists model.quotients.coherence β r
    ((SyntheticCategory.biShift old).obj A)
  let εRaw := quotientShiftAlongIso β r eCg εβ
  have hεRaw := quotientShiftAlongIso_inclusion β r eCg εβ hεβ
  letI := model.exactness.shiftCommShift (0,ef)
  letI := model.exactness.shiftExact (0,ef)
  obtain ⟨εe,hεe,_⟩ := quotient_shift_exists model.quotients.coherence (0,ef) r A
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨εs,hεs,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) r
    ((SyntheticCategory.biShift (0,ef)).obj A)
  letI := model.exactness.shiftCommShift total
  letI := model.exactness.shiftExact total
  obtain ⟨εtotal,hεtotal,_⟩ := quotient_shift_exists model.quotients.coherence total r A
  refine ⟨εRaw,εe,εs,hεRaw,hεe,hεs,?_⟩
  let a0 := shiftHomotopyClass β (p+old) cGeometry≫εRaw.inv
  have hdegree : (p+old)+β=p+total := by ext <;> dsimp [p,old,β,total] <;> omega
  let a := homotopyRegrade (congrArg Prod.fst hdegree) (congrArg Prod.snd hdegree) a0
  let R := normalized_g_raw_cofiber_iso T he hT
  let raw := a≫XModLambdaN.map ((SyntheticCategory.biShift β).map R.hom) r
  let κ := fSourceKappa ef eg eh he
  let χ := fSourceSignedChi ef eg eh he
  let E := biShiftAddIso (Syn:=SyntheticSpectrum) old β total
    (by ext; rfl; dsimp [old,β,total]; omega)
  have hfactor : (SyntheticCategory.biShift β).map R.hom≫κ.hom.app A =
      (SyntheticCategory.biShift β).map eCg.hom≫E.hom.app A := by
    simp only [κ,fSourceKappa,R,eCg,normalized_g_cofiber_iso,E,old,β,total,
      Iso.trans_hom,Functor.map_comp,Functor.isoWhiskerRight_hom,
      NatTrans.comp_app,Category.assoc]
    rfl
  have hraw0 : a0≫XModLambdaN.map ((SyntheticCategory.biShift β).map R.hom) r≫
      XModLambdaN.map (κ.hom.app A) r =
      (shiftHomotopyClass β (p+old) (cGeometry≫XModLambdaN.map eCg.hom r)≫εβ.inv)≫
        XModLambdaN.map (E.hom.app A) r := by
    rw [←model.quotients.functoriality.map_comp,hfactor,
      model.quotients.functoriality.map_comp,←Category.assoc]
    exact congrArg (fun z => z≫XModLambdaN.map (E.hom.app A) r)
      (quotientShiftAlongIso_evaluation β (p+old) r eCg εβ cGeometry)
  have hfixed : raw≫XModLambdaN.map (κ.hom.app A) r =
      homotopyRegrade (congrArg Prod.fst hdegree) (congrArg Prod.snd hdegree)
        ((shiftHomotopyClass β (p+old) (cGeometry≫XModLambdaN.map eCg.hom r)≫εβ.inv)≫
          XModLambdaN.map (E.hom.app A) r) := by
    simpa only [raw,a,regrade_comp,Category.assoc] using
      congrArg (homotopyRegrade (congrArg Prod.fst hdegree) (congrArg Prod.snd hdegree)) hraw0
  have hκ : Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
      (finiteTargetLabel model T.X r s t k x)
      (quotientUnshift T.X total p r εtotal (raw≫XModLambdaN.map (κ.hom.app A) r)) := by
    rw [hfixed]
    exact shifted_quotient_total_unshift_detects T.X old β total
      (by ext; rfl; dsimp [old,β,total]; omega) r k hkr s t x
      εmain εβ εtotal hεmain hεβ hεtotal _ hc
  have hχ := quotient_unshift_two_natural_transports_detects T.X
    (fSourceRawFunctor eg eh) total χ κ r k hkr s t x εtotal hεtotal raw hκ
  have hsigned : a≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) r≫
      XModLambdaN.map ((biShiftAddIso (0,ef) (1,0) total (by ext <;> simp [total])).hom.app A) r =
      raw≫XModLambdaN.map (χ.hom.app A) r := by
    rw [←model.quotients.functoriality.map_comp,
      normalized_f_suspended_source_signed_total T he hT,
      model.quotients.functoriality.map_comp]
    simp only [raw,χ,β,R,A,ef,eg,eh,Category.assoc]
  let hF : p+total=(p+(0,ef))+(1,0) := by ext <;> dsimp [total] <;> omega
  let aF := homotopyRegrade (congrArg Prod.fst hF) (congrArg Prod.snd hF)
    (a≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) r)
  have hback : homotopyRegrade (congrArg Prod.fst hF.symm) (congrArg Prod.snd hF.symm)
      (aF≫XModLambdaN.map ((biShiftAddIso (0,ef) (1,0) total (by ext <;> simp [total])).hom.app A) r) =
      raw≫XModLambdaN.map (χ.hom.app A) r := by
    change homotopyRegrade (congrArg Prod.fst hF.symm) (congrArg Prod.snd hF.symm)
      (homotopyRegrade (congrArg Prod.fst hF) (congrArg Prod.snd hF)
        (a≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) r)≫
          XModLambdaN.map ((biShiftAddIso (0,ef) (1,0) total (by ext <;> simp [total])).hom.app A) r) = _
    rw [←regrade_comp]
    rw [homotopy_regrade_inverse]
    simpa only [Category.assoc] using hsigned
  have hnested := normalized_source_double_unshift_detects T.X ef r k hkr s t x
    εe εs εtotal hεe hεs hεtotal aF (by
      change Detects (model.convergence (.quotient r (.nu T.X))) (s,t,t-k)
        (finiteTargetLabel model T.X r s t k x)
        (quotientUnshift T.X total p r εtotal
          (homotopyRegrade (congrArg Prod.fst hF.symm) (congrArg Prod.snd hF.symm)
            (aF≫XModLambdaN.map
              ((biShiftAddIso (0,ef) (1,0) total (by ext <;> simp [total])).hom.app A) r)))
      rw [hback]
      exact hχ)
  convert hnested using 1
  simp only [aF,a,a0,p,old,β,total,ef,eg,regrade_precomp,←Category.assoc,eqToHom_trans]

end
end KIP126.ProofTools.Internal.Mahowald
