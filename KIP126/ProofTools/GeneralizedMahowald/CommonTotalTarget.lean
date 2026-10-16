module
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeNativeTarget
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

private def commonRawSuspensionTransport (a : ℤ) (i : ℕ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a) ⋙
      shiftFunctor SyntheticSpectrum (1:ℤ) ≅
    SyntheticCategory.biShift (0,(i:ℤ)+a) ⋙ SyntheticCategory.biShift (1,-(i:ℤ)) :=
  Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,a)) (SyntheticCategory.biShift_compat 1).symm ≪≫
    Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,a))
      (biShiftAddIso (0,(i:ℤ)) (1,-(i:ℤ)) (1,0) (by ext <;> simp)).symm ≪≫
    Functor.isoWhiskerRight
      (biShiftAddIso (0,a) (0,(i:ℤ)) (0,(i:ℤ)+a) (by ext <;> dsimp; omega))
      (SyntheticCategory.biShift (1,-(i:ℤ)))

private def commonTotalSuspensionTransport (a : ℤ) (i : ℕ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,a) ⋙
      shiftFunctor SyntheticSpectrum (1:ℤ) ≅ SyntheticCategory.biShift (1,a) :=
  commonRawSuspensionTransport a i ≪≫
    biShiftAddIso (0,(i:ℤ)+a) (1,-(i:ℤ)) (1,a) (by ext <;> dsimp; omega)

private theorem common_edge_flat_iso_factor (V : SyntheticSpectrum) (a : ℤ) (i q : ℕ)
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,a)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (0,a)).obj (XModLambdaN V (i+q))) :
    (commonEdgeTargetFlatIso V a i q esusp eA).hom =
      esusp.hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map eA.hom ≫
        (commonRawSuspensionTransport a i).hom.app (XModLambdaN V (i+q)) := by
  simp only [commonEdgeTargetFlatIso,commonEdgeTargetIso,commonEdgeFlattenIso,
    commonRawSuspensionTransport,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,
    Functor.mapIso_hom,Functor.map_comp,Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,NatTrans.comp_app,whiskerLeft_app,whiskerRight_app,
    Category.assoc]
  have h1 := (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.naturality eA.hom
  have h2 := (biShiftAddIso (Syn:=SyntheticSpectrum) (0,(i:ℤ)) (1,-(i:ℤ)) (1,0)
    (by ext <;> simp)).inv.naturality eA.hom
  change (shiftFunctor SyntheticSpectrum (1:ℤ)).map _ ≫ _ =
    _ ≫ (SyntheticCategory.biShift (1,0)).map _ at h1
  change (SyntheticCategory.biShift (1,0)).map _ ≫ _ =
    _ ≫ (SyntheticCategory.biShift (1,-(i:ℤ))).map
      ((SyntheticCategory.biShift (0,(i:ℤ))).map _) at h2
  rw [←Category.assoc ((shiftFunctor SyntheticSpectrum (1:ℤ)).map _),h1]
  simp only [Category.assoc]
  rw [←Category.assoc ((SyntheticCategory.biShift (1,0)).map _),h2]
  simp only [Category.assoc]

private def commonTotalQuotientIso (V : SyntheticSpectrum) (a : ℤ) (i q : ℕ)
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,a)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (0,a)).obj (XModLambdaN V (i+q))) :
    XModLambdaN ((SyntheticCategory.biShift (1,a)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (1,a)).obj (XModLambdaN V (i+q)) :=
  (model.quotients.functoriality.functor (i+q)).mapIso
      ((commonTotalSuspensionTransport a i).symm.app V) ≪≫
    commonEdgeTargetFlatIso V a i q esusp eA ≪≫
    (biShiftAddIso (0,(i:ℤ)+a) (1,-(i:ℤ)) (1,a) (by ext <;> dsimp; omega)).app _

private theorem common_total_quotient_inclusion (V : SyntheticSpectrum) (a : ℤ) (i q : ℕ)
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,a)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (0,a)).obj (XModLambdaN V (i+q)))
    (hesusp : XModLambdaN.incl _ (i+q)≫esusp.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+q)))
    (heA : XModLambdaN.incl _ (i+q)≫eA.hom =
      (SyntheticCategory.biShift (0,a)).map (XModLambdaN.incl V (i+q))) :
    XModLambdaN.incl _ (i+q)≫(commonTotalQuotientIso V a i q esusp eA).hom =
      (SyntheticCategory.biShift (1,a)).map (XModLambdaN.incl V (i+q)) := by
  have hfactor := common_edge_flat_iso_factor V a i q esusp eA
  simp only [Functor.comp_obj] at hfactor ⊢
  have hD : XModLambdaN.incl _ (i+q)≫(commonEdgeTargetFlatIso V a i q esusp eA).hom =
      (commonRawSuspensionTransport a i).hom.app V ≫
        (SyntheticCategory.biShift (1,-(i:ℤ))).map
          ((SyntheticCategory.biShift (0,(i:ℤ)+a)).map (XModLambdaN.incl V (i+q))) := by
    simp only [Functor.comp_obj] at hfactor ⊢
    rw [hfactor,←Category.assoc,hesusp]
    have hx := congrArg (fun z => (shiftFunctor SyntheticSpectrum (1:ℤ)).map z ≫
      (commonRawSuspensionTransport a i).hom.app (XModLambdaN V (i+q))) heA
    have hy := (commonRawSuspensionTransport a i).hom.naturality (XModLambdaN.incl V (i+q))
    simpa only [Functor.map_comp,Functor.comp_map,Category.assoc] using hx.trans hy
  simp only [commonTotalQuotientIso,Iso.trans_hom,Functor.mapIso_hom,
    LambdaQuotientFunctoriality.functor,Functor.comp_obj]
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc]
  erw [←Category.assoc (XModLambdaN.incl _ (i+q)),hD]
  have he := (biShiftAddIso (Syn:=SyntheticSpectrum) (0,(i:ℤ)+a) (1,-(i:ℤ)) (1,a)
    (by ext <;> dsimp; omega)).hom.naturality (XModLambdaN.incl V (i+q))
  change (SyntheticCategory.biShift (1,-(i:ℤ))).map
      ((SyntheticCategory.biShift (0,(i:ℤ)+a)).map _) ≫ _ =
    _ ≫ (SyntheticCategory.biShift (1,a)).map _ at he
  simp only [Category.assoc,Iso.app_hom]
  rw [he]
  simp [commonTotalSuspensionTransport,Category.assoc]

private theorem double_pure_unshift_up_to_source_automorphism
    (α β δ : ℤ×ℤ)
    (E : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) α ⋙
      SyntheticCategory.biShift β ≅ SyntheticCategory.biShift δ)
    (m w : ℤ) (V Sα Sβ : SyntheticSpectrum)
    (Cα : (SyntheticCategory.biShift α).obj (Smn m w) ≅ Sα)
    (Cβ : (SyntheticCategory.biShift β).obj Sα ≅ Sβ)
    (Cδ : (SyntheticCategory.biShift δ).obj (Smn m w) ≅ Sβ)
    (a : Sβ ⟶ (SyntheticCategory.biShift β).obj ((SyntheticCategory.biShift α).obj V)) :
    let ffα := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) α
    let ffβ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) β
    let ffδ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
    ∃ u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w,
      ffα.preimage (Cα.hom≫ffβ.preimage (Cβ.hom≫a)) =
        u.hom≫ffδ.preimage (Cδ.hom≫a≫E.hom.app V) := by
  dsimp only
  let ffα := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) α
  let ffβ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) β
  let ffδ := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let b := ffα.preimage (Cα.hom≫ffβ.preimage (Cβ.hom≫a))
  let c := ffδ.preimage (Cδ.hom≫a≫E.hom.app V)
  let U := (E.app (Smn m w)).symm ≪≫
    (SyntheticCategory.biShift β).mapIso Cα ≪≫ Cβ ≪≫ Cδ.symm
  let u := ffδ.preimageIso U
  refine ⟨u,?_⟩
  change b=u.hom≫c
  apply ffδ.map_injective
  have hb : (SyntheticCategory.biShift δ).map b =
      E.inv.app (Smn m w)≫
        (SyntheticCategory.biShift β).map ((SyntheticCategory.biShift α).map b)≫E.hom.app V := by
    have hn := E.hom.naturality b
    exact ((Iso.inv_hom_id_app_assoc E (Smn m w)
      ((SyntheticCategory.biShift δ).map b)).symm).trans
        (congrArg (fun z => E.inv.app (Smn m w)≫z) hn.symm)
  rw [hb]
  simp only [b,u,c,U,Functor.map_comp,Functor.FullyFaithful.map_preimage,
    Functor.FullyFaithful.preimageIso_hom,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Category.assoc,Iso.inv_hom_id_assoc,Iso.app_inv]


private theorem common_total_quotient_sphere_equation
    (V S : SyntheticSpectrum) (e : ℤ) (i q : ℕ)
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj V) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (0,e)).obj (XModLambdaN V (i+q)))
    (a : S ⟶ XModLambdaN (((SyntheticCategory.biShift (0,e)).obj V)⟦(1:ℤ)⟧) (i+q)) :
    a≫XModLambdaN.map ((commonTotalSuspensionTransport e i).hom.app V) (i+q)≫
        (commonTotalQuotientIso V e i q esusp eA).hom =
      a≫(commonEdgeTargetFlatIso V e i q esusp eA).hom≫
        (biShiftAddIso (0,(i:ℤ)+e) (1,-(i:ℤ)) (1,e)
          (by ext <;> dsimp; omega)).hom.app (XModLambdaN V (i+q)) := by
  simp only [commonTotalQuotientIso,Iso.trans_hom,Functor.mapIso_hom,
    LambdaQuotientFunctoriality.functor,Iso.app_hom,Iso.symm_hom]
  rw [←Category.assoc (XModLambdaN.map _ _),←model.quotients.functoriality.map_comp,
    Iso.hom_inv_id_app,model.quotients.functoriality.map_id,Category.id_comp]

private theorem common_total_native_detection
    (Y : ClassicalObject) (e : ℤ) (i q k : ℕ) (hk : k < i+q)
    (s t : ℤ) (y : Ambient model Y (s,t))
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary))) (i+q) ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (i+q)))
    (Sα Sβ : SyntheticSpectrum)
    (Cα : (SyntheticCategory.biShift (0,(i:ℤ)+e)).obj (Smn (t-s) (t-k)) ≅ Sα)
    (Cβ : (SyntheticCategory.biShift (1,-(i:ℤ))).obj Sα ≅ Sβ)
    (Cδ : (SyntheticCategory.biShift (1,e)).obj (Smn (t-s) (t-k)) ≅ Sβ)
    (a : Sβ ⟶ XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))⟦(1:ℤ)⟧) (i+q))
    (ha : Detects (model.convergence (.quotient (i+q) (.nu Y))) (s,t,t-k)
      (finiteTargetLabel model Y (i+q) s t k y)
      ((SyntheticCategory.biShift_fullyFaithful (0,(i:ℤ)+e)).preimage
        (Cα.hom≫(SyntheticCategory.biShift_fullyFaithful (1,-(i:ℤ))).preimage
          (Cβ.hom≫a≫(commonEdgeTargetFlatIso _ e i q esusp eA).hom)))) :
    Detects (model.convergence (.quotient (i+q) (.nu Y))) (s,t,t-k)
      (finiteTargetLabel model Y (i+q) s t k y)
      ((SyntheticCategory.biShift_fullyFaithful (1,e)).preimage
        (Cδ.hom≫a≫XModLambdaN.map
          ((commonTotalSuspensionTransport e i).hom.app _) (i+q)≫
            (commonTotalQuotientIso _ e i q esusp eA).hom)) := by
  let V := model.nu.functor.obj (Y.obj model.auxiliary)
  let E := biShiftAddIso (Syn:=SyntheticSpectrum) (0,(i:ℤ)+e) (1,-(i:ℤ)) (1,e)
    (by ext <;> dsimp; omega)
  let b := a≫(commonEdgeTargetFlatIso V e i q esusp eA).hom
  obtain ⟨u,hu⟩ := double_pure_unshift_up_to_source_automorphism
    (0,(i:ℤ)+e) (1,-(i:ℤ)) (1,e) E (t-s) (t-k)
    (XModLambdaN V (i+q)) Sα Sβ Cα Cβ Cδ b
  let c := (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,e)).preimage
    (Cδ.hom≫b≫E.hom.app (XModLambdaN V (i+q)))
  have hc : Detects (model.convergence (.quotient (i+q) (.nu Y))) (s,t,t-k)
      (finiteTargetLabel model Y (i+q) s t k y) (u.hom≫c) := by
    rw [←hu]
    exact ha
  have hc0 := sphere_automorphism_finite_detects Y (i+q) k hk s t y u.symm (u.hom≫c) hc
  have h0 : Detects (model.convergence (.quotient (i+q) (.nu Y))) (s,t,t-k)
      (finiteTargetLabel model Y (i+q) s t k y) c := by
    simpa only [Iso.symm_hom,Category.assoc,Iso.inv_hom_id_assoc] using hc0
  have heq := common_total_quotient_sphere_equation V Sβ e i q esusp eA a
  have hrepr : (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,e)).preimage
      (Cδ.hom≫a≫XModLambdaN.map ((commonTotalSuspensionTransport e i).hom.app V) (i+q)≫
        (commonTotalQuotientIso V e i q esusp eA).hom) = c := by
    simpa only [c,b,E,Category.assoc] using congrArg
      (fun z => (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,e)).preimage
        (Cδ.hom≫z)) heq
  exact (congrArg (fun z => Detects (model.convergence (.quotient (i+q) (.nu Y))) (s,t,t-k)
    (finiteTargetLabel model Y (i+q) s t k y) z) hrepr).mpr h0

end
end KIP126.ProofTools.Internal.Mahowald
