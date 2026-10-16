module
import all KIP126.Def.ProofTools.GeneralizedMahowald.CommonEdgeNativeTarget
import all KIP126.Def.ProofTools.GeneralizedMahowald.FSourceTransport
import all KIP126.Def.ProofTools.GeneralizedMahowald.CommonTotalTarget
import all KIP126.Def.ProofTools.GeneralizedMahowald.TotalFTransport
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

private theorem common_corrected_geometry_second_image
    {C D U V : SyntheticSpectrum} (i : ℕ) (M W : ℤ)
    (eC : C ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D)
    (eD : U ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj V)
    (h : C ⟶ U) (c : BiHom (M-1) (W+i) D) :
    (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
      ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
        (by ext <;> dsimp; all_goals omega)).hom.app S_0_0 ≫
      commonCorrectedGeometry i M W eC c ≫ h ≫ eD.hom) =
    c ≫ (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
      (eC.inv≫h≫eD.hom) := by
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).map_injective
  simp only [Functor.FullyFaithful.map_preimage,Functor.map_comp,commonCorrectedGeometry,
    Category.assoc,Iso.hom_inv_id_app_assoc]

private theorem common_corrected_total_native_detection
    (Y : ClassicalObject) (e : ℤ) (i q : ℕ) (hq : 0 < q)
    (s t M W : ℤ) (hM : M-1=t-s) (hW : W+i=t+e) (y : Ambient model Y (s,t))
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary))) (i+q) ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (i+q)))
    (C D : SyntheticSpectrum)
    (eC : C ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D)
    (h : C ⟶ XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))⟦(1:ℤ)⟧) (i+q))
    (c : BiHom (M-1) (W+i) D)
    (hc : Detects (model.convergence (.quotient (i+q) (.nu Y))) (s,t,t-i)
      (finiteTargetLabel model Y (i+q) s t i y)
      (commonTargetUnshift (0,(i:ℤ)+e) (t-s,t-i) _
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (c ≫ (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
            (eC.inv≫h≫(commonEdgeTargetFlatIso _ e i q esusp eA).hom))))) :
    Detects (model.convergence (.quotient (i+q) (.nu Y))) (s,t,t-i)
      (finiteTargetLabel model Y (i+q) s t i y)
      (quotientUnshift Y (1,e) (t-s,t-i) (i+q)
        (commonTotalQuotientIso _ e i q esusp eA)
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (commonCorrectedGeometry i M W eC c≫h≫
            XModLambdaN.map ((commonTotalSuspensionTransport e i).hom.app _) (i+q)))) := by
  let V := model.nu.functor.obj (Y.obj model.auxiliary)
  let p : ℤ×ℤ := (t-s,t-i)
  let α : ℤ×ℤ := (0,(i:ℤ)+e)
  let β : ℤ×ℤ := (1,-(i:ℤ))
  let δ : ℤ×ℤ := (1,e)
  let Cα := (biShiftAddIso (Syn:=SyntheticSpectrum) p α (M-1,W+i)
    (by ext <;> dsimp [p,α]; all_goals omega)).app S_0_0
  let Cβ := (biShiftAddIso (Syn:=SyntheticSpectrum) (M-1,W+i) β (M,W)
    (by ext <;> dsimp [β]; all_goals omega)).app S_0_0
  let Cδ := (biShiftAddIso (Syn:=SyntheticSpectrum) p δ (M,W)
    (by ext <;> dsimp [p,δ]; all_goals omega)).app S_0_0
  have hn := common_total_native_detection Y e i q i (by omega) s t y esusp eA
    (Smn (M-1) (W+i)) (Smn M W) Cα Cβ Cδ
    (commonCorrectedGeometry i M W eC c≫h) (by
      dsimp only [Cβ,β]
      simp only [Iso.app_hom,Category.assoc]
      erw [common_corrected_geometry_second_image]
      simpa only [Cα,commonTargetUnshift,biShiftAddIso,Iso.app_hom,Iso.trans_hom,
        eqToIso.hom,eqToHom_app,regrade_precomp,Category.assoc,NatTrans.comp_app,p,α] using hc)
  simpa only [Cδ,quotientUnshift,biShiftAddIso,Iso.app_hom,Iso.trans_hom,NatTrans.comp_app,
    eqToIso.hom,eqToHom_app,regrade_precomp,Category.assoc,p,δ] using hn

end
end KIP126.ProofTools.Internal.Mahowald
