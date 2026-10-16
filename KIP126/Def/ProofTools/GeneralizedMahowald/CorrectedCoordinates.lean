module
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereMayActual
import all KIP126.Def.ProofTools.GeneralizedMahowald.FSourceActual
import all KIP126.Def.ProofTools.GeneralizedMahowald.MinimalFinalAssembly

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
set_option maxHeartbeats 1000000
set_option Elab.async false

private def commonCorrectedGeometry
    {C D : SyntheticSpectrum} (i : ℕ) (M W : ℤ)
    (eC : C ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D)
    (c : BiHom (M-1) (W+i) D) : BiHom M W C :=
  (biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
    (by ext <;> dsimp <;> omega)).inv.app S_0_0 ≫
    (SyntheticCategory.biShift (1,-(i:ℤ))).map c ≫ eC.inv

private theorem common_corrected_geometry_desuspend
    {C D : SyntheticSpectrum} (i : ℕ) (M W : ℤ)
    (eC : C ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D)
    (c : BiHom (M-1) (W+i) D) :
    (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
      ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
        (by ext <;> dsimp <;> omega)).hom.app S_0_0 ≫
      commonCorrectedGeometry i M W eC c ≫ eC.hom) = c := by
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).map_injective
  simp only [Functor.FullyFaithful.map_preimage,commonCorrectedGeometry,
    Category.assoc,Iso.inv_hom_id,Category.comp_id,Iso.hom_inv_id_app_assoc]

private theorem common_correction_preserves_native_rho
    (X : ClassicalObject) {C : SyntheticSpectrum} (e : ℤ)
    (e₀ : C ≅ (SyntheticCategory.biShift (1,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (i r : ℕ) (hir : i ≤ r)
    (eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) r ≅
      (SyntheticCategory.biShift (1,e)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (M W : ℤ) (c : BiHom M W (XModLambdaN C r))
    (c' : BiHom (M-1) (W+i) ((SyntheticCategory.biShift (0,(i:ℤ)+e)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r)))
    (hρ : c'≫(SyntheticCategory.biShift (0,(i:ℤ)+e)).map
        ((model.quotients.tower _).rho i r hir) =
      (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).preimage
        ((biShiftAddIso (M-1,W+i) (1,-(i:ℤ)) (M,W)
          (by ext <;> dsimp <;> omega)).hom.app S_0_0 ≫ c ≫
          (commonCofiberTargetIso e e₀ i r eQ).hom) ≫
        (SyntheticCategory.biShift (0,(i:ℤ)+e)).map ((model.quotients.tower _).rho i r hir)) :
    quotientShiftDesuspend X (1,e) r eQ M W
        (commonCorrectedGeometry i M W (commonCofiberTargetIso e e₀ i r eQ) c' ≫
          XModLambdaN.map e₀.hom r) ≫ (model.quotients.tower _).rho i r hir =
      quotientShiftDesuspend X (1,e) r eQ M W (c≫XModLambdaN.map e₀.hom r) ≫
        (model.quotients.tower _).rho i r hir := by
  have hleft := common_cofiber_desuspend_eq_shift_cNu X e e₀ i r eQ M W
    (commonCorrectedGeometry i M W (commonCofiberTargetIso e e₀ i r eQ) c')
  dsimp only at hleft
  rw [common_corrected_geometry_desuspend] at hleft
  have hright := common_cofiber_desuspend_eq_shift_cNu X e e₀ i r eQ M W c
  dsimp only at hright
  rw [hright, hleft] at hρ
  rw [shift_regrade,shift_regrade] at hρ
  let Cb := (biShiftAddIso (Syn:=SyntheticSpectrum) (M-1,W-e) (0,(i:ℤ)+e) (M-1,W+i)
    (by ext <;> dsimp <;> omega)).app S_0_0
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,(i:ℤ)+e)).map_injective
  apply (cancel_epi Cb.inv).mp
  simpa only [Cb,Iso.app_inv,Functor.map_comp,Category.assoc] using hρ

private theorem native_bottom_detects_of_restriction
    (X : ClassicalObject) (i r : ℕ) (hi : 0 < i) (hir : i ≤ r) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X i s t 0 x)) a)
    (c : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (hc : c≫(model.quotients.tower _).rho i r hir=a) :
    Detects (model.convergence (.quotient r (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X r s t 0 x)) c := by
  have hfirst := finite_detected_bottom_first X i hi s t x a
    (by rw [zero_weight_label X i s t x]; exact ha)
  apply first_label_detects_unshifted X r (by omega) s t x c
  rw [←(model.quotients.tower _).rho_comp hi hir,←Category.assoc,hc,hfirst]

end
end KIP126.ProofTools.Internal.Mahowald
