module
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection
import all KIP126.Def.ProofTools.GeneralizedMahowald.CofiberIdentification

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
set_option maxHeartbeats 200000
set_option Elab.async false

private theorem shifted_finite_lambda_class_general
    (X : ClassicalObject) (δ : ℤ×ℤ) (q d : ℕ) (hd : 0<d) (hdq : d<q) (s t : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d) ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (εq : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεn : XModLambdaN.incl _ (q-d)≫εn.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ (q-d)))
    (hεq : XModLambdaN.incl _ q≫εq.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    homotopyRegrade (m':=t-s+δ.1) (w':=t+δ.2-d) rfl (by dsimp; omega)
        (shiftHomotopyClass δ (t-s,t-d) (finiteLambdaClass X q d hd hdq s t b)) ≫ εq.inv =
      homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(d:ℤ)) (t-s+δ.1,t+δ.2)
            (shiftHomotopyClass δ (t-s,t) b ≫ εn.inv)) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap := by
  apply (cancel_mono εq.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  unfold finiteLambdaClass
  rw [shift_hom_comp,regrade_comp,shift_hom_comp,regrade_comp]
  simp only [Category.assoc]
  rw [quotient_shift_lambda_on_spheres X δ q d hd hdq εn εq hεn hεq]
  rw [shift_regrade,shift_regrade,shift_regrade]
  simp only [shiftHomotopyClass]
  rw [←Category.assoc]
  apply congrArg (fun z => z ≫ (SyntheticCategory.biShift δ).map
    ((model.quotients.tower _).triangle hd hdq).lambdaMap)
  simpa [biShiftAddIso,Category.assoc] using
    (shift_hom_swap (t-s,t) δ (0,-(d:ℤ)) (t-s+δ.1,t+δ.2) (t-s,t-d)
      (t-s+δ.1,t+δ.2-d)
      rfl (by ext <;> simp [sub_eq_add_neg])
      (by ext <;> simp [sub_eq_add_neg]) (by ext <;> dsimp; omega) b).symm


private theorem quotient_unshift_finite_lambda
    (X : ClassicalObject) (δ : ℤ×ℤ) (q d : ℕ) (hd : 0<d) (hdq : d<q) (s t : ℤ)
    (εn : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d) ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (εq : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεn : XModLambdaN.incl _ (q-d)≫εn.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ (q-d)))
    (hεq : XModLambdaN.incl _ q≫εq.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom ((t-s,t)+δ).1 ((t-s,t)+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d))) :
    quotientUnshift X δ (t-s,t-d) q εq
      (homotopyRegrade (m':=((t-s,t-d)+δ).1) (w':=((t-s,t-d)+δ).2)
          (by simp) (by dsimp; omega)
          (shiftHomotopyClass (0,-(d:ℤ)) (t-s+δ.1,t+δ.2) a) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap) =
      finiteLambdaClass X q d hd hdq s t
        (quotientUnshift X δ (t-s,t) (q-d) εn a) := by
  let b := quotientUnshift X δ (t-s,t) (q-d) εn a
  have hb : shiftHomotopyClass δ (t-s,t) b≫εn.inv=a :=
    shift_quotient_unshift X δ (t-s,t) (q-d) εn a
  have hshift := shifted_finite_lambda_class_general X δ q d hd hdq s t εn εq hεn hεq b
  rw [hb] at hshift
  have hraw := congrArg (homotopyRegrade
    (show t-s+δ.1=((t-s,t-d)+δ).1 from rfl)
    (show t+δ.2-d=((t-s,t-d)+δ).2 from by dsimp; omega)) hshift
  rw [←regrade_comp,homotopy_regrade_inverse] at hraw
  have regrade_trans {B : SyntheticSpectrum} {m₁ m₂ m₃ w₁ w₂ w₃ : ℤ}
      (hm₁ : m₁=m₂) (hm₂ : m₂=m₃) (hw₁ : w₁=w₂) (hw₂ : w₂=w₃)
      (z : BiHom m₁ w₁ B) :
      homotopyRegrade hm₂ hw₂ (homotopyRegrade hm₁ hw₁ z) =
        homotopyRegrade (hm₁.trans hm₂) (hw₁.trans hw₂) z := by
    subst m₂; subst m₃; subst w₂; subst w₃; rfl
  rw [regrade_comp,regrade_trans] at hraw
  change quotientUnshift X δ (t-s,t-d) q εq _ = finiteLambdaClass X q d hd hdq s t b
  rw [←hraw,quotient_unshift_shift]


private theorem quotient_unshift_finite_lambda_detects
    (X : ClassicalObject) (δ : ℤ×ℤ) (q d : ℕ) (hd : 0<d) (hdq : d<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (εn : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d) ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (εq : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεn : XModLambdaN.incl _ (q-d)≫εn.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ (q-d)))
    (hεq : XModLambdaN.incl _ q≫εq.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom ((t-s,t)+δ).1 ((t-s,t)+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (q-d)))
    (ha : quotientUnshift X δ (t-s,t) (q-d) εn a ≫
        (model.quotients.tower _).rho 1 (q-d) (by omega) =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      (finiteTargetLabel model X q s t d x)
      (quotientUnshift X δ (t-s,t-d) q εq
        (homotopyRegrade (m':=((t-s,t-d)+δ).1) (w':=((t-s,t-d)+δ).2)
            (by simp) (by dsimp; omega)
            (shiftHomotopyClass (0,-(d:ℤ)) (t-s+δ.1,t+δ.2) a) ≫
          ((model.quotients.tower _).triangle hd hdq).lambdaMap)) := by
  rw [quotient_unshift_finite_lambda X δ q d hd hdq s t εn εq hεn hεq a]
  exact finite_quotient_lambda_detects X q d hd hdq s t x _ ha

end
end KIP126.ProofTools.Internal.Mahowald
