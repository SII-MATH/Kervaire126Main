module
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import KIP126.AdamsSynthetic
/-! Finite bottom-weight target labels under classical suspension.
Uses the separately authorized first-quotient suspension compatibility.
The weighted case with a positive λ exponent remains a separate step. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem first_label_inline (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) :
    firstLabel model X s t x =
      homotopyRegrade rfl (by simp) ((model.firstQuotient X 0 s t).symm x) := by
  have cast (m w w' : ℤ) (h : w=w') (A : SyntheticSpectrum) (a : BiHom m w A) :
      homotopyRegrade rfl h a = (congrArg (fun v => BiHom m v A) h).mp a := by
    subst w'; rfl
  exact (cast _ _ _ _ _ _).symm

private theorem suspension_first_unshift
    (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) (sx : Ambient model (.shift 1 X) (s,t+1))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hsx : (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x)) :
    quotientUnshift X (1,1) (t-s,t) 1 ε
      (homotopyRegrade (by dsimp; omega) rfl
        ((firstLabel model (.shift 1 X) s (t+1) sx ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
          XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1)) =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hf := firstQuotient_suspension X s t x sx ε hε hsx
  rw [←first_label_inline,←first_label_inline] at hf
  have hc : homotopyRegrade (show (t+1)-s=((t-s,t)+(1,1)).1 by dsimp; omega) rfl
      ((firstLabel model (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
        XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1) =
      shiftHomotopyClass (1,1) (t-s,t)
        (firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫ ε.inv := by
    apply (cancel_mono ε.hom).mp
    rw [←regrade_comp,Category.assoc,hf,homotopy_regrade_inverse,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [hc,quotient_unshift_shift]

private theorem suspension_finite_target_desuspend
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model X (s,t)) (sx : Ambient model (.shift 1 X) (s,t+1))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε₁ : XModLambdaN.incl _ 1 ≫ ε₁.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hsx : (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x))
    (a : BiHom ((t+1)-s) (t+1)
      (XModLambdaN (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) q))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      firstLabel model (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    let a₀ := quotientUnshift X (1,1) (t-s,t) q εq
      (homotopyRegrade (by dsimp; omega) rfl
        (a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q))
    a₀ ≫ (model.quotients.tower _).rho 1 q hq =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a₀ := by
  dsimp only
  have hfirst : (a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q) ≫
      (model.quotients.tower _).rho 1 q hq =
      (firstLabel model (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
        XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1 := by
    rw [Category.assoc,←(model.quotients.natural
      (model.nu.suspensionIso (X.obj model.auxiliary)).hom).rho_naturality,
      ←Category.assoc]
    erw [ha]
  have h : quotientUnshift X (1,1) (t-s,t) q εq
      (homotopyRegrade (by dsimp; omega) rfl
        (a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q)) ≫
      (model.quotients.tower _).rho 1 q hq =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [quotient_unshift_restriction X (1,1) (t-s,t) 1 q (by decide) hq ε₁ εq hε₁ hεq,
      ←regrade_comp,hfirst,suspension_first_unshift X s t x sx ε₁ hε₁ hsx]
  exact ⟨h,first_label_detects_unshifted X q hq s t x _ h⟩

private theorem suspension_finite_target_unshifted
    (X : ClassicalObject) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model X (s,t)) (sx : Ambient model (.shift 1 X) (s,t+1))
    (hsx : (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x))
    (a : BiHom ((t+1)-s) (t+1)
      (XModLambdaN (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) q))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      firstLabel model (.shift 1 X) s (t+1) sx ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    ∃ (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
        (SyntheticCategory.biShift (1,1)).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)),
      XModLambdaN.incl _ q ≫ εq.hom =
        (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q) ∧
      ∃ a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
        a₀ ≫ (model.quotients.tower _).rho 1 q hq =
          firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
        Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a₀ ∧
        homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass (1,1) (t-s,t) a₀) ≫ εq.inv =
          a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q := by
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) 1
    (model.nu.functor.obj (X.obj model.auxiliary))
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) q
    (model.nu.functor.obj (X.obj model.auxiliary))
  have h := suspension_finite_target_desuspend X q hq s t x sx ε₁ εq hε₁ hεq hsx a ha
  refine ⟨εq,hεq,_,h.1,h.2,?_⟩
  rw [←regrade_comp,shift_quotient_unshift,homotopy_regrade_inverse]

end
end KIP126.ProofTools.Internal.Mahowald
