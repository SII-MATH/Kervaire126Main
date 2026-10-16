module
import all KIP126.ProofTools.GeneralizedMahowald.Detection

/-! Removal of the specified zero vertical shift preserves the prescribed
classical label. The page comparison follows from the actual quotient
inclusion square and the definition of the unshifted target label. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem finite_zero_shift_label (X : ClassicalObject) (q : ℕ)
    (s t : ℤ) (k : ℕ) (x : Ambient model X (s,t)) :
    familyPageMap model.family
      (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app
        (model.nu.functor.obj (X.obj model.auxiliary))) q) 2 (s,t,t-k)
      (regradeE2 (by simp) (finiteNuLabel model X q 0 s t k x)) =
        finiteTargetLabel model X q s t k x := by
  unfold finiteNuLabel finiteTargetLabel targetNuLabel
  rw [page_regrade]
  have regrade_cast {B : SyntheticAdamsSS.{0}} {i j : Tridegree} (h : i=j) (z : B.E₂ i) :
      regradeE2 h z = (congrArg (fun k => (B.E₂ k : Type)) h).mp z := by
    subst j
    rfl
  rw [regrade_cast]
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let z : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj A)).E₂ (s,t,t-k) :=
    (congrArg (fun i => ((model.family.obj ((SyntheticCategory.biShift (0,0)).obj A)).E₂ i : Type))
      (show (s,t,t+0-k)=(s,t,t-k) by simp)).mp (model.comparison.nuE2 X 0 s t k x)
  change familyPageMap model.family (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q) 2 (s,t,t-k)
      (familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t-k) z) =
    familyPageMap model.family (XModLambdaN.incl A q) 2 (s,t,t-k)
      (familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app A) 2 (s,t,t-k) z)
  rw [← ModuleCat.comp_apply, family_page_comp, ← XModLambdaN.incl_naturality]
  rw [← family_page_comp, ModuleCat.comp_apply]
  rfl


private theorem finite_zero_shift_detects (X : ClassicalObject) (q : ℕ)
    (s t : ℤ) (k : ℕ) (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN
      ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,0) (.nu X)))) (s,t,t-k)
      (regradeE2 (by simp) (finiteNuLabel model X q 0 s t k x)) a) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) := by
  have h := detects_map (.quotient q (.shift (0,0) (.nu X))) (.quotient q (.nu X))
    (XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) (s,t,t-k) _ a ha
  exact (congrArg (fun z => Detects (model.convergence (.quotient q (.nu X)))
    (s,t,t-k) z (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q))
      (finite_zero_shift_label X q s t k x)).mp h

end
end KIP126.ProofTools.Internal.Mahowald
