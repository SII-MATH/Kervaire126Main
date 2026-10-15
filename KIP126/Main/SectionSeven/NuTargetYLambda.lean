module
public import KIP126.Main.SectionSeven.Predicates
public import KIP126.Def.Literature.Standard.Filtration
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.SectionSeven.NuTargetWindows
import all KIP126.Main.Internal.Selected.LambdaOperations
/-! The λ-action and unit comparison used for the Y representative, from
NuTargetHelpers.lean:2384–2387,2427–2521, bbac1fc05843 (MIT). -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
noncomputable section

def sphere_unit : BiHom 0 0 (S_0_0 : SyntheticSpectrum) :=
  SyntheticCategory.biShift_zero.hom.app _
def sphere_unit_label : model.classical.sphere.Page 2 (0,0) :=
  (KIP126.Literature.sphereFirstQuotient model) 0 0 (quotientClass 1 sphere_unit)

theorem lambda_one_one_133
    {X : SyntheticSpectrum} (c : BiHom 125 133 X) :
    lambdaMultiply 1 (lambdaMultiply 1 c) = lambdaMultiply 2 c := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (125,133) (0,-1) (0,-1)
    (125,132) (0,-2) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (125,133) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 1 (Smn 125 133)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add graded_coherence 1 1 2 (by decide) (Smn 125 133)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl
theorem h0_action_right_one
    {X : SyntheticSpectrum} (etaAux : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (c : BiHom 125 131 X) :
    sphereAction etaAux (lambdaMultiply 1 c) = lambdaMultiply 1 (sphereAction etaAux c) := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (0,1) (125,131) (0,-1)
    (125,132) (125,130) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (0,1) (125,131)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift (125,131)).map etaAux))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,131) (0,-1)).inv.naturality etaAux)]
  rfl
theorem lambda_sphere_unit :
    lambdaMultiply 1 (sphere_unit) = SyntheticCategory.lam.app (S_0_0 : SyntheticSpectrum) := by
  have hu := graded_coherence.left_unit (0,-1) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
  unfold lambdaMultiply sphere_unit
  simp only [eqToHom_refl,Category.id_comp]
  erw [←lambdaPow_naturality 1 (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum))]
  erw [←hu,Iso.inv_hom_id_app_assoc]
  exact lambdaPow_one graded_coherence _
theorem sphere_lambda_action {A : SyntheticSpectrum}
    (a : BiHom 125 132 A) :
    sphereAction (lambdaMultiply 1 (sphere_unit)) a = lambdaMultiply 1 a := by
  rw [lambda_sphere_unit]
  have hc := graded_coherence.lambda_comm (125,132) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
    eqToIso.hom,eqToIso.inv,eqToHom_refl,Category.comp_id,Category.id_comp] at hc
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp]
  erw [lambdaPow_one graded_coherence, hc]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rfl
theorem sphere_unit_action_136 {A : SyntheticSpectrum}
    (a : BiHom 125 136 A) : sphereAction (sphere_unit) a = a := by
  have hu := graded_coherence.left_unit (125,136) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
  unfold sphereAction sphere_unit
  erw [←hu,Iso.inv_hom_id_app_assoc]
theorem sphere_unit_label_product_136
    (y : model.classical.sphere.Page 2 (11,136)) :
    model.sphereAlgebra.product (0,0) (11,136) sphere_unit_label y = y := by
  let b := ((KIP126.Literature.sphereFirstQuotient model) 11 136).symm y
  have hb : (KIP126.Literature.sphereFirstQuotient model) 11 136 b = y :=
    ((KIP126.Literature.sphereFirstQuotient model) 11 136).apply_symm_apply y
  have h := KIP126.Literature.Standard.first_quotient_action 0 0 11 136 sphere_unit b
  change (KIP126.Literature.sphereFirstQuotient model) 11 136 (sphereAction sphere_unit b) =
    model.sphereAlgebra.product (0,0) (11,136) sphere_unit_label
      ((KIP126.Literature.sphereFirstQuotient model) 11 136 b) at h
  rw [sphere_unit_action_136,hb] at h
  exact h.symm

theorem lambda_one_finite_detected_136
    (y : model.classical.sphere.Page 2 (11,136))
    (a : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : Detects (model.convergence (.quotient 9 .sphere)) (11,136,132)
      (quotientLabel 9 11 136 4 y) a) :
    Detects (model.convergence (.quotient 9 .sphere)) (11,136,131)
      (quotientLabel 9 11 136 5 y) (lambdaMultiply 1 a) := by
  have hu := model.sphereDetectionCompatible.homotopy_lambda 0 0 1 (sphere_unit)
  change Detects (model.convergence .sphere) (0,0,0-(1:ℕ))
    (sphereLabel 0 0 1 sphere_unit_label) (lambdaMultiply 1 sphere_unit) at hu
  have hh := KIP126.Literature.Standard.finite_action 9 (by decide) 0 0 11 136 1 4
    (sphere_unit_label) y (lambdaMultiply 1 (sphere_unit)) a hu ha
  change Detects (model.convergence (.quotient 9 .sphere)) (11,136,131)
    (quotientLabel 9 11 136 5
      (model.sphereAlgebra.product (0,0) (11,136) (sphere_unit_label) y))
    (sphereAction (lambdaMultiply 1 (sphere_unit)) a) at hh
  rw [sphere_unit_label_product_136 y,sphere_lambda_action] at hh
  exact hh
end
end KIP126.Main.SectionSeven.Internal
