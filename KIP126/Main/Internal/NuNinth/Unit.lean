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
import all KIP126.Main.SectionSeven.NuTargetYLambda
/-! NuNinth:1459–1574, bbac1fc05843 (MIT): the λ-action on the Y
and AF13 correction representatives. Shared unit comparison uses NuTargetYLambda. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace KIP126.Main.Internal.NuNinth
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
open KIP126.Main.SectionSeven.Internal (sphere_unit sphere_unit_label lambda_sphere_unit sphere_unit_label_product_136)
noncomputable section

theorem sphere_lambda_action {A : SyntheticSpectrum}
    (a : BiHom 125 131 A) :
    sphereAction (lambdaMultiply 1 (sphere_unit)) a = lambdaMultiply 1 a := by
  rw [lambda_sphere_unit]
  have hc := graded_coherence.lambda_comm (125,131) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
    eqToIso.hom,eqToIso.inv,eqToHom_refl,Category.comp_id,Category.id_comp] at hc
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp]
  erw [lambdaPow_one graded_coherence, hc]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rfl
theorem lambda_one_finite_detected_136
    (y : model.classical.sphere.Page 2 (11,136))
    (a : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : Detects (model.convergence (.quotient 9 .sphere)) (11,136,131)
      (quotientLabel 9 11 136 5 y) a) :
    Detects (model.convergence (.quotient 9 .sphere)) (11,136,130)
      (quotientLabel 9 11 136 6 y) (lambdaMultiply 1 a) := by
  have hu := model.sphereDetectionCompatible.homotopy_lambda 0 0 1 (sphere_unit)
  change Detects (model.convergence .sphere) (0,0,0-(1:ℕ))
    (sphereLabel 0 0 1 sphere_unit_label) (lambdaMultiply 1 sphere_unit) at hu
  have hh := KIP126.Literature.Standard.finite_action 9 (by decide) 0 0 11 136 1 5
    (sphere_unit_label) y (lambdaMultiply 1 (sphere_unit)) a hu ha
  change Detects (model.convergence (.quotient 9 .sphere)) (11,136,130)
    (quotientLabel 9 11 136 6
      (model.sphereAlgebra.product (0,0) (11,136) (sphere_unit_label) y))
    (sphereAction (lambdaMultiply 1 (sphere_unit)) a) at hh
  rw [sphere_unit_label_product_136 y,sphere_lambda_action] at hh
  exact hh

theorem sphere_unit_action_138 {A : SyntheticSpectrum}
    (a : BiHom 125 138 A) : sphereAction (sphere_unit) a = a := by
  have hu := graded_coherence.left_unit (125,138) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
  unfold sphereAction sphere_unit
  erw [←hu,Iso.inv_hom_id_app_assoc]
theorem sphere_unit_label_product_138
    (y : model.classical.sphere.Page 2 (13,138)) :
    model.sphereAlgebra.product (0,0) (13,138) sphere_unit_label y = y := by
  let b := ((KIP126.Literature.sphereFirstQuotient model) 13 138).symm y
  have hb : (KIP126.Literature.sphereFirstQuotient model) 13 138 b = y :=
    ((KIP126.Literature.sphereFirstQuotient model) 13 138).apply_symm_apply y
  have h := KIP126.Literature.Standard.first_quotient_action 0 0 13 138 sphere_unit b
  change (KIP126.Literature.sphereFirstQuotient model) 13 138 (sphereAction sphere_unit b) =
    model.sphereAlgebra.product (0,0) (13,138) sphere_unit_label
      ((KIP126.Literature.sphereFirstQuotient model) 13 138 b) at h
  rw [sphere_unit_action_138,hb] at h
  exact h.symm

theorem lambda_one_finite_detected_138
    (y : model.classical.sphere.Page 2 (13,138))
    (a : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : Detects (model.convergence (.quotient 9 .sphere)) (13,138,131)
      (quotientLabel 9 13 138 7 y) a) :
    Detects (model.convergence (.quotient 9 .sphere)) (13,138,130)
      (quotientLabel 9 13 138 8 y) (lambdaMultiply 1 a) := by
  have hu := model.sphereDetectionCompatible.homotopy_lambda 0 0 1 (sphere_unit)
  change Detects (model.convergence .sphere) (0,0,0-(1:ℕ))
    (sphereLabel 0 0 1 sphere_unit_label) (lambdaMultiply 1 sphere_unit) at hu
  have hh := KIP126.Literature.Standard.finite_action 9 (by decide) 0 0 13 138 1 7
    (sphere_unit_label) y (lambdaMultiply 1 (sphere_unit)) a hu ha
  change Detects (model.convergence (.quotient 9 .sphere)) (13,138,130)
    (quotientLabel 9 13 138 8
      (model.sphereAlgebra.product (0,0) (13,138) (sphere_unit_label) y))
    (sphereAction (lambdaMultiply 1 (sphere_unit)) a) at hh
  rw [sphere_unit_label_product_138 y,sphere_lambda_action] at hh
  exact hh
end
end KIP126.Main.Internal.NuNinth
