module

import all KIP126.Main.SectionSeven.WeakYDetection
import all KIP126.Main.SectionSeven.AnyYPeeling
import all KIP126.Main.SectionSeven.NuTargetFull

/-! Partial change-of-representative results for AimPaper Corollary 7.18.

Equal Y labels force the h0-image of their difference into filtration 15.
Multiplication by lambda squared kills this difference in Q9. This proves
choice independence only after that multiplication; it does not assert the
full unmultiplied equation of the corollary. The lambda-six image of a
T-detected representative is independent of its choice as well.
-/

@[expose] section
namespace KIP126.Main.Paper.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations KIP126.Main.SectionSeven KIP126.Main.SectionSeven.Internal
open KIP126.Literature.Standard (syntheticH0)
open KIP126.Computation.Standard (Y T)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem any_y_h0_detected :
    Detects (model.convergence .sphere) (1,1,1)
      (sphereLabel 1 1 0 KIP126.Computation.Standard.h0) syntheticH0 := by
  have h := model.sphereDetectionCompatible.homotopy_lambda 1 1 0 syntheticH0
  change Detects (model.convergence .sphere) (1,1,1)
    (sphereLabel 1 1 0 ((KIP126.Literature.sphereFirstQuotient model) 1 1
      (quotientClass 1 syntheticH0))) (lambdaMultiply 0 syntheticH0) at h
  have hh : (KIP126.Literature.sphereFirstQuotient model) 1 1
      (quotientClass 1 syntheticH0) = KIP126.Computation.Standard.h0 :=
    KIP126.Literature.Standard.toda_h0_label
  rw [hh,lambda_zero_0_1] at h
  exact h

private theorem any_y_h0_difference_filtration_fifteen
    (y y' : BiHom 125 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (hy : FiniteDetected 9 (by decide) 11 136 4 Y y)
    (hy' : FiniteDetected 9 (by decide) 11 136 4 Y y') :
    FiltrationAtLeast model.syntheticTower 15 (sphereAction syntheticH0 (y-y')) := by
  have hf12 : FiltrationAtLeast model.syntheticTower 12 (y-y') :=
    detects_sub_filtration (model.convergence (.quotient 9 .sphere)) (11,136,132) hy.1 hy'.1
  have hf14 := (weak_y_filtration_twelve_fourteen (y-y')).mp hf12
  exact KIP126.Literature.Standard.action_filtration (.quotient 9 .sphere)
    0 1 125 132 1 14 syntheticH0 (y-y')
    (detected_filtration .sphere (1,1,1) any_y_h0_detected) hf14

private theorem any_y_h0_difference_lambda_two_zero
    (y y' : BiHom 125 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (hy : FiniteDetected 9 (by decide) 11 136 4 Y y)
    (hy' : FiniteDetected 9 (by decide) 11 136 4 Y y') :
    lambdaMultiply 2 (sphereAction syntheticH0 (y-y'))=0 := by
  have hf := lambda_filtration_preserved 2 15 _
    (any_y_h0_difference_filtration_fifteen y y' hy hy')
  exact sphere_quotient_high_filtration_zero 9 (by decide) 125 131 15 (by decide) _ hf

private theorem any_y_h0_lambda_two_independent
    (y y' : BiHom 125 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (hy : FiniteDetected 9 (by decide) 11 136 4 Y y)
    (hy' : FiniteDetected 9 (by decide) 11 136 4 Y y') :
    lambdaMultiply 2 (sphereAction syntheticH0 y)=
      lambdaMultiply 2 (sphereAction syntheticH0 y') := by
  have h := any_y_h0_difference_lambda_two_zero y y' hy hy'
  simpa only [sphereAction,lambdaMultiply,Preadditive.comp_sub,sub_eq_zero] using h

private theorem any_y_target_lambda_six_independent
    (t t' : BiHom 125 139 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (ht : FiniteDetected 9 (by decide) 14 139 0 T t)
    (ht' : FiniteDetected 9 (by decide) 14 139 0 T t') :
    lambdaMultiply 6 t = lambdaMultiply 6 t' := by
  have hd : FiltrationAtLeast model.syntheticTower 15 (t-t') :=
    detects_sub_filtration (model.convergence (.quotient 9 .sphere)) (14,139,139) ht.1 ht'.1
  have hh := anyy_lambda_six_filtration_fifteen_zero (t-t') hd
  simpa only [lambdaMultiply,Preadditive.comp_sub,sub_eq_zero] using hh

/-- An actual initial exact equation propagates to every Y representative
only after multiplying by lambda squared. The initial representative and
its target remain the same actual Q9 classes throughout. -/
private theorem any_y_extension_after_lambda_two
    (hc3 : KIP126.Main.Stem126D6Vanishes)
    (y0 : BiHom 125 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (hy0 : FiniteDetected 9 (by decide) 11 136 4 Y y0)
    (t : BiHom 125 139 (XModLambdaN (S_0_0:SyntheticSpectrum) 9))
    (ht : FiniteDetected 9 (by decide) 14 139 0 T t)
    (he : sphereAction syntheticH0 y0=lambdaMultiply 6 t) :
    ∀ y : BiHom 125 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 9),
      FiniteDetected 9 (by decide) 11 136 4 Y y →
      lambdaMultiply 2 (sphereAction syntheticH0 y)=lambdaMultiply 8 t ∧
        lambdaMultiply 8 t≠0 := by
  intro y hy
  refine ⟨?_,nu_target_lambda_eight_nonzero hc3 t ht⟩
  rw [any_y_h0_lambda_two_independent y y0 hy hy0,he,lambda_two_six_139]

end
end KIP126.Main.Paper.Internal
