module
public import KIP126.Main.SectionSeven.Predicates
public import KIP126.Def.Literature.Standard.Filtration
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.SectionSeven.NuTargetWindows
import all KIP126.Main.SectionSeven.NuTargetYLambda
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
import all KIP126.Main.Internal.Selected.LambdaOperations
/-! The actual Y-representative error equation from
NuTargetHelpers.lean:2522–2568, bbac1fc05843 (MIT). -/
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

theorem nu_target_y_relation
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) (ν : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (hd : Detects (model.convergence .sphere) (1,1,1)
      (sphereLabel 1 1 0 (KIP126.Computation.Standard.h0)) h0)
    (hgap : cycles model .sphere 3 (12,137) ≤ boundaries model .sphere 7 (12,137))
    (hprod : ∀ x : model.classical.sphere.Page 2 (13,138),
      model.sphereAlgebra.product (1,1) (13,138)
        (KIP126.Computation.Standard.h0) x ∈ boundaries model .sphere 2 (14,139))
    (Y : model.classical.sphere.Page 2 (11,136))
    (y0 : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hy0 : Detects (model.convergence (.quotient 9 .sphere)) (11,136,132)
      (quotientLabel 9 11 136 4 Y) y0)
    (x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (y : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hy : FiniteDetected 9 (by decide) 11 136 5 Y y)
    (hxy : sphereAction ν x=lambdaMultiply 1 y) :
    sphereAction h0 (sphereAction ν x)=lambdaMultiply 2 (sphereAction h0 y0) := by
  have hly := lambda_one_finite_detected_136 Y y0 hy0
  let ly : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := lambdaMultiply 1 y0
  let e : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := y-ly
  have hef : FiltrationAtLeast model.syntheticTower 12 e :=
    by simpa only [e,ly,Int.reduceAdd] using
      detects_sub_filtration (model.convergence (.quotient 9 .sphere)) (11,136,131) hy.1 hly
  have hez := nu_target_finite_error_twice_zero h0 hd hgap hprod e hef
  have heq : lambdaMultiply 1 (sphereAction h0 y)=
      lambdaMultiply 1 (sphereAction h0 ly) := by
    apply sub_eq_zero.mp
    simpa only [e,sphereAction,lambdaMultiply,Preadditive.comp_sub,Functor.map_sub,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one] using hez
  rw [hxy,h0_action_right_one,heq]
  have hright : sphereAction h0 ly=lambdaMultiply 1 (sphereAction h0 y0) := by
    change sphereAction h0 (lambdaMultiply 1 y0)=lambdaMultiply 1 (sphereAction h0 y0)
    -- The same coherence calculation at weight 132.
    have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (0,1) (125,132) (0,-1)
      (125,133) (125,131) (125,132) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift_comp (0,1) (125,132)).inv.app (S_0_0 : SyntheticSpectrum)))]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift (125,132)).map h0))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,132) (0,-1)).inv.naturality h0)]
    rfl
  rw [hright,lambda_one_one_133]
end
end KIP126.Main.SectionSeven.Internal
