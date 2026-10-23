module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.SectionSeven.NuTargetWindows
public import KIP126.SSComputation.Table
import all KIP126.Main.SectionSeven.NuTargetFinite
import all KIP126.Main.SectionSeven.NuTargetProducts
import all KIP126.Main.SectionSeven.NuTargetH0Products
import all KIP126.Main.SectionSeven.NuTargetFiniteGap
import all KIP126.Main.SectionSeven.NuTargetYRelation
import all KIP126.Main.SectionSeven.NuTargetCommute
/-! Final ν-target assembly from NuTargetHelpers.lean:2087–2812,
bbac1fc05843 (MIT). The intervening finite calculations and actual
representative equations are proved in the imported internal files. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section

theorem lambda_zero_0_1 (a : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) :
    lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (0,1) (S_0_0 : SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : SyntheticSpectrum) := by
    change (biShiftAddIso (0,1) (0,0) (0,1) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : SyntheticSpectrum) ≫ a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]


theorem nu_target_full_of_nonzero
    (nu : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (hnu : (KIP126.Literature.sphereFirstQuotient model) 1 4 (quotientClass 1 nu)=KIP126.Computation.Standard.h2)
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (hh0 : (KIP126.Literature.sphereFirstQuotient model) 1 1 (quotientClass 1 h0)=KIP126.Computation.Standard.h0)
    (hext : NuExtension9 KIP126.Computation.Standard.X KIP126.Computation.Standard.Y nu)
    (y0 : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hy0 : Detects (model.convergence (.quotient 9 .sphere)) (11,136,132)
      (quotientLabel 9 11 136 4 KIP126.Computation.Standard.Y) y0)
    (hweaknonzero : lambdaMultiply 2 (sphereAction h0 y0)≠0) :
    TargetNuDivisible KIP126.Computation.Standard.T nu := by
  have hh0d := model.sphereDetectionCompatible.homotopy_lambda 1 1 0 h0
  change Detects (model.convergence .sphere) (1,1,1)
    (sphereLabel 1 1 0 ((KIP126.Literature.sphereFirstQuotient model) 1 1 (quotientClass 1 h0))) (lambdaMultiply 0 h0) at hh0d
  rw [hh0,lambda_zero_0_1] at hh0d
  have hgap : cycles model .sphere 3 (12,137) ≤ boundaries model .sphere 7 (12,137) := by
    intro x hx
    obtain ⟨xr,hxr⟩ := (KIP126.ProofTools.isCycle_iff_reaches model .sphere 4 (by decide) (12,137) x).mp ⟨by decide,hx⟩
    haveI : Subsingleton ((model.classical.obj (ClassicalObject.sphere.obj model.auxiliary)).Page 4 (12,137)) :=
      KIP126.Computation.Standard.e4_stem125_af12
    have hz : xr=0 := Subsingleton.elim _ _
    rw [hz] at hxr
    exact boundaries_monotone model .sphere (12,137) (by decide : (3:ℤ)≤7)
      (represents_zero_mem_boundary model .sphere 4 (12,137) x hxr)
  obtain ⟨x,y,hx,hy,hxy⟩ := hext
  have he := nu_target_y_relation h0 nu hh0d hgap nu_target_h0_af13_image_boundary_two
    KIP126.Computation.Standard.Y y0 hy0 x y hy hxy
  have hxF : FiltrationAtLeast model.syntheticTower 8 x :=
    detected_filtration (.quotient 9 .sphere) (8,130,126) hx.1
  have hF := nu_target_h0x_filtration h0 hh0d x hxF
  have hn : sphereAction nu (sphereAction h0 x)≠0 := by
    rw [←h0_nu_actions_commute h0 nu x,he]
    exact hweaknonzero
  exact nu_target_of_finite_nonzero nu hnu nu_target_h2_af13_product_zero _ hF hn

end
end KIP126.Main.SectionSeven.Internal
