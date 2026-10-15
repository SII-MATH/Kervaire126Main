module
public import KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.Internal.AlphaOne.FiniteFrames
import all KIP126.Main.Internal.AlphaOne.Quotients
import all KIP126.Main.Internal.AlphaOne.Staircase
import all KIP126.Main.Internal.AlphaOne.Detection
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.Selected.LambdaOperations

/-! The three actual finite-quotient correction layers of
AlphaOne/Existence.lean:1321–1370, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.SectionSeven KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations KIP126.Main.Internal KIP126.Main.Internal.Selected
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
private theorem normalize_permanent (p : ℤ×ℤ) (x : model.classical.sphere.Page 2 p)
    (hx : IsPermanentCycle model.classical.sphere p x) :
    IsPermanentCycle Normalized.sphere p (Normalized.label p x) := by
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (x : E.Page 2 p) (hx : IsPermanentCycle E p x) :
      IsPermanentCycle E' p ((eqToHom (congrArg (fun A => A.Page 2 p) h)) x) := by
    subst E'
    exact hx
  exact tr _ _ Normalized.sphere_eq.symm x hx

private theorem normalized_permanent_mem (c : ℤ) (p : ℤ×ℤ)
    (x : Normalized.sphere.Page 2 p) (hx : IsPermanentCycle Normalized.sphere p x) :
    x∈cycles c p := by
  obtain ⟨z,hz⟩ := hx
  let P := Normalized.sphere.ssData p
  refine ⟨(Subobject.ofLE (P.Z ⊤) (P.Z ↑(c-1).toNat) (P.Z_anti le_top)) z,?_⟩
  change (Subobject.ofLE _ _ _ ≫ cycleMap ↑(c-1).toNat p) z=x
  simp only [cycleMap,cycleMapFor,←Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

private theorem actual_frame_thirteen :
    ∃ c : KIP126.Literature.cycles model .sphere 5 (13,137),
      c.val=KIP126.Computation.Standard.correction ∧
      ∀ q : KIP126.Literature.CycleQuotient model .sphere 5 7 (13,137),
        q=0 ∨ q=KIP126.Literature.subquotientClass _ _ c := by
  apply frame_actual
  obtain ⟨c,hc,hq⟩ := alpha_all_finite_frames_alpha_finite_frame_13
  refine ⟨c,?_,hq⟩
  rw [←KIP126.Computation.Table.basis_correction]
  exact hc

private theorem actual_frame_fourteen :
    ∃ c : KIP126.Literature.cycles model .sphere 4 (14,138),
      c.val=KIP126.Computation.Table.basis .sphere 14 138 2 ∧
      ∀ q : KIP126.Literature.CycleQuotient model .sphere 4 8 (14,138),
        q=0 ∨ q=KIP126.Literature.subquotientClass _ _ c := by
  apply frame_actual
  have hp := normalize_permanent _ _ full_staircase_high_cycles.1
  change IsPermanentCycle Normalized.sphere (14,138) (Normalized.basis .sphere 14 138 2) at hp
  have hc := normalized_permanent_mem 4 _ _ hp
  refine ⟨⟨_,hc⟩,?_,alpha_all_finite_frames_alpha_finite_frame_14 hc⟩
  exact (Normalized.label_basis _ _ _).symm

private theorem actual_frame_fifteen :
    ∃ c : KIP126.Literature.cycles model .sphere 3 (15,139),
      c.val=KIP126.Computation.Table.basis .sphere 15 139 1+KIP126.Computation.Table.basis .sphere 15 139 3 ∧
      ∀ q : KIP126.Literature.CycleQuotient model .sphere 3 9 (15,139),
        q=0 ∨ q=KIP126.Literature.subquotientClass _ _ c := by
  apply frame_actual
  have hp := normalize_permanent _ _ full_staircase_high_cycles.2
  have hl : Normalized.label (15,139)
      (KIP126.Computation.Table.basis .sphere 15 139 1+KIP126.Computation.Table.basis .sphere 15 139 3)=
      Normalized.basis .sphere 15 139 1+Normalized.basis .sphere 15 139 3 := by
    exact map_add _ _ _
  rw [hl] at hp
  have hc := normalized_permanent_mem 3 _ _ hp
  exact ⟨⟨_,hc⟩,hl.symm,alpha_all_finite_frames_alpha_finite_frame_15 hc⟩
private theorem alpha_three_layer_restriction
    (c13 : BiHom 124 137 (S_0_0 : SyntheticSpectrum))
    (hc13 : KIP126.Literature.sphereFirstQuotient model 13 137 (quotientClass 1 c13)=KIP126.Computation.Standard.correction)
    (c14 : BiHom 124 138 (S_0_0 : SyntheticSpectrum))
    (hc14 : KIP126.Literature.sphereFirstQuotient model 14 138 (quotientClass 1 c14)=KIP126.Computation.Table.basis .sphere 14 138 2)
    (c15 : BiHom 124 139 (S_0_0 : SyntheticSpectrum))
    (hc15 : KIP126.Literature.sphereFirstQuotient model 15 139 (quotientClass 1 c15)=KIP126.Computation.Table.basis .sphere 15 139 1+KIP126.Computation.Table.basis .sphere 15 139 3)
    (z : BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11))
    (hz : FiltrationAtLeast model.syntheticTower 13 z) :
    ∃ b13 b14 b15 : Bool,
      z≫(model.quotients.tower S_0_0).rho 9 11 (by decide) =
      (if b13 then (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 6 (quotientClass 9 c13)) else 0)+
      (if b14 then (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 7 (quotientClass 9 c14)) else 0)+
      (if b15 then (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from lambdaMultiply 8 (quotientClass 9 c15)) else 0) := by
  classical
  obtain ⟨x13,hx13,frame13a⟩ := actual_frame_thirteen
  obtain ⟨x14,hx14,frame14a⟩ := actual_frame_fourteen
  obtain ⟨x15,hx15,frame15a⟩ := actual_frame_fifteen
  have frame13 := finite_sphere_frame 11 6 (by decide) (by decide) 13 137 x13 frame13a
  have frame14 := finite_sphere_frame 11 7 (by decide) (by decide) 14 138 x14 frame14a
  have frame15 := finite_sphere_frame 11 8 (by decide) (by decide) 15 139 x15 frame15a
  rw [hx13] at frame13
  rw [hx14] at frame14
  rw [hx15] at frame15
  let v13 : BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) := lambdaMultiply 6 (quotientClass 11 c13)
  let v14 : BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) := lambdaMultiply 7 (quotientClass 11 c14)
  let v15 : BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11) := lambdaMultiply 8 (quotientClass 11 c15)
  obtain ⟨b13,hb13⟩ := finite_detection_peel 11 (13,137,131) _ frame13 v13
    (sphere_lift_finite_detection 11 (by decide) 6 13 137 _ c13 hc13) z hz
  obtain ⟨b14,hb14⟩ := finite_detection_peel 11 (14,138,131) _ frame14 v14
    (sphere_lift_finite_detection 11 (by decide) 7 14 138 _ c14 hc14) _ hb13
  obtain ⟨b15,hb15⟩ := finite_detection_peel 11 (15,139,131) _ frame15 v15
    (sphere_lift_finite_detection 11 (by decide) 8 15 139 _ c15 hc15) _ hb14
  let rho := (model.quotients.tower S_0_0).rho 9 11 (by decide)
  have hzero : (((z-(if b13 then v13 else 0))-(if b14 then v14 else 0))-(if b15 then v15 else 0))≫rho=0 := by
    apply sphere_quotient_high_filtration_zero 9 (by decide) 124 131 16 (by decide)
    exact Selected.map_filtration (.quotient 11 .sphere) (.quotient 9 .sphere) rho _ hb15
  have hc (n : ℕ) (w : ℤ) (c : BiHom 124 w (S_0_0 : SyntheticSpectrum)) :
      lambdaMultiply n (quotientClass 11 c)≫rho=lambdaMultiply n (quotientClass 9 c) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc,rho,
      FiniteLambdaQuotientTower.rho_quotient]
  refine ⟨b13,b14,b15,?_⟩
  simp only [Preadditive.sub_comp,ite_comp,zero_comp,v13,v14,v15,hc] at hzero
  rw [sub_sub,sub_sub] at hzero
  simpa only [add_assoc] using (sub_eq_zero.mp hzero)



end
end KIP126.Main.Internal.AlphaOne
end
