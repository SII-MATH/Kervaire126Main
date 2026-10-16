module
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.High125.Filtration
/-! The original Main proof combining the BMQ source product, actual
multiplicative detection and the proved higher-filtration tail. Source:
Main/Solution/Computation/Tmf:30–89 and Route/CofiberAndFiltration:914–942,
bbac1fc05843 (MIT). No strengthened tmf input is assumed. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem source_high_detected : ClassicalDetects (model.classicalConvergence .sphere) (25,150)
    KIP126.Computation.Standard.highClass Standard.high125 := by
  have hk := Standard.kappaBar_detection
  have hw := Standard.w_detection
  have hk2 := Standard.classical_product_detection 4 24 4 24 Standard.g Standard.g
    Standard.kappaBar Standard.kappaBar hk hk
  norm_num at hk2
  have hk4 := Standard.classical_product_detection 8 48 8 48 _ _ _ _ hk2 hk2
  norm_num at hk4
  have hprod := Standard.classical_product_detection 16 96 9 54 _ _ _ _ hk4 hw
  norm_num at hprod
  simpa [KIP126.Computation.Standard.highClass,KIP126.Computation.Standard.product,
    KIP126.Computation.Standard.g_agrees,KIP126.Computation.Standard.delta_agrees,
    eqToHom_refl,ModuleCat.id_apply,LinearMap.id_apply,Category.id_comp,Standard.high125,Standard.classicalSphereProduct] using hprod

theorem high_nonzero_survival : NonzeroSurvival model.classical.sphere (25,150)
    KIP126.Computation.Standard.highClass := by
  obtain ⟨z,hz,a,ha,hgrade⟩ := source_high_detected
  refine ⟨z,hz,?_⟩
  intro hzero
  let F := (model.classicalTower.tower SphereSpectrum).filtration
  have hg : F.toAssociatedGraded 25 (150-25) a=0 := by
    erw [←hgrade,hzero,map_zero]
  have hm := (F.toAssociatedGraded_eq_zero_iff 25 (150-25) a).mp hg
  erw [ha] at hm
  have hm' : Standard.high125 ∈
      (model.classicalTower.tower SphereSpectrum).filtrationSubmodule 26 125 := by
    simpa [F,AbstractAdamsTower.filtration,AbstractAdamsTower.homotopy,OrderIso.apply_symm_apply] using hm
  have hz := classical_filtration26_zero Standard.high125 hm'
  exact Standard.tmf_high125_nonzero (by rw [hz,zero_comp])

theorem high_detected_choice_unique
    (a b : HomotopyGroup (C := Spectrum) 125 SphereSpectrum)
    (ha : ClassicalDetects (model.classicalConvergence .sphere) (25,150)
      KIP126.Computation.Standard.highClass a)
    (hb : ClassicalDetects (model.classicalConvergence .sphere) (25,150)
      KIP126.Computation.Standard.highClass b) : a=b := by
  obtain ⟨z,hz,a',ha',hga⟩ := ha
  obtain ⟨z',hz',b',hb',hgb⟩ := hb
  let P := model.classical.sphere.ssData (25,150)
  have heq := P.infinity_projection_eq_of_page_projection_eq ↑(2-model.classical.sphere.r₀).toNat
    z z' (hz.trans hz'.symm)
  let F := (model.classicalTower.tower SphereSpectrum).filtration
  have hzero : F.toAssociatedGraded 25 (150-25) (a'-b')=0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (hga.symm.trans
      ((congrArg ((model.classicalConvergence .sphere).identification (25,150)).hom heq).trans hgb))
  have hm := (F.toAssociatedGraded_eq_zero_iff 25 (150-25) (a'-b')).mp hzero
  erw [map_sub,ha',hb'] at hm
  apply sub_eq_zero.mp
  apply classical_filtration26_zero (a-b)
  simpa [F,AbstractAdamsTower.filtration,AbstractAdamsTower.homotopy,OrderIso.apply_symm_apply] using hm

theorem high_detected_detector_nonzero
    (a : HomotopyGroup (C := Spectrum) 125 SphereSpectrum)
    (ha : ClassicalDetects (model.classicalConvergence .sphere) (25,150)
      KIP126.Computation.Standard.highClass a) : a ≫ model.auxiliary.detectorUnit ≠ 0 := by
  have h := high_detected_choice_unique a Standard.high125 ha source_high_detected
  rw [h,←Standard.tmfUnit_agrees,←Category.assoc]
  intro hz
  have hzero : Standard.high125 ≫ Standard.tmfUnit=0 := by
    apply (cancel_mono Standard.tmfIso.hom).mp
    simpa only [zero_comp] using hz
  exact Standard.tmf_high125_nonzero hzero

end
end KIP126.Main.Internal.High125
