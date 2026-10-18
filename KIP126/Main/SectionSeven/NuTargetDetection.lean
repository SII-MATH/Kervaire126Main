module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.SectionSeven.NuTargetWindows
/-! Detection and filtration steps of NuTargetHelpers.lean:955–1070,
1672–1693 at bbac1fc05843 (MIT). -/
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

theorem nu_target_sphere_detected
    (T : model.classical.sphere.Page 2 (14,139))
    (ht : IsPermanentCycle model.classical.sphere (14,139) T)
    (hf : ∃ a : model.classical.sphere.Page 6 (14,139),
      RepresentsOnPage model.classical.sphere 6 (14,139) T a ∧
      ∀ y : model.classical.sphere.Page 6 (14,139),y=0 ∨ y=a)
    (a : BiHom 125 135 (S_0_0 : SyntheticSpectrum))
    (ha : FiltrationAtLeast model.syntheticTower 14 a)
    (hne : quotientClass 9 (lambdaMultiply 4 a) ≠ 0) :
    Detects (model.convergence .sphere) (14,139,135) (sphereLabel 14 139 4 T) a := by
  let F := model.syntheticTower.filtration (S_0_0 : SyntheticSpectrum)
  obtain ⟨a',ha'⟩ := filtration_representative_exists model.syntheticTower _ (125,135) 14 a ha
  let gr := F.toAssociatedGraded 14 (125,135) a'
  let e := ((model.convergence .sphere).identification (14,139,135)).inv gr
  have he : ((model.convergence .sphere).identification (14,139,135)).hom e = gr :=
    ConcreteCategory.congr_hom ((model.convergence .sphere).identification (14,139,135)).inv_hom_id gr
  obtain ⟨b,hb,hall⟩ := hf
  have hq := permanent_quotient_frame_of_page 6 5 (by decide) (by decide)
    14 139 T ht b hb hall
  have hframe := sphere_frame_of_permanent_quotient 14 139 4 T hq
  rcases hframe e with hz | hz
  · have hd0 : Detects (model.convergence .sphere) (14,139,135) 0 a :=
      ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,a',ha',by rw [←hz]; exact he⟩
    have hh := detects_zero_filtration (model.convergence .sphere) (14,139,135) hd0
    have hl := lambda_filtration_preserved 4 15 a hh
    have hproj := map_preserves_filtration
      (model.convergentMap .sphere (.quotient 9 .sphere) (XModLambdaN.incl _ 9))
      (125,131) 15 (lambdaMultiply 4 a) hl
    exact False.elim (hne (sphere_quotient_high_filtration_zero 9 (by decide) 125 131 15 (by decide) _ hproj))
  · exact ⟨e,hz,a',ha',he⟩

theorem nu_target_sphere_products_filtration
    (nu : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (hnu : (KIP126.Literature.sphereFirstQuotient model) 1 4 (quotientClass 1 nu) = KIP126.Computation.Standard.h2)
    (P : model.classical.sphere.Page 2 (11,133)) (Q : model.classical.sphere.Page 2 (12,134))
    (hp : model.sphereAlgebra.product (1,4) (11,133) KIP126.Computation.Standard.h2 P ∈ boundaries model .sphere 2 (12,137))
    (hq : model.sphereAlgebra.product (1,4) (12,134) KIP126.Computation.Standard.h2 Q ∈ boundaries model .sphere 2 (13,138))
    (p : BiHom 122 133 (S_0_0 : SyntheticSpectrum)) (q : BiHom 122 134 (S_0_0 : SyntheticSpectrum))
    (hlp : (KIP126.Literature.sphereFirstQuotient model) 11 133 (quotientClass 1 p) = P)
    (hlq : (KIP126.Literature.sphereFirstQuotient model) 12 134 (quotientClass 1 q) = Q) :
    FiltrationAtLeast model.syntheticTower 14 (sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 1 p)) ∧
    FiltrationAtLeast model.syntheticTower 14 (sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 2 q)) := by
  have hn := model.sphereDetectionCompatible.homotopy_lambda 1 4 1 nu
  change Detects (model.convergence .sphere) (1,4,3)
    (sphereLabel 1 4 1 ((KIP126.Literature.sphereFirstQuotient model) 1 4 (quotientClass 1 nu))) (lambdaMultiply 1 nu) at hn
  rw [hnu] at hn
  constructor
  · have hpd := model.sphereDetectionCompatible.homotopy_lambda 11 133 1 p
    change Detects (model.convergence .sphere) (11,133,132)
      (sphereLabel 11 133 1 ((KIP126.Literature.sphereFirstQuotient model) 11 133 (quotientClass 1 p))) (lambdaMultiply 1 p) at hpd
    rw [hlp] at hpd
    have hd := model.multiplicationCompatible 1 4 11 133 1 1 _ P (lambdaMultiply 1 nu) (lambdaMultiply 1 p) hn hpd
    let v := model.sphereAlgebra.product (1,4) (11,133) KIP126.Computation.Standard.h2 P
    have hb : v ∈ boundaries model .sphere 3 (12,137) :=
      boundaries_monotone model .sphere (12,137) (by decide : (2:ℤ) ≤ 3) hp
    have hz := sphere_boundary_detects_zero 2 12 137 v hb
    have hf : FiltrationAtLeast model.syntheticTower 13 (sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 1 p)) := by
      simpa only [sub_zero,homotopyRegrade,Int.reduceAdd,Int.reduceSub,Nat.reduceAdd,Nat.cast_ofNat] using
        detects_sub_filtration (model.convergence .sphere) (12,137,135) hd hz
    exact (nu_target_sphere_gap KIP126.Computation.Standard.e5_stem125_af13 _).mp hf
  · have hqd := model.sphereDetectionCompatible.homotopy_lambda 12 134 2 q
    change Detects (model.convergence .sphere) (12,134,132)
      (sphereLabel 12 134 2 ((KIP126.Literature.sphereFirstQuotient model) 12 134 (quotientClass 1 q))) (lambdaMultiply 2 q) at hqd
    rw [hlq] at hqd
    have hd := model.multiplicationCompatible 1 4 12 134 1 2 _ Q (lambdaMultiply 1 nu) (lambdaMultiply 2 q) hn hqd
    let v := model.sphereAlgebra.product (1,4) (12,134) KIP126.Computation.Standard.h2 Q
    have hb : v ∈ boundaries model .sphere 4 (13,138) :=
      boundaries_monotone model .sphere (13,138) (by decide : (2:ℤ) ≤ 4) hq
    have hz := sphere_boundary_detects_zero 3 13 138 v hb
    simpa only [sub_zero,homotopyRegrade,Int.reduceAdd,Int.reduceSub,Nat.reduceAdd,Nat.cast_ofNat] using
      detects_sub_filtration (model.convergence .sphere) (13,138,135) hd hz

theorem nu_target_remainder_zero
    (nu : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (hd : Detects (model.convergence .sphere) (1,4,4)
      (sphereLabel 1 4 0 KIP126.Computation.Standard.h2) nu)
    (hprod : ∀ x : model.classical.sphere.Page 2 (13,135),
      model.sphereAlgebra.product (1,4) (13,135) KIP126.Computation.Standard.h2 x = 0)
    (a : BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : FiltrationAtLeast model.syntheticTower 13 a) : sphereAction nu a = 0 := by
  obtain ⟨x,_,hx⟩ := finite_sphere_filtration_has_cycle_label 9 8 (by decide) (by decide) 13 135 a ha
  have hm := KIP126.Literature.Standard.finite_action 9 (by decide) 1 4 13 135 0 8
    KIP126.Computation.Standard.h2 x nu a hd hx
  change Detects (model.convergence (.quotient 9 .sphere)) (14,139,131)
    (quotientLabel 9 14 139 8 (model.sphereAlgebra.product (1,4) (13,135) KIP126.Computation.Standard.h2 x))
    (sphereAction nu a) at hm
  rw [hprod x] at hm
  have hz := finite_sphere_boundary_detects_zero 9 8 (by decide) (by decide) 14 139 0 (Submodule.zero_mem _)
  have hf : FiltrationAtLeast model.syntheticTower 15 (sphereAction nu a) := by
    simpa only [sub_zero,homotopyRegrade,Int.reduceAdd,Int.reduceSub,SyntheticObject.obj] using
      detects_sub_filtration (model.convergence (.quotient 9 .sphere)) (14,139,131) hm hz
  exact sphere_quotient_high_filtration_zero 9 (by decide) 125 131 15 (by decide) _ hf

theorem target_first_label_nonzero_detection
    (T : model.classical.sphere.Page 2 (14,139))
    (htn : T ≠ 0) (t : BiHom 125 139 (S_0_0 : SyntheticSpectrum))
    (hlt : (KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t) = T) :
    SphereDetected 14 139 0 T t := by
  have hd := model.sphereDetectionCompatible.homotopy_lambda 14 139 0 t
  change Detects (model.convergence .sphere) (14,139,139)
    (sphereLabel 14 139 0 ((KIP126.Literature.sphereFirstQuotient model) 14 139 (quotientClass 1 t))) (lambdaMultiply 0 t) at hd
  rw [hlt,KIP126.Main.Internal.lambda_zero_125_139] at hd
  refine ⟨hd,?_⟩
  obtain ⟨e,he,_,_,_⟩ := hd
  refine ⟨e,he,?_⟩
  intro he0
  have hn := family_infinity_representative_map model.nu.unitIso.inv (14,139,139) _ _ he
  have hl := sphere_label_to_nu 0 14 139 T
  change familyPageMap model.family model.nu.unitIso.inv 2 (14,139,139)
    (sphereLabel 14 139 0 T) = targetNuLabel model .sphere 14 139 0 T at hl
  rw [hl,he0,map_zero] at hn
  obtain ⟨ht,hz⟩ := (KIP126.Main.Internal.Selected.nu_target_label_iff 14 139 0 T 0).mp hn
  rw [map_zero] at hz
  have hh := (subquotientClass_eq_zero_iff _ _ ⟨T,ht⟩).mp hz.symm
  change T ∈ boundaries model .sphere 1 (14,139) at hh
  rw [boundaries_one] at hh
  exact htn hh

end
end KIP126.Main.SectionSeven.Internal
