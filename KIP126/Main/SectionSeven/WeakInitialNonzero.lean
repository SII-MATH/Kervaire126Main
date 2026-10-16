module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.SectionSeven.NuTargetWindows
import all KIP126.Main.SectionSeven.WeakInitialLambda
import all KIP126.Main.SectionSeven.NuTargetYLambda
import all KIP126.Main.Internal.Selected.DetectionOperations
import all KIP126.Main.ClassicalReduction
/-! Nonzero starting bracket argument from WeakInitialNonzero.lean:125–147,568–675 at bbac1fc05843 (MIT). -/
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

theorem sphere_unit_action_139 {A : SyntheticSpectrum}
    (a : BiHom 125 139 A) : sphereAction (sphere_unit) a = a := by
  have hu := graded_coherence.left_unit (125,139) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
  unfold sphereAction sphere_unit
  erw [←hu,Iso.inv_hom_id_app_assoc]
theorem sphere_unit_label_product_139
    (y : model.classical.sphere.Page 2 (14,139)) :
    model.sphereAlgebra.product (0,0) (14,139) sphere_unit_label y = y := by
  let b := ((KIP126.Literature.sphereFirstQuotient model) 14 139).symm y
  have hb : (KIP126.Literature.sphereFirstQuotient model) 14 139 b = y :=
    ((KIP126.Literature.sphereFirstQuotient model) 14 139).apply_symm_apply y
  have h := KIP126.Literature.Standard.first_quotient_action 0 0 14 139 sphere_unit b
  change (KIP126.Literature.sphereFirstQuotient model) 14 139 (sphereAction sphere_unit b) =
    model.sphereAlgebra.product (0,0) (14,139) sphere_unit_label
      ((KIP126.Literature.sphereFirstQuotient model) 14 139 b) at h
  rw [sphere_unit_action_139,hb] at h
  exact h.symm

theorem lambda_eight_target_detected
    (y : model.classical.sphere.Page 2 (14,139))
    (a : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : Detects (model.convergence (.quotient 9 .sphere)) (14,139,139)
      (quotientLabel 9 14 139 0 y) a) :
    Detects (model.convergence (.quotient 9 .sphere)) (14,139,131)
      (quotientLabel 9 14 139 8 y) (lambdaMultiply 8 a) := by
  have hu := model.sphereDetectionCompatible.homotopy_lambda 0 0 8 sphere_unit
  change Detects (model.convergence .sphere) (0,0,0-(8:ℕ))
    (sphereLabel 0 0 8 sphere_unit_label) (lambdaMultiply 8 sphere_unit) at hu
  have hh := KIP126.Literature.Standard.finite_action 9 (by decide) 0 0 14 139 8 0
    sphere_unit_label y (lambdaMultiply 8 sphere_unit) a hu ha
  change Detects (model.convergence (.quotient 9 .sphere)) (14,139,131)
    (quotientLabel 9 14 139 8
      (model.sphereAlgebra.product (0,0) (14,139) sphere_unit_label y))
    (sphereAction (lambdaMultiply 8 sphere_unit) a) at hh
  rw [sphere_unit_label_product_139 y,lambda_left_eight,sphere_unit_action_139] at hh
  exact hh

theorem sphere_finite_detection_nonzero (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : x∈cycles model .sphere ((q:ℤ)-t+(t-k)) (s,t))
    (hn : x∉boundaries model .sphere (1+t-(t-k)) (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : Detects (model.convergence (.quotient q .sphere)) (s,t,t-k) (quotientLabel q s t k x) a) :
    DetectsNonzero (model.convergence (.quotient q .sphere)) (s,t,t-k) (quotientLabel q s t k x) a := by
  refine ⟨ha,?_⟩
  obtain ⟨e,he,aa,haa,hgr⟩ := ha
  refine ⟨e,he,?_⟩
  intro he0
  let g := XModLambdaN.map model.nu.unitIso.inv q
  have henu := family_infinity_representative_map g (s,t,t-k) _ _ he
  change HasInfinityRepresentative (model.family.quotient (model.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
    (familyPageMap model.family (XModLambdaN.map model.nu.unitIso.inv q) 2 (s,t,t-k)
      (quotientLabel q s t k x)) ((model.family.map g).eInftyMap (s,t,t-k) e) at henu
  rw [sphere_quotient_label_to_nu q k s t x,he0,map_zero] at henu
  have hh := (finite_target_label_iff .sphere q hq s t k hk ⟨x,hx⟩ 0).mp henu
  rw [map_zero] at hh
  exact hn ((subquotientClass_eq_zero_iff _ _ ⟨x,hx⟩).mp hh.symm)

theorem nonzero_detection_ne_zero (X : SyntheticObject) (i : Tridegree)
    (x : (model.family.obj (X.obj model.nu model.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj model.nu model.auxiliary))
    (ha : DetectsNonzero (model.convergence X) i x a) : a≠0 := by
  intro hz
  obtain ⟨⟨e,he,b,hb,hgr⟩,e',he',hne⟩ := ha
  have hbb : b=0 := by
    apply (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono
      ((model.syntheticTower.filtration (X.obj model.nu model.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)).arrow)
    simpa only [map_zero,hz] using hb
  have hez : e=0 := by
    apply (ModuleCat.mono_iff_injective ((model.convergence X).identification i).hom).mp inferInstance
    simpa only [hbb,map_zero] using hgr
  exact hne ((he'.unique he).trans hez)

theorem nu_target_lambda_eight_nonzero
    (hc3 : Stem126D6Vanishes) (t : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ht : FiniteDetected 9 (by decide) 14 139 0 KIP126.Computation.Standard.T t) :
    lambdaMultiply 8 t ≠ 0 := by
  have hd := lambda_eight_target_detected KIP126.Computation.Standard.T t ht.1
  have hp := (permanent_cycle_iff_mem .sphere (14,139) _).mp KIP126.Computation.Standard.t_permanent_cycle
  have hn := sphere_finite_detection_nonzero 9 8 (by decide) (by decide) 14 139
    KIP126.Computation.Standard.T (permanentCycles_le_cycles model .sphere (14,139) _ hp) (by
      intro hb
      exact survives_twelve_not_boundary_eleven .sphere (14,139) KIP126.Computation.Standard.T
        (KIP126.Main.d6_vanishes_iff_target_survives_twelve.mp hc3)
        (boundaries_monotone model .sphere (14,139) (by decide) hb)) _ hd
  exact nonzero_detection_ne_zero (.quotient 9 .sphere) (14,139,131) _ _ hn

theorem lambda_two_six_139
    {X : SyntheticSpectrum} (c : BiHom 125 139 X) :
    lambdaMultiply 2 (lambdaMultiply 6 c) = lambdaMultiply 8 c := by
  have ha := KIP126.Main.Internal.Selected.shift_assoc_inv graded_coherence (125,139) (0,-6) (0,-2)
    (125,133) (0,-8) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (125,139) (0,-6)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 2 (lambdaPow 6 (Smn 125 139)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add graded_coherence 6 2 8 (by decide) (Smn 125 139)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl

theorem weak_initial_twice_h0_nonzero
    (hc3 : Stem126D6Vanishes) (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (t : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ht : FiniteDetected 9 (by decide) 14 139 0 KIP126.Computation.Standard.T t)
    (he : sphereAction h0 z=lambdaMultiply 6 t) :
    lambdaMultiply 2 (sphereAction h0 z)≠0 := by
  rw [he,lambda_two_six_139]
  exact nu_target_lambda_eight_nonzero hc3 t ht

end
end KIP126.Main.SectionSeven.Internal
