module
public import KIP126.Main.SectionSeven.Predicates
public import KIP126.Def.Computation.Table.Values
import all KIP126.Main.Internal.AlphaOne.Staircase
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.DetectionLabels
/-! Permanence, nonzero labels and actual sphere detection in
ThetaToda.lean:1076–1110,1226–1427, bbac1fc05843 (MIT).
The generic representative-map arguments reuse the proved public operations. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations KIP126.Main.SectionSeven
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem b_basis_label : KIP126.Computation.Table.basis .sphere 8 70 1=KIP126.Computation.Standard.atom .b := by
  exact KIP126.Computation.Table.basis_value ⟨.named .b,1⟩ (by decide)

theorem b_permanent_from_inputs : IsPermanentCycle model.classical.sphere (8,70) (KIP126.Computation.Standard.atom .b) := by
  rw [←b_basis_label]
  apply AlphaOne.permanent_cycle_of_reaches1000 8 70 (by decide) (by decide)
  have hrow := KIP126.Computation.Table.result
    ⟨.sphere,.reaches,1000,8,70,[1],8,70,[],"S0_AdamsE2_ss",509⟩
    (List.mem_of_getElem? (i:=193) rfl)
  obtain ⟨x,hx,h⟩ := hrow
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 70 [1]=true := rfl
  simp only [KIP126.Computation.Table.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rwa [←hx] at h

theorem b_nonzero_from_inputs : KIP126.Computation.Standard.atom .b ≠ 0 := by
  obtain ⟨e,he⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere,8,70,["83,1","82,1","0,6,18,2"]⟩
    (List.mem_of_getElem? (i:=155) rfl)
  change model.classical.sphere.Page 2 (8,70) ≃ₗ[ℤ] (Fin 3 →₀ ZMod 2) at e
  change ∀i:Fin 3,e.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 8 70 i.val at he
  intro hz
  have hzero : e.symm (Finsupp.single (1:Fin 3) 1)=0 := (he 1).trans (b_basis_label.trans hz)
  have hh:=congrArg (fun z=>e z (1:Fin 3)) hzero
  simp at hh

theorem sphere_lambda_zero_8_70 (a:BiHom (70-8) 70 (S_0_0:SyntheticSpectrum)) : lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (70-8,70) (S_0_0:SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (70-8,70) (0,0)).hom.app (S_0_0:SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn (70-8) 70:SyntheticSpectrum) := by
    change (biShiftAddIso (70-8,70) (0,0) (70-8,70) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (70-8,70) (0,0)).inv.app (S_0_0:SyntheticSpectrum)≫
    (SyntheticCategory.biShift_comp (70-8,70) (0,0)).hom.app (S_0_0:SyntheticSpectrum)≫a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

theorem sphere_zero_weight_nonzero_detection_8_70
    (x:model.classical.sphere.Page 2 (8,70)) (a:BiHom (70-8) 70 (S_0_0:SyntheticSpectrum))
    (ha:KIP126.Literature.sphereFirstQuotient model 8 70 (quotientClass 1 a)=x) (hne:x≠0) :
    SphereDetected 8 70 0 x a := by
  have hd:=model.sphereDetectionCompatible.homotopy_lambda 8 70 0 a
  change Detects (model.convergence .sphere) (8,70,70)
    (sphereLabel 8 70 0 (KIP126.Literature.sphereFirstQuotient model 8 70 (quotientClass 1 a))) (lambdaMultiply 0 a) at hd
  rw [sphere_lambda_zero_8_70,ha] at hd
  refine ⟨hd,?_⟩
  obtain ⟨e,he,_⟩:=hd
  refine ⟨e,he,?_⟩
  have hf:=family_infinity_representative_map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) (8,70,70) _ _ he
  have hfn:=finite_sphere_infinity_nonzero 1 (by decide) 8 70 x hne _ hf
  intro hz
  exact hfn (by rw [hz,map_zero])


theorem sphere_lambda_zero_9_134 (a:BiHom (134-9) 134 (S_0_0:SyntheticSpectrum)) : lambdaMultiply 0 a=a := by
  have hc := model.quotients.coherence.right_unit (134-9,134) (S_0_0:SyntheticSpectrum)
  have he : (SyntheticCategory.biShift_comp (134-9,134) (0,0)).hom.app (S_0_0:SyntheticSpectrum)=
      SyntheticCategory.biShift_zero.hom.app (Smn (134-9) 134:SyntheticSpectrum) := by
    change (biShiftAddIso (134-9,134) (0,0) (134-9,134) (by simp)).hom.app _=_ at hc
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
  dsimp only [lambdaMultiply,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp]
  rw [←he]
  change (SyntheticCategory.biShift_comp (134-9,134) (0,0)).inv.app (S_0_0:SyntheticSpectrum)≫
    (SyntheticCategory.biShift_comp (134-9,134) (0,0)).hom.app (S_0_0:SyntheticSpectrum)≫a=a
  rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]

theorem sphere_zero_weight_nonzero_detection_9_134
    (x:model.classical.sphere.Page 2 (9,134)) (a:BiHom (134-9) 134 (S_0_0:SyntheticSpectrum))
    (ha:KIP126.Literature.sphereFirstQuotient model 9 134 (quotientClass 1 a)=x) (hne:x≠0) :
    SphereDetected 9 134 0 x a := by
  have hd:=model.sphereDetectionCompatible.homotopy_lambda 9 134 0 a
  change Detects (model.convergence .sphere) (9,134,134)
    (sphereLabel 9 134 0 (KIP126.Literature.sphereFirstQuotient model 9 134 (quotientClass 1 a))) (lambdaMultiply 0 a) at hd
  rw [sphere_lambda_zero_9_134,ha] at hd
  refine ⟨hd,?_⟩
  obtain ⟨e,he,_⟩:=hd
  refine ⟨e,he,?_⟩
  have hf:=family_infinity_representative_map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) (9,134,134) _ _ he
  have hfn:=finite_sphere_infinity_nonzero 1 (by decide) 9 134 x hne _ hf
  intro hz
  exact hfn (by rw [hz,map_zero])

theorem h6b_basis_label : KIP126.Computation.Table.basis .sphere 9 134 2 =
    KIP126.Computation.Standard.product (r := (9,134)) KIP126.Computation.Standard.h6
      (KIP126.Computation.Standard.atom .b) := by
  have h := KIP126.Computation.Table.basis_value ⟨.mul (.named .h6) (.named .b),2⟩ (by decide)
  simpa only [KIP126.Computation.Table.Expression.value,KIP126.Computation.Table.Expression.degree,
    KIP126.Computation.Standard.atom_h6] using h

theorem h6b_nonzero_from_inputs : KIP126.Computation.Standard.product (r:=(9,134))
    KIP126.Computation.Standard.h6 (KIP126.Computation.Standard.atom .b)≠0 := by
  obtain ⟨e,he⟩ := KIP126.Computation.Table.basis_correct
    ⟨.sphere,9,134,["391,1","390,1","69,1,82,1","18,1,190,1","0,1,375,1"]⟩
    (List.mem_of_getElem? (i:=173) rfl)
  change model.classical.sphere.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ ZMod 2) at e
  change ∀i:Fin 5,e.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 9 134 i.val at he
  intro hz
  have hzero : e.symm (Finsupp.single (2:Fin 5) 1)=0 := (he 2).trans (h6b_basis_label.trans hz)
  have hh:=congrArg (fun z=>e z (2:Fin 5)) hzero
  simp at hh

theorem theta_b_bracket_label_suffices (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum))
    (b:BiHom 62 70 (S_0_0:SyntheticSpectrum)) (z:BiHom 125 134 (S_0_0:SyntheticSpectrum))
    (hb:SphereDetected 8 70 0 (KIP126.Computation.Standard.atom .b) b)
    (htoda:KIP126.Literature.Route.TripleToda theta KIP126.Literature.Route.syntheticTwo b z)
    (hz:KIP126.Literature.sphereFirstQuotient model 9 134 (quotientClass 1 z)=
      KIP126.Computation.Standard.product (r:=(9,134)) KIP126.Computation.Standard.h6 (KIP126.Computation.Standard.atom .b)) :
    SphereDetected 8 70 0 (KIP126.Computation.Standard.atom .b) b ∧
    SphereDetected 9 134 0 (KIP126.Computation.Standard.product (r:=(9,134))
      KIP126.Computation.Standard.h6 (KIP126.Computation.Standard.atom .b)) z ∧
    KIP126.Literature.Route.TripleToda theta KIP126.Literature.Route.syntheticTwo b z :=
  ⟨hb,sphere_zero_weight_nonzero_detection_9_134 _ z hz h6b_nonzero_from_inputs,htoda⟩
end
end KIP126.Main.Internal.Theta
