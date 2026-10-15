module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Def.Computation.Table.Values
import all KIP126.Main.Internal.LambdaZero
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.SectionSeven.NuTargetCosets
import all KIP126.Main.SectionSeven.NuTargetPeeling
import all KIP126.Main.SectionSeven.NuTargetFrame
import all KIP126.Main.SectionSeven.NuTargetDetection
import all KIP126.Main.SectionSeven.NuTargetLambda
/-! The P/Q alternative giving the actual target division, from
NuTargetHelpers.lean:1071–1103,1694–1764 (bbac1fc05843, MIT). -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal
open KIP126.Computation.Standard KIP126.ProofTools.Operations
noncomputable section

theorem boundary_by_is_boundary {p : ℤ×ℤ}
    {x : model.classical.sphere.Page 2 p}
    (hx : IsBoundaryBy model.classical.sphere 2 p x) :
    x ∈ boundaries model .sphere 2 p := by
  exact represents_zero_mem_boundary model .sphere 3 p x
    (KIP126.Core.SpectralSequence.PageThree.boundary_represents_zero hx)

theorem nu_target_pq_boundaries :
    model.sphereAlgebra.product (1,4) (11,133) h2 P ∈ boundaries model .sphere 2 (12,137) ∧
    model.sphereAlgebra.product (1,4) (12,134) h2 Q ∈ boundaries model .sphere 2 (13,138) := by
  constructor
  · have h := boundary_by_is_boundary p_h2_boundary
    have hc := KIP126.Computation.Table.product_comm 1 4 11 133 (by decide) h2 P
    change product h2 P ∈ boundaries model .sphere 2 (12,137)
    rw [hc]
    exact h
  · have h := boundary_by_is_boundary q_h2_boundary
    have hc := KIP126.Computation.Table.product_comm 1 4 12 134 (by decide) h2 Q
    change product h2 Q ∈ boundaries model .sphere 2 (13,138)
    rw [hc]
    exact h

theorem nu_target_of_finite_nonzero
    (nu : BiHom 3 4 (S_0_0 : SyntheticSpectrum))
    (hnu : (KIP126.Literature.sphereFirstQuotient model) 1 4 (quotientClass 1 nu) = h2)
    (hprod : ∀ x : model.classical.sphere.Page 2 (13,135),
      model.sphereAlgebra.product (1,4) (13,135) h2 x = 0)
    (a0 : BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha0 : FiltrationAtLeast model.syntheticTower 11 a0)
    (hne : sphereAction nu a0 ≠ 0) : TargetNuDivisible T nu := by
  obtain ⟨p,q,bp,bq,hp,hq,hrem⟩ := pq_lift_peel p_cosets q_cosets a0 ha0
  let a : BiHom 122 132 (S_0_0 : SyntheticSpectrum) :=
    (if bp then (show BiHom 122 132 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 p) else 0)+
    (if bq then (show BiHom 122 132 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 2 q) else 0)
  let v : BiHom 125 135 (S_0_0 : SyntheticSpectrum) := sphereProduct (lambdaMultiply 1 nu) a
  let b : BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := quotientClass 9 (lambdaMultiply 5 a)
  have hb : b=
      (if bp then (show BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from quotientClass 9 (lambdaMultiply 6 p)) else 0)+
      (if bq then (show BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from quotientClass 9 (lambdaMultiply 7 q)) else 0) := by
    let f : BiHom 122 132 (S_0_0 : SyntheticSpectrum) →+ BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) :=
      { toFun := fun c=>quotientClass 9 (lambdaMultiply 5 c)
        map_zero' := by simp only [lambdaMultiply,quotientClass,CategoryTheory.Limits.comp_zero,CategoryTheory.Limits.zero_comp]
        map_add' := by intros; simp only [lambdaMultiply,quotientClass,Preadditive.comp_add,Preadditive.add_comp] }
    have hp5 : f (lambdaMultiply 1 p)=quotientClass 9 (lambdaMultiply 6 p) :=
      congrArg (quotientClass 9) (nu_target_five_one p)
    have hq5 : f (lambdaMultiply 2 q)=quotientClass 9 (lambdaMultiply 7 q) :=
      congrArg (quotientClass 9) (nu_target_five_two q)
    change f ((if bp then (show BiHom 122 132 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 1 p) else 0)+
      (if bq then (show BiHom 122 132 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 2 q) else 0))=_
    rw [map_add]
    cases bp <;> cases bq <;> simp only [Bool.false_eq_true,↓reduceIte,map_zero,hp5,hq5]
  rw [←hb] at hrem
  have hnud := model.sphereDetectionCompatible.homotopy_lambda 1 4 0 nu
  change Detects (model.convergence .sphere) (1,4,4)
    (sphereLabel 1 4 0 ((KIP126.Literature.sphereFirstQuotient model) 1 4 (quotientClass 1 nu))) (lambdaMultiply 0 nu) at hnud
  have hznu : lambdaMultiply 0 nu=nu := by
    exact KIP126.Main.Internal.lambda_zero_3_4 nu
  rw [hnu,hznu] at hnud
  have hr := nu_target_remainder_zero nu hnud hprod (a0-b) hrem
  have hab : sphereAction nu a0=sphereAction nu b := by
    change _ ≫ _ ≫ (a0-b)=0 at hr
    simp only [Preadditive.comp_sub,sub_eq_zero] at hr
    exact hr
  have hvq : quotientClass 9 (lambdaMultiply 4 v)=sphereAction nu b := by
    dsimp only [v,b]
    rw [nu_target_lambda_four_product]
    simp only [sphereProduct,sphereAction,quotientClass,Category.assoc,Nat.cast_ofNat,Int.reduceSub]
  have hvn : quotientClass 9 (lambdaMultiply 4 v)≠0 := by
    rw [hvq,←hab]
    exact hne
  obtain ⟨hpb,hqb⟩ := nu_target_pq_boundaries
  obtain ⟨hpf,hqf⟩ := nu_target_sphere_products_filtration nu hnu
    P Q hpb hqb p q hp hq
  have hvf : FiltrationAtLeast model.syntheticTower 14 v := by
    cases bp <;> cases bq
    · change FiltrationAtLeast model.syntheticTower 14
        (sphereProduct (lambdaMultiply 1 nu) ((0 : BiHom 122 132 (S_0_0 : SyntheticSpectrum))+0))
      simp only [FiltrationAtLeast,add_zero,sphereProduct,comp_zero]
      exact Submodule.zero_mem _
    · simpa only [v,a,Bool.false_eq_true,↓reduceIte,zero_add] using hqf
    · simpa only [v,a,Bool.false_eq_true,↓reduceIte,add_zero] using hpf
    · have hh := (model.syntheticTower.filtrationSubmodule (S_0_0 : SyntheticSpectrum) 14 (125,135)).add_mem hpf hqf
      simpa only [FiltrationAtLeast,v,a,↓reduceIte,sphereProduct,Preadditive.comp_add,Nat.cast_ofNat,Int.natCast_one,Int.reduceSub] using hh
  have ht := KIP126.Computation.Standard.t_permanent_cycle
  have hdet := nu_target_sphere_detected T ht target_page_six_frame v hvf hvn
  obtain ⟨t,hlt,hltv⟩ := nu_target_sphere_four_split T ht v hdet
  have htn : T≠0 := by
    intro hz
    apply KIP126.Computation.Standard.t_not_h0_multiple
    refine ⟨0,?_⟩
    rw [hz]
    simp only [KIP126.Computation.Standard.product,map_zero]
  exact ⟨t,a,target_first_label_nonzero_detection T htn t hlt,hltv.symm⟩

end
end KIP126.Main.SectionSeven.Internal
