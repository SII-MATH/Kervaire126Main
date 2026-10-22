module

import all KIP126.AdamsSynthetic.Internal.SteenrodComodules
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Kernels for the fixed total graded left-comodule category. The finite homogeneous
decomposition gives a graded linear retraction onto the kernel. Tensor exactness
then identifies the restricted coaction with the original one. -/

namespace KIP126.AdamsSynthetic.Internal.SteenrodComodules
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private def kernelGrade {M N : GradedSteenrodComodule} (f : M ⟶ N) (n : ℤ) :
    Submodule F2 f.linearMap.ker := (M.grade n).comap f.linearMap.ker.subtype

private theorem kernel_component {M N : GradedSteenrodComodule} (f : M ⟶ N)
    (n : ℤ) (x : f.linearMap.ker) :
    letI := M.internal.chooseDecomposition
    (DirectSum.decompose M.grade x n).val ∈ f.linearMap.ker := by
  classical
  letI := M.internal.chooseDecomposition
  letI := N.internal.chooseDecomposition
  have hn (y : M.carrier) :
      (DirectSum.decompose N.grade (f.linearMap y) n).val =
        f.linearMap (DirectSum.decompose M.grade y n).val := by
    induction y using DirectSum.Decomposition.inductionOn M.grade with
    | zero => simp
    | homogeneous y =>
      rename_i i
      by_cases h : n = i
      · subst n
        rw [DirectSum.decompose_of_mem_same M.grade y.property,
          DirectSum.decompose_of_mem_same N.grade (f.graded i y y.property)]
      · rw [DirectSum.decompose_of_mem_ne M.grade y.property (Ne.symm h),
          DirectSum.decompose_of_mem_ne N.grade (f.graded i y y.property) (Ne.symm h)]
        simp
    | add x y hx hy => simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
        Submodule.coe_add, hx, hy]
  change f.linearMap (DirectSum.decompose M.grade x n).val = 0
  rw [← hn, x.property]
  simp

private theorem kernel_internal {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    DirectSum.IsInternal (kernelGrade f) := by
  classical
  letI := M.internal.chooseDecomposition
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · let e := f.linearMap.ker.mapIic
    apply (iSupIndep_map_orderIso_iff e).mp
    apply iSupIndep.of_coe_Iic_comp
    change iSupIndep (fun n => ((M.grade n).comap f.linearMap.ker.subtype).map
      f.linearMap.ker.subtype)
    simp only [Submodule.map_comap_subtype]
    exact M.internal.submodule_iSupIndep.mono (fun n => inf_le_right)
  · apply top_unique
    intro x hx
    have hxsum : (∑ n ∈ (DirectSum.decompose M.grade x.val).support,
        (⟨(DirectSum.decompose M.grade x.val n).val,
          kernel_component f n x⟩ : f.linearMap.ker)) = x := by
      apply Subtype.ext
      simpa using DirectSum.sum_support_decompose M.grade x.val
    rw [← hxsum]
    apply Submodule.sum_mem
    intro n hn
    exact Submodule.mem_iSup_of_mem n (show
      (⟨(DirectSum.decompose M.grade x.val n).val, kernel_component f n x⟩ :
        f.linearMap.ker) ∈ kernelGrade f n from
      (DirectSum.decompose M.grade x.val n).property)

private def kernelGradeInclusion {M N : GradedSteenrodComodule} (f : M ⟶ N) (n : ℤ) :
    kernelGrade f n →ₗ[F2] M.grade n :=
  (f.linearMap.ker.subtype.comp (kernelGrade f n).subtype).codRestrict (M.grade n)
    (fun x => x.property)

private theorem kernelGradeInclusion_injective {M N : GradedSteenrodComodule}
    (f : M ⟶ N) (n : ℤ) : Function.Injective (kernelGradeInclusion f n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : M.grade n => z.val) h

private def kernelRetraction {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    M.carrier →ₗ[F2] f.linearMap.ker :=
  letI := M.internal.chooseDecomposition
  (DirectSum.toModule F2 ℤ f.linearMap.ker (fun n =>
    (kernelGrade f n).subtype ∘ₗ (LinearMap.leftInverse (K := F2) (kernelGradeInclusion f n)))) ∘ₗ
      (DirectSum.decomposeLinearEquiv M.grade).toLinearMap

private theorem kernelRetraction_homogeneous {M N : GradedSteenrodComodule}
    (f : M ⟶ N) (n : ℤ) (x : M.grade n) :
    kernelRetraction f x = (kernelGrade f n).subtype
      ((LinearMap.leftInverse (K := F2) (kernelGradeInclusion f n)) x) := by
  classical
  letI := M.internal.chooseDecomposition
  simp [kernelRetraction, DirectSum.decomposeLinearEquiv_apply_coe]

private theorem kernelRetraction_graded {M N : GradedSteenrodComodule}
    (f : M ⟶ N) (n : ℤ) (x : M.carrier) (hx : x ∈ M.grade n) :
    kernelRetraction f x ∈ kernelGrade f n := by
  rw [kernelRetraction_homogeneous f n ⟨x,hx⟩]
  exact ((LinearMap.leftInverse (K := F2) (kernelGradeInclusion f n)) ⟨x,hx⟩).property

private theorem kernelRetraction_comp {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    kernelRetraction f ∘ₗ f.linearMap.ker.subtype = LinearMap.id := by
  classical
  letI := (kernel_internal f).chooseDecomposition
  apply DirectSum.decompose_lhom_ext (kernelGrade f)
  intro n
  apply LinearMap.ext
  intro x
  change kernelRetraction f (kernelGradeInclusion f n x).val = x.val
  rw [kernelRetraction_homogeneous f n (kernelGradeInclusion f n x)]
  rw [LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (kernelGradeInclusion_injective f n))]
  rfl

private theorem tensorGrade_map {V W : ModuleCat.{0} F2}
    (gv : ℤ → Submodule F2 V) (gw : ℤ → Submodule F2 W)
    (l : V →ₗ[F2] W) (hl : ∀ n x, x ∈ gv n → l x ∈ gw n)
    (n : ℤ) (x : DualSteenrod ⊗[F2] V) (hx : x ∈ tensorGrade V gv n) :
    l.lTensor DualSteenrod x ∈ tensorGrade W gw n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d,a,m,ha,hm,rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨d,a,l m,ha,hl (n-d) m hm,rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (tensorGrade W gw n).add_mem ihx ihy
  | smul c x hx ih => simpa using (tensorGrade W gw n).smul_mem c ih

private def kernelRho {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    f.linearMap.ker →ₗ[F2] DualSteenrod ⊗[F2] f.linearMap.ker :=
  (kernelRetraction f).lTensor DualSteenrod ∘ₗ M.rho ∘ₗ f.linearMap.ker.subtype

private theorem kernelRho_subtype {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    f.linearMap.ker.subtype.lTensor DualSteenrod ∘ₗ kernelRho f =
      M.rho ∘ₗ f.linearMap.ker.subtype := by
  ext x
  have hz : f.linearMap.lTensor DualSteenrod (M.rho x.val) = 0 := by
    have h := LinearMap.congr_fun f.coaction x.val
    simpa using h
  have hr : M.rho x.val ∈ LinearMap.range
      (f.linearMap.ker.subtype.lTensor DualSteenrod) := by
    have he := (Module.Flat.lTensor_exact DualSteenrod
      (LinearMap.exact_subtype_ker_map f.linearMap)).linearMap_ker_eq
    change M.rho x.val ∈ LinearMap.ker (f.linearMap.lTensor DualSteenrod) at hz
    rw [he] at hz
    exact hz
  obtain ⟨y,hy⟩ := hr
  change f.linearMap.ker.subtype.lTensor DualSteenrod
    ((kernelRetraction f).lTensor DualSteenrod (M.rho x.val)) = M.rho x.val
  rw [← hy]
  have hret := congrArg (fun l => l.lTensor DualSteenrod) (kernelRetraction_comp f)
  rw [LinearMap.lTensor_comp, LinearMap.lTensor_id] at hret
  exact congrArg (f.linearMap.ker.subtype.lTensor DualSteenrod)
    (LinearMap.congr_fun hret y)

private def counitMap (V : Type*) [AddCommGroup V] [Module F2 V] :
    DualSteenrod ⊗[F2] V →ₗ[F2] V :=
  (TensorProduct.lid F2 V).toLinearMap ∘ₗ milnorCounit.toLinearMap.rTensor V

private theorem counitMap_natural {V W : Type*} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W] (l : V →ₗ[F2] W) :
    l ∘ₗ counitMap V = counitMap W ∘ₗ l.lTensor DualSteenrod := by
  apply TensorProduct.ext'
  intro a x
  simp [counitMap]

private def deltaMap (V : Type*) [AddCommGroup V] [Module F2 V] :
    DualSteenrod ⊗[F2] V →ₗ[F2] DualSteenrod ⊗[F2] (DualSteenrod ⊗[F2] V) :=
  (TensorProduct.assoc F2 DualSteenrod DualSteenrod V).toLinearMap ∘ₗ
    milnorCoproduct.toLinearMap.rTensor V

private theorem deltaMap_natural {V W : Type*} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W] (l : V →ₗ[F2] W) :
    (l.lTensor DualSteenrod).lTensor DualSteenrod ∘ₗ deltaMap V =
      deltaMap W ∘ₗ l.lTensor DualSteenrod := by
  apply TensorProduct.ext'
  intro a x
  change (l.lTensor DualSteenrod).lTensor DualSteenrod
    ((TensorProduct.assoc F2 DualSteenrod DualSteenrod V)
      (milnorCoproduct a ⊗ₜ[F2] x)) =
    (TensorProduct.assoc F2 DualSteenrod DualSteenrod W)
      (milnorCoproduct a ⊗ₜ[F2] l x)
  generalize milnorCoproduct a = d
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add d e hd he => simp [TensorProduct.add_tmul, hd, he]

private theorem kernelRho_counit {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    counitMap f.linearMap.ker ∘ₗ kernelRho f = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply f.linearMap.ker.injective_subtype
  have hnat := LinearMap.congr_fun (counitMap_natural f.linearMap.ker.subtype)
    (kernelRho f x)
  change f.linearMap.ker.subtype (counitMap f.linearMap.ker (kernelRho f x)) = x.val
  change (f.linearMap.ker.subtype ∘ₗ counitMap f.linearMap.ker) (kernelRho f x) = x.val
  rw [hnat]
  change counitMap M.carrier
    ((f.linearMap.ker.subtype.lTensor DualSteenrod ∘ₗ kernelRho f) x) = x.val
  rw [kernelRho_subtype]
  exact LinearMap.congr_fun M.counit x.val

private theorem kernelRho_coassoc {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    deltaMap f.linearMap.ker ∘ₗ kernelRho f =
      (kernelRho f).lTensor DualSteenrod ∘ₗ kernelRho f := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    f.linearMap.ker.subtype f.linearMap.ker.injective_subtype (M := DualSteenrod)
  have hii := Module.Flat.lTensor_preserves_injective_linearMap
    (f.linearMap.ker.subtype.lTensor DualSteenrod) hi (M := DualSteenrod)
  apply (LinearMap.cancel_left hii).mp
  calc
    _ = deltaMap M.carrier ∘ₗ M.rho ∘ₗ f.linearMap.ker.subtype := by
      rw [← LinearMap.comp_assoc, deltaMap_natural, LinearMap.comp_assoc,
        kernelRho_subtype, ← LinearMap.comp_assoc]
    _ = M.rho.lTensor DualSteenrod ∘ₗ M.rho ∘ₗ f.linearMap.ker.subtype := by
      simpa only [deltaMap, LinearMap.comp_assoc] using congrArg
        (fun l => l ∘ₗ f.linearMap.ker.subtype) M.coassoc
    _ = _ := by
      have hc : (f.linearMap.ker.subtype.lTensor DualSteenrod).lTensor DualSteenrod ∘ₗ
          (kernelRho f).lTensor DualSteenrod =
          M.rho.lTensor DualSteenrod ∘ₗ f.linearMap.ker.subtype.lTensor DualSteenrod := by
        rw [← LinearMap.lTensor_comp, kernelRho_subtype, LinearMap.lTensor_comp]
      calc
        _ = M.rho.lTensor DualSteenrod ∘ₗ
            (f.linearMap.ker.subtype.lTensor DualSteenrod ∘ₗ kernelRho f) := by
          rw [kernelRho_subtype]
        _ = (M.rho.lTensor DualSteenrod ∘ₗ
            f.linearMap.ker.subtype.lTensor DualSteenrod) ∘ₗ kernelRho f :=
          (LinearMap.comp_assoc ..).symm
        _ = _ := by rw [← hc, LinearMap.comp_assoc]

private def kernelObject {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    GradedSteenrodComodule where
  carrier := ModuleCat.of F2 f.linearMap.ker
  grade := kernelGrade f
  internal := kernel_internal f
  rho := kernelRho f
  counit := kernelRho_counit f
  coassoc := kernelRho_coassoc f
  graded n x hx := tensorGrade_map (V := M.carrier)
    (W := ModuleCat.of F2 f.linearMap.ker) M.grade (kernelGrade f) (kernelRetraction f)
    (kernelRetraction_graded f) n (M.rho x.val) (M.graded n x.val hx)

private def kernelInclusion {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    kernelObject f ⟶ M where
  linearMap := f.linearMap.ker.subtype
  graded _ _ hx := hx
  coaction := kernelRho_subtype f

private theorem kernelInclusion_condition {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    kernelInclusion f ≫ f = 0 := by
  apply GradedSteenrodComodule.Hom.ext
  apply LinearMap.ext
  intro x
  exact x.property

private def kernelLift {M N P : GradedSteenrodComodule} (f : M ⟶ N)
    (k : P ⟶ M) (hk : k ≫ f = 0) : P ⟶ kernelObject f := by
  have hz : f.linearMap ∘ₗ k.linearMap = 0 :=
    congrArg GradedSteenrodComodule.Hom.linearMap hk
  let l := k.linearMap.codRestrict f.linearMap.ker (fun x => LinearMap.congr_fun hz x)
  have hl : f.linearMap.ker.subtype ∘ₗ l = k.linearMap := rfl
  refine ⟨l, (fun n x hx => k.graded n x hx), ?_⟩
  have hi := Module.Flat.lTensor_preserves_injective_linearMap
    f.linearMap.ker.subtype f.linearMap.ker.injective_subtype (M := DualSteenrod)
  apply (LinearMap.cancel_left hi).mp
  change f.linearMap.ker.subtype.lTensor DualSteenrod ∘ₗ
    (l.lTensor DualSteenrod ∘ₗ P.rho) =
    f.linearMap.ker.subtype.lTensor DualSteenrod ∘ₗ (kernelRho f ∘ₗ l)
  rw [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp, hl, k.coaction,
    ← LinearMap.comp_assoc, kernelRho_subtype, LinearMap.comp_assoc, hl]

private theorem kernelLift_fac {M N P : GradedSteenrodComodule} (f : M ⟶ N)
    (k : P ⟶ M) (hk : k ≫ f = 0) : kernelLift f k hk ≫ kernelInclusion f = k := by
  apply GradedSteenrodComodule.Hom.ext
  rfl

private def kernelLimit {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    IsLimit (KernelFork.ofι (kernelInclusion f) (kernelInclusion_condition f)) :=
  KernelFork.IsLimit.ofι (kernelInclusion f) (kernelInclusion_condition f)
    (fun k hk => kernelLift f k hk) (fun k hk => kernelLift_fac f k hk) (by
      intro P k hk m hm
      apply GradedSteenrodComodule.Hom.ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun l : P ⟶ M => l.linearMap x) hm)

private instance comoduleHasKernels : HasKernels GradedSteenrodComodule where
  has_limit f := ⟨⟨_, kernelLimit f⟩⟩

private instance forgetPreservesKernel {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) GradedSteenrodComodule.forget := by
  apply preservesLimit_of_preserves_limit_cone (kernelLimit f)
  exact (isLimitMapConeForkEquiv' GradedSteenrodComodule.forget
    (kernelInclusion_condition f)).symm
    (ModuleCat.kernelIsLimit (GradedSteenrodComodule.forget.map f))

end
end KIP126.AdamsSynthetic.Internal.SteenrodComodules
