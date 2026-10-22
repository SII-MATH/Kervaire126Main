module

import all KIP126.AdamsSynthetic.Internal.SteenrodComodules
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Kernel
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Cokernel
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules.Biproduct
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-! The coimage-image criterion from the earlier graded-comodule construction,
applied to the current total modules with finite homogeneous decompositions.
The actual kernel and quotient constructions are preserved by the conservative
forgetful functor to modules. -/

namespace KIP126.AdamsSynthetic.Internal.SteenrodComodules
open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem decomposeMap_natural {M N : GradedSteenrodComodule} (f : M ⟶ N)
    (n : ℤ) (x : M.carrier) :
    letI := M.internal.chooseDecomposition
    letI := N.internal.chooseDecomposition
    (DirectSum.decompose N.grade (f.linearMap x) n).val =
      f.linearMap (DirectSum.decompose M.grade x n).val := by
  classical
  letI := M.internal.chooseDecomposition
  letI := N.internal.chooseDecomposition
  induction x using DirectSum.Decomposition.inductionOn M.grade with
  | zero => simp
  | homogeneous x =>
    rename_i i
    by_cases h : n = i
    · subst n
      rw [DirectSum.decompose_of_mem_same M.grade x.property,
        DirectSum.decompose_of_mem_same N.grade (f.graded i x x.property)]
    · rw [DirectSum.decompose_of_mem_ne M.grade x.property (Ne.symm h),
        DirectSum.decompose_of_mem_ne N.grade (f.graded i x x.property) (Ne.symm h)]
      simp
  | add x y hx hy => simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, hx, hy]

private def inverseHom {M N : GradedSteenrodComodule} (f : M ⟶ N)
    [IsIso (GradedSteenrodComodule.forget.map f)] : N ⟶ M := by
  let e := (asIso (GradedSteenrodComodule.forget.map f)).toLinearEquiv
  have he : e.toLinearMap = f.linearMap := rfl
  refine ⟨e.symm.toLinearMap, ?_, ?_⟩
  · intro n x hx
    letI := M.internal.chooseDecomposition
    letI := N.internal.chooseDecomposition
    have hn := decomposeMap_natural f n (e.symm x)
    have hx' : f.linearMap (e.symm x) = x := e.apply_symm_apply x
    rw [hx', DirectSum.decompose_of_mem_same N.grade hx] at hn
    have hi : (DirectSum.decompose M.grade (e.symm x) n).val = e.symm x :=
      e.injective (hn.symm.trans hx'.symm)
    change e.symm x ∈ M.grade n
    rw [← hi]
    exact (DirectSum.decompose M.grade (e.symm x) n).property
  · have hi := Module.Flat.lTensor_preserves_injective_linearMap f.linearMap
      e.injective (M := DualSteenrod)
    apply (LinearMap.cancel_left hi).mp
    have hf : f.linearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
      ext x
      exact e.apply_symm_apply x
    rw [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp, hf, LinearMap.lTensor_id,
      LinearMap.id_comp, ← LinearMap.comp_assoc, f.coaction, LinearMap.comp_assoc,
      hf, LinearMap.comp_id]

private instance forgetReflectsIsomorphisms :
    GradedSteenrodComodule.forget.ReflectsIsomorphisms where
  reflects f _ := by
    refine ⟨⟨inverseHom f, ?_, ?_⟩⟩
    · apply GradedSteenrodComodule.Hom.ext
      apply LinearMap.ext
      intro x
      exact (asIso (GradedSteenrodComodule.forget.map f)).toLinearEquiv.symm_apply_apply x
    · apply GradedSteenrodComodule.Hom.ext
      apply LinearMap.ext
      intro x
      exact (asIso (GradedSteenrodComodule.forget.map f)).toLinearEquiv.apply_symm_apply x

private instance comoduleHasCokernels : HasCokernels GradedSteenrodComodule :=
  CokernelConstruction.hasCokernels

private instance forgetPreservesCokernel {M N : GradedSteenrodComodule} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) GradedSteenrodComodule.forget :=
  CokernelConstruction.forget_preservesCokernel f

private instance coimageImageComparison_isIso {M N : GradedSteenrodComodule}
    (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  let F := GradedSteenrodComodule.forget
  haveI : IsIso (F.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso (Abelian.PreservesCoimageImageComparison.iso F f).hom]
    infer_instance
  exact isIso_of_reflects_iso (Abelian.coimageImageComparison f) F

@[reducible] private def comoduleAbelian : Abelian GradedSteenrodComodule :=
  Abelian.ofCoimageImageComparisonIsIso

end
end KIP126.AdamsSynthetic.Internal.SteenrodComodules
