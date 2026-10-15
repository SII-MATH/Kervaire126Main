module

public import KIP126.Def.Algebra.GradedVectorSpace.Data
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.CategoryTheory.Preadditive.LeftExact

@[expose] public section

/-! Properties of the actual Cauchy tensor functor over a field. Its finite
limit preservation uses flatness of vector spaces and exactness of direct
sums. These are proof obligations on the fixed functor, not extra data. -/

namespace KIP126.Algebra.GradedVectorSpace

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u
variable {K : Type u} [Field K]

theorem tensorRight_additive (X : GrVect K) : (tensorRight X).Additive := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    intro Y Z f g
    funext n
    apply GradedObject.Monoidal.tensorObj_ext
    intro i j h
    change GradedObject.Monoidal.ιTensorObj Y X i j n h ≫
      GradedObject.Monoidal.tensorHom (f + g) (𝟙 X) n = _
    rw [GradedObject.Monoidal.ι_tensorHom]
    change ((f i + g i) ⊗ₘ 𝟙 (X j)) ≫ _ =
      _ ≫ (GradedObject.Monoidal.tensorHom f (𝟙 X) n + GradedObject.Monoidal.tensorHom g (𝟙 X) n)
    simp only [MonoidalPreadditive.add_tensor, Preadditive.add_comp, Preadditive.comp_add]
    rw [GradedObject.Monoidal.ι_tensorHom, GradedObject.Monoidal.ι_tensorHom]
    rfl

attribute [instance] tensorRight_additive

theorem tensorRight_linear (X : GrVect K) : Functor.Linear K (tensorRight X) := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    intro Y Z f r
    funext n
    apply GradedObject.Monoidal.tensorObj_ext
    intro i j h
    change GradedObject.Monoidal.ιTensorObj Y X i j n h ≫
      GradedObject.Monoidal.tensorHom (r • f) (𝟙 X) n = _
    rw [GradedObject.Monoidal.ι_tensorHom]
    change ((r • f i) ⊗ₘ 𝟙 (X j)) ≫ _ =
      _ ≫ (r • GradedObject.Monoidal.tensorHom f (𝟙 X) n)
    simp only [tensorHom_id, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]
    rw [GradedObject.Monoidal.ι_tensorHom]
    rfl

attribute [instance] tensorRight_linear

/-- Degreewise Cauchy tensoring over a field preserves finite limits. -/
theorem tensorRight_preservesFiniteLimits (X : GrVect K) :
    PreservesFiniteLimits (tensorRight X) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    have generalizedInverse {X Y : GrVect K} (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
      classical
      have hg (n : ℤ) : ∃ g : Y n ⟶ X n, f n ≫ g ≫ f n = f n := by
        obtain ⟨s, hs⟩ := (f n).hom.rangeRestrict.exists_rightInverse_of_surjective
          (f n).hom.range_rangeRestrict
        obtain ⟨r, hr⟩ := (LinearMap.range (f n).hom).subtype.exists_leftInverse_of_injective
          (Submodule.ker_subtype _)
        refine ⟨ModuleCat.ofHom (s.comp r), ?_⟩
        apply ModuleCat.hom_ext
        ext x
        have h₁ := LinearMap.congr_fun hr ((f n).hom.rangeRestrict x)
        have h₂ := congrArg Subtype.val (LinearMap.congr_fun hs ((f n).hom.rangeRestrict x))
        change (f n).hom (s (r ((f n).hom x))) = (f n).hom x
        rw [show r ((f n).hom x) = (f n).hom.rangeRestrict x from h₁]
        exact h₂
      choose g hg using hg
      exact ⟨g, funext hg⟩

    let F := tensorRight X
    haveI (Y Z : GrVect K) (f : Y ⟶ Z) : PreservesLimit (parallelPair f 0) F := by
      obtain ⟨g, hg⟩ := generalizedInverse f
      have hp : (𝟙 Y - f ≫ g) ≫ f = 0 := by
        simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, hg, sub_self]
      let r := kernel.lift f (𝟙 Y - f ≫ g) hp
      have hri : r ≫ kernel.ι f = 𝟙 Y - f ≫ g := kernel.lift_ι _ _ _
      have hir : kernel.ι f ≫ r = 𝟙 (kernel f) := by
        apply (cancel_mono (kernel.ι f)).1
        simp only [Category.assoc, hri, Preadditive.comp_sub, Category.comp_id,
          kernel.condition_assoc, zero_comp, sub_zero, Category.id_comp]
      apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
      refine (isLimitMapConeForkEquiv' F (kernel.condition f)).symm ?_
      refine KernelFork.IsLimit.ofι _ _ (fun h _ => h ≫ F.map r) ?_ ?_
      · intro W h hh
        rw [Category.assoc, ← F.map_comp, hri, F.map_sub, F.map_id,
          F.map_comp, Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
          hh, zero_comp, sub_zero]
      · intro W h hh m hm
        rw [← hm, Category.assoc, ← F.map_comp, hir, F.map_id, Category.comp_id]
    exact Functor.preservesFiniteLimits_of_preservesKernels F

attribute [instance] tensorRight_preservesFiniteLimits

end KIP126.Algebra.GradedVectorSpace
