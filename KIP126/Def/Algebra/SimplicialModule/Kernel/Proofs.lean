module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

@[expose] public section

namespace KIP126.Algebra.SimplicialModule

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u
variable {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false

/-- The categorical simplicial kernel has exactly the expected elements
in every degree, via the actual evaluation and module kernel comparisons. -/
theorem kernel_exists_element {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) (a : SimplexCategoryᵒᵖ) (x : A.obj a) (hx : (p.app a).hom x = 0) :
    ∃ y : (kernel p).obj a, ((kernel.ι p).app a).hom y = x := by
  let E := (evaluation SimplexCategoryᵒᵖ (ModuleCat R)).obj a
  let g := (ModuleCat.kernelIsoKer (p.app a)).inv ≫ (PreservesKernel.iso E p).inv
  have hg : g ≫ (kernel.ι p).app a = ModuleCat.ofHom (p.app a).hom.ker.subtype := by
    dsimp only [g]
    rw [Category.assoc]
    change (ModuleCat.kernelIsoKer (p.app a)).inv ≫
      ((PreservesKernel.iso E p).inv ≫ E.map (kernel.ι p)) = _
    rw [PreservesKernel.iso_inv_ι]
    exact ModuleCat.kernelIsoKer_inv_kernel_ι (f := p.app a)
  refine ⟨g.hom ⟨x,hx⟩, ?_⟩
  exact ConcreteCategory.congr_hom hg (⟨x,hx⟩ : (p.app a).hom.ker)

/-- The simplicial kernel inclusion is injective in each degree. -/
theorem kernel_inclusion_injective {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) (a : SimplexCategoryᵒᵖ) :
    Function.Injective ((kernel.ι p).app a).hom := by
  haveI : Mono (kernel.ι p) := inferInstance
  exact (ModuleCat.mono_iff_injective ((kernel.ι p).app a)).mp inferInstance

end KIP126.Algebra.SimplicialModule
