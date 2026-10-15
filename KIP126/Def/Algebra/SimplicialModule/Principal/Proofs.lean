module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Data
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

namespace KIP126.Algebra.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped MonoidalCategory
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

theorem principalSimplexMap_comp {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) {n : SimplexCategory} (z : A.obj (op n)) :
    principalSimplexMap p z ≫ Functor.whiskerRight p (forget (ModuleCat R)) =
      CartesianMonoidalCategory.snd _ _ ≫ (SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm ((p.app (op n)).hom z) := by
  ext a x
  change (p.app a).hom (((kernel.ι p).app a).hom x.1 +
      (A.map (SSet.stdSimplex.objEquiv x.2).op).hom z) =
    ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm ((p.app (op n)).hom z)).app a x.2
  have hk := ConcreteCategory.congr_hom (NatTrans.congr_app (kernel.condition p) a) x.1
  change (p.app a).hom (((kernel.ι p).app a).hom x.1) = 0 at hk
  rw [map_add,hk,zero_add]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (SSet.yonedaEquiv_symm_comp z (Functor.whiskerRight p (forget (ModuleCat R)))) a) x.2

theorem principalSimplex_isPullback {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) {n : SimplexCategory} (z : A.obj (op n)) :
    IsPullback (principalSimplexMap p z) (CartesianMonoidalCategory.snd _ _)
      (Functor.whiskerRight p (forget (ModuleCat R)))
      ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm ((p.app (op n)).hom z)) := by
  apply IsPullback.of_forall_isPullback_app
  intro a
  apply (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (principalSimplexMap_comp p z) a, ?_, ?_⟩
  · rintro ⟨k,θ⟩ ⟨l,φ⟩ ⟨h₁,h₂⟩
    change θ = φ at h₂
    subst φ
    change ((kernel.ι p).app a).hom k + _ = ((kernel.ι p).app a).hom l + _ at h₁
    have hkl := kernel_inclusion_injective p a (add_right_cancel h₁)
    subst l
    rfl
  · intro x θ hx
    change A.obj a at x
    let s : A.obj a := (A.map (SSet.stdSimplex.objEquiv θ).op).hom z
    have hs : (p.app a).hom s =
        ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm ((p.app (op n)).hom z)).app a θ :=
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (SSet.yonedaEquiv_symm_comp z (Functor.whiskerRight p (forget (ModuleCat R)))) a) θ
    have hr : (p.app a).hom (x-s) = 0 := by
      rw [map_sub,hs]
      exact sub_eq_zero.mpr hx
    obtain ⟨k,hk⟩ := kernel_exists_element p a (x-s) hr
    refine ⟨(k,θ),?_,rfl⟩
    change ((kernel.ι p).app a).hom k + s = x
    rw [hk,sub_add_cancel]


@[simp] theorem principalSimplexMap_app {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) {n : SimplexCategory} (z : A.obj (op n)) (a : SimplexCategoryᵒᵖ)
    (k : (kernel p).obj a) (θ : (SSet.stdSimplex.obj n).obj a) :
    (principalSimplexMap p z).app a (k,θ) =
      ((kernel.ι p).app a).hom k + (A.map (SSet.stdSimplex.objEquiv θ).op).hom z := rfl

@[simp] theorem principalSimplexMap_app_zero_kernel {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) {n : SimplexCategory} (z : A.obj (op n)) (a : SimplexCategoryᵒᵖ)
    (θ : (SSet.stdSimplex.obj n).obj a) :
    (principalSimplexMap p z).app a (0,θ) =
      (A.map (SSet.stdSimplex.objEquiv θ).op).hom z := by
  rw [principalSimplexMap_app,map_zero,zero_add]

@[simp] theorem principalSimplexMap_app_zero_lift {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) {n : SimplexCategory} (a : SimplexCategoryᵒᵖ)
    (k : (kernel p).obj a) (θ : (SSet.stdSimplex.obj n).obj a) :
    (principalSimplexMap p (0 : A.obj (op n))).app a (k,θ) = ((kernel.ι p).app a).hom k := by
  rw [principalSimplexMap_app,map_zero,add_zero]

/-- Restricting the chosen lift along a simplex operator restricts the
trivialization along exactly the same operator. -/
theorem principalSimplexMap_natural_simplex {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) {m n : SimplexCategory} (φ : m ⟶ n) (z : A.obj (op n)) :
    (𝟙 (kernel p ⋙ forget (ModuleCat R)) ⊗ₘ SSet.stdSimplex.map φ) ≫ principalSimplexMap p z =
      principalSimplexMap p ((A.map φ.op).hom z) := by
  ext a x
  change ((kernel.ι p).app a).hom x.1 +
      (A.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map φ).app a x.2)).op).hom z =
    ((kernel.ι p).app a).hom x.1 +
      (A.map (SSet.stdSimplex.objEquiv x.2).op).hom ((A.map φ.op).hom z)
  congr 1
  change (A.map ((SSet.stdSimplex.objEquiv x.2) ≫ φ).op).hom z = _
  rw [op_comp,A.map_comp]
  rfl

end KIP126.Algebra.SimplicialModule
