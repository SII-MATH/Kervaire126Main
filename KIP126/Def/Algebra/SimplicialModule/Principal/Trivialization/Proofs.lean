module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Trivialization.Data

@[expose] public section

namespace KIP126.Algebra.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped MonoidalCategory
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

@[reassoc (attr := simp)] theorem principalSimplexIso_hom_fst
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : SimplexCategory} (b : B.obj (op n)) (z : A.obj (op n))
    (hz : (p.app (op n)).hom z = b) :
    (principalSimplexIso p b z hz).hom ≫ pullback.fst _ _ = principalSimplexMap p z :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)] theorem principalSimplexIso_hom_snd
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : SimplexCategory} (b : B.obj (op n)) (z : A.obj (op n))
    (hz : (p.app (op n)).hom z = b) :
    (principalSimplexIso p b z hz).hom ≫ pullback.snd _ _ = CartesianMonoidalCategory.snd _ _ :=
  IsPullback.isoPullback_hom_snd _

@[reassoc (attr := simp)] theorem principalSimplexIso_inv_fst
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : SimplexCategory} (b : B.obj (op n)) (z : A.obj (op n))
    (hz : (p.app (op n)).hom z = b) :
    (principalSimplexIso p b z hz).inv ≫ principalSimplexMap p z = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

@[reassoc (attr := simp)] theorem principalSimplexIso_inv_snd
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : SimplexCategory} (b : B.obj (op n)) (z : A.obj (op n))
    (hz : (p.app (op n)).hom z = b) :
    (principalSimplexIso p b z hz).inv ≫ CartesianMonoidalCategory.snd _ _ = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

/-- The inverse kernel coordinate is the actual residual from the lifted simplex. -/
theorem principalSimplexIso_inv_kernel
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : SimplexCategory} (b : B.obj (op n)) (z : A.obj (op n))
    (hz : (p.app (op n)).hom z = b) (a : SimplexCategoryᵒᵖ)
    (x : (pullback (Functor.whiskerRight p (forget (ModuleCat R)))
      ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b)).obj a) :
    ((kernel.ι p).app a).hom (((principalSimplexIso p b z hz).inv.app a x).1) =
      (show A.obj a from (pullback.fst (Functor.whiskerRight p (forget (ModuleCat R)))
        ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b)).app a x) -
        (A.map (SSet.stdSimplex.objEquiv (((principalSimplexIso p b z hz).inv.app a x).2)).op).hom z := by
  apply (eq_sub_iff_add_eq).mpr
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (principalSimplexIso_inv_fst p b z hz) a) x

/-- Every target simplex of a degreewise surjection has an actual kernel-product trivialization. -/
theorem principalSimplexIso_exists_of_degreewise_surjective
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    (hp : ∀ n : ℕ, Function.Surjective (p.app (op ⦋n⦌)).hom)
    (n : ℕ) (b : B.obj (op ⦋n⦌)) :
    ∃ z : A.obj (op ⦋n⦌), ∃ hz : (p.app (op ⦋n⦌)).hom z = b,
      (principalSimplexIso p b z hz).hom ≫ pullback.snd _ _ = CartesianMonoidalCategory.snd _ _ := by
  obtain ⟨z,hz⟩ := hp n b
  exact ⟨z,hz,principalSimplexIso_hom_snd p b z hz⟩


end KIP126.Algebra.SimplicialModule
