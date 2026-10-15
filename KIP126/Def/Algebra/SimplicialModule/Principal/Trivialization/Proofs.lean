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

end KIP126.Algebra.SimplicialModule
