module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Proofs

@[expose] public section

namespace KIP126.Algebra.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped MonoidalCategory
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

noncomputable def principalSimplexIso {A B : SimplicialObject (ModuleCat.{u} R)}
    (p : A ⟶ B) {n : SimplexCategory} (b : B.obj (op n))
    (z : A.obj (op n)) (hz : (p.app (op n)).hom z = b) :
    ((kernel p ⋙ forget (ModuleCat R)) ⊗ SSet.stdSimplex.obj n) ≅
      pullback (Functor.whiskerRight p (forget (ModuleCat R)))
        ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) :=
  (show IsPullback (principalSimplexMap p z) (CartesianMonoidalCategory.snd _ _)
    (Functor.whiskerRight p (forget (ModuleCat R)))
    ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) by
      rw [← hz]
      exact principalSimplex_isPullback p z).isoPullback

end KIP126.Algebra.SimplicialModule
