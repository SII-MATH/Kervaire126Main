module

public import KIP126.Def.Algebra.SimplicialModule.Kernel.Proofs
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

@[expose] public section

namespace KIP126.Algebra.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped MonoidalCategory
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

/-- Translation by the simplex determined by a chosen lift, with the kernel
as its free coordinate. -/
noncomputable def principalSimplexMap {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : SimplexCategory} (z : A.obj (op n)) :
    ((kernel p ⋙ forget (ModuleCat R)) ⊗ SSet.stdSimplex.obj n) ⟶
      A ⋙ forget (ModuleCat R) where
  app a := TypeCat.ofHom (fun x => ((kernel.ι p).app a).hom x.1 +
    (A.map (SSet.stdSimplex.objEquiv x.2).op).hom z)
  naturality := by
    intro a b θ
    ext x
    change ((kernel.ι p).app b).hom ((kernel p).map θ |>.hom x.1) +
        (A.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj n).map θ x.2)).op).hom z =
      (A.map θ).hom (((kernel.ι p).app a).hom x.1 + (A.map (SSet.stdSimplex.objEquiv x.2).op).hom z)
    rw [map_add]
    congr 1
    · exact ConcreteCategory.congr_hom ((kernel.ι p).naturality θ) x.1
    · exact ConcreteCategory.congr_hom (((SSet.yonedaEquiv (X := A ⋙ forget (ModuleCat R))).symm z).naturality θ) x.2


end KIP126.Algebra.SimplicialModule
