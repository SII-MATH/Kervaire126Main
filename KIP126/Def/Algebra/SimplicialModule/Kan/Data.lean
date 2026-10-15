module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

@[expose] public section

namespace KIP126.Algebra.SimplicialModule

open CategoryTheory Simplicial Opposite

universe u
variable {R : Type u} [Ring R] (A : SimplicialObject (ModuleCat.{u} R))

/-- Correct one face using the degeneracy immediately following that face. -/
def lowerCorrection {n : ℕ} (j : Fin (n + 1))
    (x : A.obj (op ⦋n⦌)) (y : A.obj (op ⦋n + 1⦌)) : A.obj (op ⦋n + 1⦌) :=
  y + (A.σ j).hom (x - (A.δ j.castSucc).hom y)

/-- Correct one face using the degeneracy immediately preceding that face. -/
def upperCorrection {n : ℕ} (j : Fin (n + 1))
    (x : A.obj (op ⦋n⦌)) (y : A.obj (op ⦋n + 1⦌)) : A.obj (op ⦋n + 1⦌) :=
  y + (A.σ j).hom (x - (A.δ j.succ).hom y)

end KIP126.Algebra.SimplicialModule
