module

public import KIP126.Def.Algebra.SimplicialModule.Kan.Data

@[expose] public section

namespace KIP126.Algebra.SimplicialModule

open CategoryTheory Simplicial Opposite

universe u
variable {R : Type u} [Ring R] (A : SimplicialObject (ModuleCat.{u} R))

/-- Pairwise agreement of the faces prescribed on a horn of dimension at least two. -/
def HornFacesCompatible {n : ℕ} (k : Fin (n + 3))
    (x : Fin (n + 3) → A.obj (op ⦋n + 1⦌)) : Prop :=
  ∀ (i j : Fin (n + 3)) (_ : i ≠ k) (_ : j ≠ k) (hij : i < j),
    (A.δ (j.pred (Fin.ne_zero_of_lt hij))).hom (x i) =
      (A.δ (i.castPred (Fin.ne_last_of_lt hij))).hom (x j)

end KIP126.Algebra.SimplicialModule
