module

public import KIP126.Def.Synthetic.Sphere.Homotopy.Data

@[expose] public section

namespace KIP126.Synthetic.Context
open CategoryTheory
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- A sphere class acts on an actual homotopy group by composition.
In particular no new multiplication is chosen on a truncated sphere. -/
def sphereAction {m n k l : ℤ} {X : Syn}
    (x : BiHom m n (S_0_0 : Syn)) (y : BiHom k l X) : BiHom (m + k) (n + l) X :=
  (SyntheticCategory.biShift_comp (m, n) (k, l)).inv.app S_0_0 ≫
    (SyntheticCategory.biShift (k, l)).map x ≫ y

/-- Iterated λ action, with its change of weight visible in the result type. -/
def lambdaMultiply {m w : ℤ} {X : Syn} (k : ℕ)
    (x : BiHom m w X) : BiHom m (w - k) X :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m, w) (0, -(k : ℤ))).inv.app S_0_0 ≫
      lambdaPow k (Smn m w) ≫ x

/-- Explicit regrading along two proved integer equalities. -/
def homotopyRegrade {m m' w w' : ℤ} {X : Syn} (hm : m = m') (hw : w = w')
    (x : BiHom m w X) : BiHom m' w' X := by
  subst m'
  subst w'
  exact x
end
end KIP126.Synthetic.Context
