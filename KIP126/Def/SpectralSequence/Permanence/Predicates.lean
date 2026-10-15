module

public import KIP126.Def.SpectralSequence.Basic.Data
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

namespace KIP126.SpectralSequence

open CategoryTheory

universe u v

/-- A specified page class has a common Z∞ representative whose E∞ image is
nonzero. This is internal SSData reasoning, with no Mathlib SS dependency. -/
def NonzeroSurvival {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat R),
    (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) z = x ∧
      D.pageπ ⊤ z ≠ 0

end KIP126.SpectralSequence
