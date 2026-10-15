module

public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Data

@[expose] public section

/-! Derived F₂ scalars preserve the represented groups and their original maps. -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The scalar action is independent of which compatible multiplication proves two-torsion. -/
theorem mod2HomologyModule_eq (R' : Mod2RingStructure H) (n : ℤ) (X : C) :
    mod2HomologyModule H R n X = mod2HomologyModule H R' n X :=
  Subsingleton.elim _ _

@[simp] theorem mod2Pi0LinearEquiv_apply (x : HomotopyGroup 0 H.HF2) :
    mod2Pi0LinearEquiv H R x = H.pi0Equiv x := rfl

@[simp] theorem cooperationCounitF2_apply (n : ℤ) (x : Mod2Cooperations H n) :
    cooperationCounitF2 H R n x = cooperationCounit H R n x := rfl

@[simp] theorem cooperationDiagonalF2_apply (n : ℤ) (x : Mod2Cooperations H n) :
    cooperationDiagonalF2 H R n x = cooperationDiagonalMap H n x := rfl

@[simp] theorem mod2HomologyF2Map_apply {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (x : Mod2Homology H n X) :
    (mod2HomologyF2Map H R f n).hom x = Mod2Homology.pushforward H f n x := rfl

end KIP126.StableHomotopy.Cohomology
