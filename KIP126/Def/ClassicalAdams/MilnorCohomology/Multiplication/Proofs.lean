module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Data

@[expose] public section


/-! Representative formulas for the descended cobar cohomology product. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

@[simp] theorem cup_classOf {s t s' t' : ℕ} (x : cycles s t) (y : cycles s' t') :
    cup H M (classOf H M s t x) (classOf H M s' t' y) =
      classOf H M (s + s') (t + t') (cycleCup s t s' t' x y) := rfl

/-- Multiplication of specified cocycle classes uses precisely their cobar
concatenation, with no independent choice of a representative. -/
theorem cup_ofCocycle {s t s' t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : IsCycle x) (hy : IsCycle y) :
    cup H M (ofCocycle H M x hx) (ofCocycle H M y hy) =
      ofCocycle H M (KIP126.Steenrod.Milnor.cup x y) (cup_isCycle x y hx hy) := rfl

theorem cohomologyReindex_ofCocycle {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
    (x : cochains s t) (hx : IsCycle x) :
    cohomologyReindex H M hs ht (ofCocycle H M x hx) =
      ofCocycle H M (reindex hs ht x) (reindex_isCycle hs ht x hx) := by
  subst s'
  subst t'
  rfl

/-- Reindexing changes only the type index, not the represented class. -/
theorem cohomologyReindex_heq {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
    (x : Cohomology H M s t) : HEq (cohomologyReindex H M hs ht x) x := by
  subst s'
  subst t'
  rfl

/-- The specified hᵢ² class is the actual cup square, transported from
`2^i + 2^i` to its named internal degree `2^(i+1)`. -/
theorem hiSquare_eq_cup (i : ℕ) :
    hiSquare H M i =
      cohomologyReindex H M rfl (hiSquare_internalDegree i)
        (cup H M (hi H M i) (hi H M i)) := by
  rw [hi, cup_ofCocycle, cohomologyReindex_ofCocycle]
  rfl

end
end KIP126.Classical.Adams.MilnorCohomology
