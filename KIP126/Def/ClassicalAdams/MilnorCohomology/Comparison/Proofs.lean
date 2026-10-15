module

public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Data
public import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data

@[expose] public section

/-! The comparison preserves each specified actual cocycle representative. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Steenrod.Milnor

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem comparison_classOf {s t : ℕ} (x : cycles s t) :
    comparison H M s t (classOf H M s t x) = cycleClassMap H M s t x := by
  simp [comparison, classOf, LinearEquiv.trans_apply]

/-- A specified cocycle is sent to the class of that same cocycle in the
actual tower, not merely to some element under an arbitrary equivalence. -/
@[simp] theorem comparison_ofCocycle {s t : ℕ} (x : cochains s t)
    (hx : differential s t x = 0) :
    comparison H M s t (ofCocycle H M x hx) = internalClassOfCocycle H M x hx :=
  comparison_classOf H M ⟨x, hx⟩

/-- The comparison sends each specified cobar generator to the existing
standard class on the same internal Adams tower. -/
@[simp] theorem comparison_hi (i : ℕ) :
    comparison H M 1 (2 ^ i) (hi H M i) = Sphere.Internal.hi H M i := by
  exact (comparison_ofCocycle H M (hiCochain i) (hiCochain_isCycle i)).trans
    (internalClassOfCocycle_eq H M (hiCochain i) (hiCochain_isCycle i))

/-- The same comparison preserves the already specified concatenation square
for every index; it makes no additional nonvanishing assumption. -/
@[simp] theorem comparison_hiSquare (i : ℕ) :
    comparison H M 2 (2 ^ (i + 1)) (hiSquare H M i) =
      Sphere.Internal.hiSquare H M i := by
  exact (comparison_ofCocycle H M (hiSquareCochain i) (hiSquareCochain_isCycle i)).trans
    (internalClassOfCocycle_eq H M (hiSquareCochain i) (hiSquareCochain_isCycle i))

end
end KIP126.Classical.Adams.MilnorCohomology
