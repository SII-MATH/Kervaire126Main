module

public import KIP126.Def.ClassicalAdams.Tower.Data
public import KIP126.Def.StableHomotopy.Cohomology.Data

@[expose] public section

/-!
# Adams filtration of a map

The lower bound is a factorization through the target's constructed Adams
tower. It does not select an arbitrary filtration integer and does not use
spectral-sequence pages or survival predicates.
-/





namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- A map has Adams filtration at least `k` when it factors through stage
`k` of the actual target Adams tower for the specified mod-2 unit. -/
def AdamsFiltrationAtLeast (H : Mod2EilenbergMacLane (C := C))
    {X Y : C} (f : X ⟶ Y) (k : ℕ) : Prop :=
  ∃ lift : X ⟶ adamsTower H.unit Y k,
    lift ≫ adamsTowerMap H.unit Y 0 k (Nat.zero_le k) = f

end KIP126.Classical.Adams
