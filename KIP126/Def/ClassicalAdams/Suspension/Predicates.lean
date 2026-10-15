module

public import KIP126.Def.ClassicalAdams.Suspension.Data

@[expose] public section

namespace KIP126.Classical.Adams.Suspension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}

/-- The E₂ labels are related by desuspending the same actual first-page
representative, through S's fixed layer map and then the genuine quotients.
This does not silently identify the two differently graded E₂ objects or
assert existence/uniqueness of suspension comparisons. -/
def TowerComparison.DesuspendsClass (S : TowerComparison H X) (s t : ℤ)
    (sx : PageRepresentatives.Ambient H (X⟦(1 : ℤ)⟧) (s, t))
    (x : PageRepresentatives.Ambient H X (s, t - 1)) : Prop :=
  ∃ (a : adamsCycles H.unit (X⟦(1 : ℤ)⟧) 2 (by decide) s t)
    (b : adamsCycles H.unit X 2 (by decide) s (t - 1)),
    classOfSecondCycle H (X⟦(1 : ℤ)⟧) s t a = sx ∧
      classOfSecondCycle H X s (t - 1) b = x ∧
      S.desuspendFirstPage s t a.val = b.val

end KIP126.Classical.Adams.Suspension
