module

public import KIP126.Def.Steenrod.MilnorCobar.Data

@[expose] public section

/-! Cycles and incoming boundaries of the actual normalized Milnor cobar differential. -/

namespace KIP126.Classical.Adams.MilnorCohomology

open KIP126.Algebra KIP126.Steenrod.Milnor

noncomputable section

/-- The kernel of the explicit coproduct differential in bidegree `(s,t)`. -/
def cycles (s t : ℕ) : Submodule F2 (cochains s t) :=
  LinearMap.ker (differential s t)

/-- The incoming image, with no incoming cochains in homological degree zero.
In degree `s+1` this is exactly `range (differential s t)`. -/
def boundaries : (s t : ℕ) → Submodule F2 (cochains s t)
  | 0, _ => ⊥
  | s + 1, t => LinearMap.range (differential s t)

end
end KIP126.Classical.Adams.MilnorCohomology
