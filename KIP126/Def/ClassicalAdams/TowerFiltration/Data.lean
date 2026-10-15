module

public import KIP126.Def.ClassicalAdams.TowerPages.Data
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# The actual Adams cycle and boundary towers, based at page two

The ambient module is `Z₂` inside the constructed tower's first page, not an
independently chosen E₂. Stage `n` means the classical page `n + 2`.
The infinite stages are the intersection of cycles and union of boundaries.
No spectral-sequence identity or permanence assertion is postulated here.
-/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Representatives in the tower's second-page cycle module. -/
abbrev adamsCycleAmbient (s t : ℤ) := adamsCycles unit X 2 (by omega) s t

/-- Classical `(n + 2)`-cycles, as a submodule of `Z₂`. -/
def adamsFiniteCycleSubmodule (s t : ℤ) (n : ℕ) :
    Submodule ℤ (adamsCycleAmbient unit X s t) :=
  (adamsCycles unit X (n + 2) (by omega) s t).comap
    (adamsCycles unit X 2 (by omega) s t).subtype

/-- Classical `(n + 2)`-boundaries, as a submodule of `Z₂`. -/
def adamsFiniteBoundarySubmodule (s t : ℤ) (n : ℕ) :
    Submodule ℤ (adamsCycleAmbient unit X s t) :=
  (adamsBoundaries unit X (n + 2) (by omega) s t).comap
    (adamsCycles unit X 2 (by omega) s t).subtype

/-- All finite cycles and their actual intersection. -/
def adamsCycleSubmodule (s t : ℤ) : WithTop ℕ →
    Submodule ℤ (adamsCycleAmbient unit X s t)
  | ⊤ => ⨅ n : ℕ, adamsFiniteCycleSubmodule unit X s t n
  | (n : ℕ) => adamsFiniteCycleSubmodule unit X s t n

/-- All finite boundaries and their actual supremum. -/
def adamsBoundarySubmodule (s t : ℤ) : WithTop ℕ →
    Submodule ℤ (adamsCycleAmbient unit X s t)
  | ⊤ => ⨆ n : ℕ, adamsFiniteBoundarySubmodule unit X s t n
  | (n : ℕ) => adamsFiniteBoundarySubmodule unit X s t n

end
end KIP126.Classical.Adams
