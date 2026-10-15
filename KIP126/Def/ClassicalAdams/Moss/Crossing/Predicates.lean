module

public import KIP126.Def.ClassicalAdams.Moss.Mapping.Data

@[expose] public section

/-!
Moss-direction crossings in the specified actual mapping Adams sequence.
This direction is opposite to the paper's extension-crossing convention.
The full Moss theorem and its exact literature range are separate obligations.
-/

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- A crossing starts one stem above the product and in filtration q. -/
def crossingSourceDegree (k : ℤ × ℤ) (q : ℤ) : ℤ × ℤ :=
  (q, q + (k.2 - k.1) + 1)

/-- Explicit historical Moss-direction condition: a later differential from
below the defining-system filtration to strictly above the product filtration. -/
def HasMossCrossing (X Y : C) (r : ℤ) (k : ℤ × ℤ) : Prop :=
  ∃ m q : ℤ, r < m ∧ 0 ≤ q ∧ q < k.1 - (r - 1) ∧ k.1 < q + m ∧
    (mappingSequence unit X Y).d m (crossingSourceDegree k q) ≠ 0

def NoMossCrossing (X Y : C) (r : ℤ) (k : ℤ × ℤ) : Prop :=
  ¬ HasMossCrossing unit X Y r k

/-- The two product sequences use the same unit, closed structure and endpoints. -/
def NoMossCrossingForProducts (W X Y Z : C) (r : ℤ) (i j k : ℤ × ℤ) : Prop :=
  NoMossCrossing unit W Y r (i + j) ∧ NoMossCrossing unit X Z r (j + k)

end KIP126.Classical.Adams.Moss
